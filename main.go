package main

import (
	"bufio"
	"fmt"
	"os"
	"strings"
)

type rule struct {
	deny       bool
	pathTokens []string
	current    int
	perms      string
}

func newRule(rs string) rule {
	r := rule{}
	i := 0
	tokens := strings.Split(rs, " ")
	if len(tokens) == 3 {
		if tokens[i] == "deny" {
			r.deny = true
		}
		i++
	}
	r.pathTokens = strings.Split(tokens[i], "/")
	if r.pathTokens[0] == "" {
		r.pathTokens = r.pathTokens[1:]
	}
	r.perms = tokens[i+1]
	return r
}

func (r *rule) next() (string, bool) {
	if r.current == len(r.pathTokens) {
		return "", true
	}
	n := r.pathTokens[r.current]
	r.current++
	return n, r.current == len(r.pathTokens)
}

func (r *rule) reset() {
	r.current = 0
}

type leaf struct {
	// dir is only set to true if the expression
	// ended as a dir (trailing slash)
	dir      bool
	part     string
	children map[string]*leaf
}

func newLeaf(p string) *leaf {
	return &leaf{
		part:     p,
		children: make(map[string]*leaf),
	}
}

func (l *leaf) isDirectory() bool {
	return l.dir || len(l.children) > 0
}

func (l *leaf) processToken(p string, last bool) {
	nl := l.children[p]
	if nl == nil {
		nl = newLeaf(p)
		l.children[p] = nl
	}
	if !last {
		// special case, if the last token is empty
		// then this was a directory and we want to stop
		// anyway
		if r.pathTokens[r.current] == "" {
			nl.dir = true
			return
		}
		nl.addRule(r)
	}
}

func (l *leaf) addRule(r rule) {
	p, last := r.next()
	if strings.HasPrefix(p, "{") {
		pt := strings.Trim(p, "{}")
		pts := strings.Split(pt, ",")
		for _, t := range pts {
			if t == "" {
				// include dir
			}
			l.processToken(t, last)
		}
	}
	nl := l.children[p]
	if nl == nil {
		nl = newLeaf(p)
		l.children[p] = nl
	}
	if !last {
		// special case, if the last token is empty
		// then this was a directory and we want to stop
		// anyway
		if r.pathTokens[r.current] == "" {
			nl.dir = true
			return
		}
		nl.addRule(r)
	}
}

func (l *leaf) dump(ctx string) {
	nctx := fmt.Sprintf("%s/%s", ctx, l.part)
	if len(l.children) == 0 {
		fmt.Println(nctx)
		return
	}

	for _, c := range l.children {
		c.dump(nctx)
	}
}

type aaOptimizer struct {
	trees map[string]*leaf
}

func newAaOptimizer() *aaOptimizer {
	return &aaOptimizer{
		trees: make(map[string]*leaf),
	}
}

func (aa *aaOptimizer) addRule(rs string) {
	r := newRule(rs)
	if r.deny {
		// ignore deny for now
		return
	}

	p, _ := r.next()
	l := aa.trees[r.perms]
	if l == nil {
		l = newLeaf(p)
		aa.trees[r.perms] = l
	}
	l.addRule(r)
}

func (aa *aaOptimizer) optimizeTreePass1(l *leaf) bool {
	if len(l.children) == 0 {
		return true
	}

	// if we do have children, then they must not have it
	var parts []string
	children := make(map[string]*leaf)
	for _, c := range l.children {
		if c.part != "" && aa.optimizeTreePass1(c) {
			parts = append(parts, c.part)
		} else {
			children[c.part] = c
		}
	}

	if len(parts) < 2 {
		return false
	}

	// If one the children is a * or **. then ignore all else
	for _, pc := range parts {
		if pc == "*" || pc == "**" {
			parts = []string{pc}
			break
		}
	}

	// ok none of our children have children, consolidate
	// them
	var p string
	if len(parts) == 1 {
		p = parts[0]
	} else {
		p = fmt.Sprintf("{%s}", strings.Join(parts, ","))
	}
	l.children = children
	l.children[p] = newLeaf(p)
	return false
}

// Combine things like:
// /sys/devices/**/uevent r,
// /sys/devices/**/read_ahead_kb r,
func (aa *aaOptimizer) optimizePass1() {
	for _, l := range aa.trees {
		aa.optimizeTreePass1(l)
	}
}

func (aa *aaOptimizer) isDirectory(l *leaf) bool {
	if len(l.children) == 0 {
		return l.dir
	}

	for _, c := range l.children {
		if !aa.isDirectory(c) {
			return false
		}
	}
	return true
}

// Check if leftCs covers rightCs
func (aa *aaOptimizer) isCoveredChildren(leftCs map[string]*leaf, rightCs map[string]*leaf) bool {
	for _, c := range rightCs {
		if !aa.isCovered(leftCs, c) {
			return false
		}
	}
	return true
}

func (aa *aaOptimizer) isCovered(ls map[string]*leaf, l *leaf) bool {
	// /tmp/*   => Files directly in /tmp.
	// /tmp/*/  => Directories directly in /tmp.
	// /tmp/**  => Files and directories anywhere underneath /tmp.
	// /tmp/**/ => Directories anywhere underneath /tmp.
	for _, c := range ls {
		if c.part == "**" {
			if !c.dir && len(c.children) == 0 {
				// expr ended with /** => covers *everything*
				return true
			} else if c.dir && len(c.children) == 0 {
				// expr ended with /**/ => covers any directories under this children
				return aa.isDirectory(l)
			}
			// otherwise the expr is going like this /**/... and we need
			// to verify down the chain
			return aa.isCoveredChildren(c.children, l.children)
		} else if c.part == "*" {
			if len(c.children) == 0 {
				// expr ended with /* => covers files directly under, which means
				// l must be a file
				return !l.isDirectory()
			} else if c.dir && len(c.children) == 0 {
				// expr ended with /*/ => covers directories directly under, which
				// means the leaf must have ended with a trailing slash here
				return l.dir
			}
			// otherwise the expr is going like this /*/... and we need
			// to verify down the chain
			return aa.isCoveredChildren(c.children, l.children)
		}
	}
	return false
}

func (aa *aaOptimizer) canCover(ls map[string]*leaf, l *leaf) []string {
	// /tmp/*   => Files directly in /tmp.
	// /tmp/*/  => Directories directly in /tmp.
	// /tmp/**  => Files and directories anywhere underneath /tmp.
	// /tmp/**/ => Directories anywhere underneath /tmp.
	var keys []string
	for k, c := range ls {
		// canCover is only called if l.part == * or l.part == **
		switch {
		case l.part == "*" && !l.dir && len(l.children) == 0:
			// expr ends on /*, which means we can cover this *if* c is
			// file
			if !c.dir && len(c.children) == 0 {
				keys = append(keys, k)
			}
		case l.part == "*" && l.dir:
			// expr ends on /*/, this means we can cover this iff c
			// is a directory (and expr ended)
			if c.dir {
				keys = append(keys, k)
			}
		case l.part == "*":
			// /*/ is just a part of expression, we must follow child
			if aa.isCoveredChildren(l.children, c.children) {
				keys = append(keys, k)
			}
		case l.part == "**" && !l.dir && len(l.children) == 0:
			// expr ends on /**, which means we can cover this in any case
			keys = append(keys, k)
		case l.part == "**" && l.dir:
			// expr ends on /**/, which means we cover this *if* c is a directory
			if aa.isDirectory(c) {
				keys = append(keys, k)
			}
		case l.part == "*":
			// /*/ is just a part of expression, we must follow child
			if aa.isCoveredChildren(l.children, c.children) {
				keys = append(keys, k)
			}
		}
	}
	return keys
}

func (aa *aaOptimizer) optimizeTreePass2(l *leaf) {
	optimized := make(map[string]*leaf)
	for _, c := range l.children {
		if c.part != "*" && c.part != "**" {
			if aa.isCovered(optimized, c) {
				continue
			}
		} else {
			covers := aa.canCover(optimized, c)
			for _, cv := range covers {
				delete(optimized, cv)
			}
		}
		optimized[c.part] = c
	}
	l.children = optimized
}

// Combine things like
// /sys/devices/**/block/**
// /sys/devices/*/block/{,**}
func (aa *aaOptimizer) optimizePass2() {
	for _, l := range aa.trees {
		aa.optimizeTreePass2(l)
	}
}

func (aa *aaOptimizer) dump() {
	for _, t := range aa.trees {
		t.dump("")
	}
}

func readLines(path string) ([]string, error) {
	file, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer file.Close()

	var lines []string
	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		lines = append(lines, scanner.Text())
	}
	return lines, scanner.Err()
}

func main() {
	fmt.Println("Hello, World!")

	lines, err := readLines("./slow.apparmor")
	if err != nil {
		fmt.Printf("%v", err)
		return
	}

	aa := newAaOptimizer()
	pathsToOptimize := []string{"/sys/devices"}
	for _, l := range lines {
		tl := strings.Trim(l, " ")
		if !strings.HasPrefix(tl, pathsToOptimize[0]) {
			continue
		}
		aa.addRule(tl)
	}

	fmt.Printf("original (len=%d):\n", len(lines))
	aa.dump()
	fmt.Println("pass 1:")
	aa.optimizePass1()
	aa.dump()
	fmt.Println("pass 2:")
	aa.optimizePass2()
	aa.dump()
}

//    /sys/devices/**/bConfigurationValue r,
//    /sys/devices/**/descriptors r,
//    /sys/devices/**/manufacturer r,
//    /sys/devices/**/product r,
//    /sys/devices/**/revision r,
//    /sys/devices/**/serial r,
//    /sys/devices/**/vendor r,
// =>  /sys/devices/**/{bConfigurationValue,descriptors,manufacturer,product,revision,serial,vendor} r,
