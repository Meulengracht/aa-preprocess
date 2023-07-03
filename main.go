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

type leaf struct {
	part     string
	children map[string]*leaf
}

func newLeaf(p string) *leaf {
	return &leaf{
		part:     p,
		children: make(map[string]*leaf),
	}
}

func (l *leaf) addToken(p string) *leaf {
	nl := l.children[p]
	if nl == nil {
		nl = newLeaf(p)
		l.children[p] = nl
	}
	return nl
}

func (l *leaf) addRule(r rule) {
	p, last := r.next()
	if strings.HasPrefix(p, "{") {
		pt := strings.Trim(p, "{}")
		pts := strings.Split(pt, ",")
		for _, t := range pts {
			nl := l.addToken(t)
			if !last {
				cl := r.current
				nl.addRule(r)
				r.current = cl
			}
		}
	} else {
		nl := l.addToken(p)
		if !last {
			nl.addRule(r)
		}
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

func (l *leaf) format(ctx, perms string) []string {
	var lines []string
	nctx := fmt.Sprintf("%s/%s", ctx, l.part)
	if len(l.children) == 0 {
		lines = append(lines, fmt.Sprintf("  %s %s", nctx, perms))
	}

	for _, c := range l.children {
		lines = append(lines, c.format(nctx, perms)...)
	}
	return lines
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

func (aa *aaOptimizer) combineLeafs(dst, src *leaf) {
	for _, s := range src.children {
		d := dst.children[s.part]
		if d != nil {
			aa.combineLeafs(d, s)
		} else {
			dst.children[s.part] = s
		}
	}
}

// Combine things like:
// /sys/devices/*/xxx r,
// /sys/devices/**/xxx r,
func (aa *aaOptimizer) optimizeTreePass0(l *leaf) {
	// /tmp/*   => Files directly in /tmp.
	// /tmp/*/  => Directories directly in /tmp.
	// /tmp/**  => Files and directories anywhere underneath /tmp.
	// /tmp/**/ => Directories anywhere underneath /tmp.

	var swc *leaf
	var dwc *leaf
	for _, c := range l.children {
		if c.part == "*" {
			swc = c
		} else if c.part == "**" {
			dwc = c
		}
	}

	if swc != nil && dwc != nil {
		if len(dwc.children) == 0 {
			// combine /* and /*/ with /**, /** covers anything
			// when they have identical perms and overrules that
			delete(l.children, "*")
		} else if len(dwc.children) > 0 && len(swc.children) > 0 {
			// combine /*/ with /**/
			aa.combineLeafs(dwc, swc)
			delete(l.children, "*")
		}
	}

	for _, c := range l.children {
		aa.optimizeTreePass0(c)
	}
}

func (aa *aaOptimizer) optimizePass0() {
	for _, l := range aa.trees {
		aa.optimizeTreePass0(l)
	}
}

func (aa *aaOptimizer) optimizeTreePass1(l *leaf) bool {
	if len(l.children) == 0 {
		return true
	}

	// if we do have children, then they must not have it, or they
	// must be identical
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

func (aa *aaOptimizer) identicalChildren(l, r *leaf) bool {
	// /sys/devices/virtual/net/tap*/**
	// /sys/devices/virtual/net/bchat*/**
	// /sys/devices/virtual/net/mstp*/**/dev
	if len(l.children) != len(r.children) {
		return false
	}
	for _, cl := range l.children {
		rl := r.children[cl.part]
		if rl == nil {
			return false
		}
		if !aa.identicalChildren(cl, rl) {
			return false
		}
	}
	return true
}

func (aa *aaOptimizer) containsUnbracketedComma(p string) bool {
	var sawBracket bool
	for _, r := range p {
		if r == '{' {
			sawBracket = true
		} else if r == ',' && !sawBracket {
			return true
		}
	}
	return false
}

func (aa *aaOptimizer) optimizeTreePass2(l *leaf) {
	if len(l.children) > 1 {
		for _, cl := range l.children {
			for _, rl := range l.children {
				if rl == cl {
					continue
				}
				if aa.identicalChildren(cl, rl) {
					p := fmt.Sprintf("%s,%s", strings.Trim(cl.part, "{}"), strings.Trim(rl.part, "{}"))
					delete(l.children, cl.part)
					delete(l.children, rl.part)
					cl.part = p
					l.children[p] = cl
				}
			}
		}
	}

	// fixup namings
	for _, c := range l.children {
		if aa.containsUnbracketedComma(c.part) {
			if !strings.HasPrefix(c.part, "{") {
				p := fmt.Sprintf("{%s}", c.part)
				delete(l.children, c.part)
				c.part = p
				l.children[p] = c
			}
		}
	}

	for _, c := range l.children {
		aa.optimizeTreePass2(c)
	}
}

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

func (aa *aaOptimizer) format() []string {
	var lines []string
	for p, t := range aa.trees {
		lines = append(lines, t.format("", p)...)
	}
	return lines
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

func writeLines(lines []string, path string) error {
	file, err := os.Create(path)
	if err != nil {
		return err
	}
	defer file.Close()

	w := bufio.NewWriter(file)
	for _, line := range lines {
		fmt.Fprintln(w, line)
	}
	return w.Flush()
}

func insert(a []string, index int, s string) []string {
	if len(a) == index {
		return append(a, s)
	}
	a = append(a[:index+1], a[index:]...)
	a[index] = s
	return a
}

func main() {
	if len(os.Args) < 3 {
		fmt.Println("usage: aaoptimizer [input] [output]")
		os.Exit(-1)
	}

	input := os.Args[1]
	output := os.Args[2]

	lines, err := readLines(input)
	if err != nil {
		fmt.Printf("aaoptimizer: %v", err)
		return
	}

	aa := newAaOptimizer()
	pathsToOptimize := []string{"/sys/devices"}

	// simple stupid replacement from the last encounter
	insertAt := -1
	var filteredLines []string
	for i, l := range lines {
		tl := strings.Trim(l, " ")
		if !strings.HasPrefix(tl, pathsToOptimize[0]) {
			filteredLines = append(filteredLines, l)
			continue
		}
		if insertAt == -1 {
			insertAt = i
		}
		aa.addRule(tl)
	}

	//fmt.Printf("original:\n")
	//aa.dump()
	fmt.Println("executing pass 0")
	aa.optimizePass0()
	//aa.dump()

	// must be last passes
	fmt.Println("executing pass 1")
	aa.optimizePass1()
	//aa.dump()
	fmt.Println("executing pass 2")
	aa.optimizePass2()
	//aa.dump()

	// insert a small header
	insert(filteredLines, insertAt, "\n  # generated by aa-optimizer app")
	insertAt++

	// insert into filteredLines
	rls := aa.format()
	for _, r := range rls {
		filteredLines = insert(filteredLines, insertAt, r)
		insertAt++
	}

	err = writeLines(filteredLines, output)
	if err != nil {
		fmt.Printf("aaoptimizer: %v", err)
	}
}

//    /sys/devices/**/bConfigurationValue r,
//    /sys/devices/**/descriptors r,
//    /sys/devices/**/manufacturer r,
//    /sys/devices/**/product r,
//    /sys/devices/**/revision r,
//    /sys/devices/**/serial r,
//    /sys/devices/**/vendor r,
// =>  /sys/devices/**/{bConfigurationValue,descriptors,manufacturer,product,revision,serial,vendor} r,
