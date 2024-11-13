/*
Copyright 2024 Simon Murray

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

package sat

import (
	"fmt"
	"iter"
	"maps"
	"slices"
	"strings"
)

// PartialClause is used during conflic resolution to resolve a new clause.
// It maps the variable to whether or not it's negated.
type PartialClause map[*Variable]bool

// resolve combines two partial clauses such that (^A v B v C) and (A, D, ^E)
// combine to form (B v C v D v ^E) i.e. ^A and A cancel each other out.
func (p PartialClause) resolve(o PartialClause) PartialClause {
	r := PartialClause{}

	for name, negated := range p {
		r[name] = negated
	}

	for name, negated := range o {
		if otherNetgated, ok := r[name]; ok && otherNetgated != negated {
			delete(r, name)

			continue
		}

		r[name] = negated
	}

	return r
}

func (p PartialClause) String() string {
	s := make([]string, 0, len(p))

	for name, negated := range p {
		if !negated {
			s = append(s, name.name)

			continue
		}

		s = append(s, "¬"+name.name)
	}

	return strings.Join(s, " v ")
}

// BooleanState wraps up a boolean variable or roll up.
type BooleanState struct {
	// defined is whether the value is defined.
	defined bool
	// value is the value of the boolean when defined.
	value bool
}

func (s *BooleanState) Define(value bool) {
	s.defined = true
	s.value = value
}

func (s *BooleanState) Undefine() {
	s.defined = false
}

type SubscribeFn func(*BooleanState)

// BooleanStatePublisher allows others to subscribe to updates of
// the boolean state.
type BooleanStatePublisher struct {
	// state is the state of the variable.
	state BooleanState
	// handle is an ID used to identify a subscriber so it can unsubscribe.
	handle int
	// subscribers are the list of clients subscribed to monitor changes.
	subscribers map[int]SubscribeFn
}

// Subscribe registers the callback function and calls it to communicate the initial state.
func (p *BooleanStatePublisher) Subscribe(callback SubscribeFn) int {
	if p.subscribers == nil {
		p.subscribers = map[int]SubscribeFn{}
	}

	handle := p.handle
	p.handle++

	p.subscribers[handle] = callback

	callback(&p.state)

	return handle
}

// Unsubscribe removes the subscription.
func (p *BooleanStatePublisher) Unsubscribe(handle int) {
	delete(p.subscribers, handle)
}

// Define defines the value and notifies subscribers.
func (p *BooleanStatePublisher) Define(value bool) {
	p.state.Define(value)
	p.notify()
}

// Undefine undefines the value and notifies subscribers.
func (p *BooleanStatePublisher) Undefine() {
	p.state.Undefine()
	p.notify()
}

func (p *BooleanStatePublisher) notify() {
	for _, f := range p.subscribers {
		f(&p.state)
	}
}

// Variable represents a boolean variable.
type Variable struct {
	// BooleanStatePublisher allows the variable to notify subscribers of updates.
	BooleanStatePublisher
	// name is the short variable name e.g. v1, v6.
	name string
	// extName is the external name set by the user.
	extName string
}

func NewVariable(name, extName string) *Variable {
	return &Variable{
		name:    name,
		extName: extName,
	}
}

func compareVariable(a, b *Variable) int {
	return strings.Compare(a.name, b.name)
}

func (v *Variable) String() string {
	head := ""
	tail := ""

	if v.state.defined {
		tail = "\x1b[0m"

		if v.state.value {
			head = "\x1b[1;32m"
		} else {
			head = "\x1b[1;31m"
		}
	}

	return head + v.name + tail
}

// VariableSet controls variable allocation and mapping.
type VariableSet struct {
	// variables is a set of variables indexed by an external naming scheme.
	// e.g. x0:y0:5 for a Sudoku solver.
	variables map[string]*Variable
	// list is an ordered list of variables.
	list []*Variable
	// counter is a monotonic counter for creating debug names for variables.
	counter int
}

func NewVariableSet() *VariableSet {
	return &VariableSet{
		variables: map[string]*Variable{},
	}
}

// get returns an existing or new variable based on an external name.
func (s *VariableSet) get(name string) *Variable {
	if v, ok := s.variables[name]; ok {
		return v
	}

	v := NewVariable(fmt.Sprint("v", s.counter), name)

	s.list = append(s.list, v)
	s.variables[name] = v
	s.counter++

	return v
}

// Complete returns whether or not all variables are set.
func (s *VariableSet) Complete() bool {
	for _, variable := range s.list {
		if !variable.state.defined {
			return false
		}
	}

	return true
}

func (s *VariableSet) String() string {
	t := make([]string, len(s.list))

	for i, v := range s.list {
		t[i] = v.String()
	}

	return strings.Join(t, ", ")
}

func (s *VariableSet) Dump() {
	fmt.Println("Variables:")
	fmt.Println(s)
}

// Literal is a reference to a variable used by a clause.
type Literal struct {
	// BooleanStatePublisher allows the variable to notify subscribers of updates.
	BooleanStatePublisher
	// variable is a reference to the underlying variable.
	variable *Variable
	// negated is whether or not the boolean value is negated.
	negated bool
}

func NewLiteral(variable *Variable, negated bool) *Literal {
	l := &Literal{
		variable: variable,
		negated:  negated,
	}

	variable.Subscribe(l.update)

	return l
}

// update accespts updates from the underlying variable, does any necessary
// mutations due to negation, then notifies any subscribed clauses.
func (l *Literal) update(s *BooleanState) {
	l.state = *s

	if l.negated {
		l.state.value = !l.state.value
	}

	l.notify()
}

// Define sets the literal to a specific value, and writes through to the
// underlying variable paying attention to any negation.  The local state
// wiill be updated by the subscription callback.
func (l *Literal) Define(value bool) {
	if l.negated {
		value = !value
	}

	l.variable.Define(value)
}

func (l *Literal) String() string {
	head := ""
	tail := ""

	if l.state.defined {
		tail = "\x1b[0m"

		if l.state.value {
			head = "\x1b[1;32m"
		} else {
			head = "\x1b[1;31m"
		}
	}

	negation := ""

	if l.negated {
		negation = "¬"
	}

	return head + negation + l.variable.name + tail
}

// Clause is a logical OR of literals.
type Clause struct {
	// BooleanStatePublisher allows the variable to notify subscribers of updates.
	BooleanStatePublisher
	// literals is an ordered list of all iterals that make up the clause.
	literals []*Literal
	// defined is a count of the number of defined literals.
	defined int
	// bitfield records the boolean states of all the literals (upto 64 for now...)
	bitfield int
	// initialized is used for consistency of the defined count.
	initialized bool
}

func NewClause(literals ...*Literal) *Clause {
	c := &Clause{
		literals: literals,
	}

	for i := range literals {
		update := func(s *BooleanState) {
			c.update(i, s)
		}

		literals[i].Subscribe(update)
	}

	c.initialized = true

	return c
}

func (c Clause) String() string {
	s := make([]string, len(c.literals))

	for i := range c.literals {
		s[i] = c.literals[i].String()
	}

	return fmt.Sprint(c.defined, len(c.literals)) + " " + strings.Join(s, " ∨ ")
}

// Complete tells us whether all literals are set.
func (c *Clause) Complete() bool {
	return c.defined == len(c.literals)
}

// Unit tells us if one literal is unset.
func (c *Clause) Unit() bool {
	return c.defined == len(c.literals)-1
}

// Value tells us whether there is a conflict (false), or not.
func (c *Clause) Value() bool {
	return c.bitfield != 0
}

func (c *Clause) update(i int, s *BooleanState) {
	// Zero out the bit unconditionally, this handles when the value
	// is undefined and when defined but false.
	c.bitfield &= ^(1 << i)

	// If something is defined either during initialization or as pert
	// of normal operation, update the counts and values.
	if s.defined {
		c.defined++

		if s.value {
			c.bitfield |= 1 << i
		}
	}

	// Only update the defined count after initialization, otherwise
	// you'll end up with negative counts!
	if !s.defined && c.initialized {
		c.defined--
	}
}

// Partial returns a partial clause for conflict resolution.
func (c *Clause) Partial() PartialClause {
	r := PartialClause{}

	for _, literal := range c.literals {
		r[literal.variable] = literal.negated
	}

	return r
}

// ClauseList wraps up handling of clauses.
type ClauseList struct {
	items []*Clause
}

func NewClauseList() *ClauseList {
	return &ClauseList{}
}

// Add appends a new clause to the list.
func (l *ClauseList) Add(c *Clause) {
	l.items = append(l.items, c)
}

func (l *ClauseList) Dump() {
	fmt.Println("Clauses:")

	for i, c := range l.items {
		fmt.Println(i, ":", c.Value(), c)
	}
}

// pathEntry remembers decisions made as we attempt to solve the SAT problem.
type pathEntry struct {
	// decision did this result from a decision, rather than BCP?
	decision bool
	// level that the entry was created at.
	level int
	// variable that was set.
	variable *Variable
	// clause (where set by BCP) that caused the inference.
	clause *Clause
}

func (e *pathEntry) String() string {
	cause := "(decision)"

	if !e.decision {
		cause = "(clause " + e.clause.String() + ")"
	}

	return fmt.Sprint(e.variable.name, "@", e.level, " ", cause)
}

// Path remembers decisions and inferences made and what made them.
type Path struct {
	entries []pathEntry
}

func NewPath() *Path {
	return &Path{}
}

func (p *Path) Dump() {
	fmt.Println("Path:")

	for _, entry := range p.entries {
		fmt.Println(entry.String())
	}
}

func (p *Path) Push(decision bool, level int, variable *Variable, clause *Clause) {
	p.entries = append(p.entries, pathEntry{
		decision: decision,
		level:    level,
		variable: variable,
		clause:   clause,
	})
}

// Rollback accepts a level to roll back to and removes all entries defined
// after that level, performing any cleanup necessary.
func (p *Path) Rollback(level int) {
	i := slices.IndexFunc(p.entries, func(entry pathEntry) bool {
		return entry.level > level
	})

	for _, entry := range p.entries[i:] {
		entry.variable.Undefine()
	}

	p.entries = p.entries[:i]
}

// CDCLSolver implements CDCL (conflict driven clause learning).
type CDCLSolver struct {
	// variables reference by clause literals.
	variables *VariableSet
	// clauses that make up the CNF (conjunctive noraml form).
	clauses *ClauseList
	// path that acts as a journal of our decisions and how we arrived there.
	path *Path
	// level is the decision level.
	level int
}

func NewCDCLSolver() *CDCLSolver {
	return &CDCLSolver{
		variables: NewVariableSet(),
		clauses:   NewClauseList(),
		path:      NewPath(),
	}
}

func (s *CDCLSolver) Literal(name string) *Literal {
	return NewLiteral(s.variables.get(name), false)
}

func (s *CDCLSolver) NegatedLiteral(name string) *Literal {
	return NewLiteral(s.variables.get(name), true)
}

func (s *CDCLSolver) Clause(literals ...*Literal) {
	s.clauses.Add(NewClause(literals...))
}

func (s *CDCLSolver) Dump() {
	s.variables.Dump()
	s.clauses.Dump()
	s.path.Dump()
}

// conflict returns true if a conflict has been detected and the clause
// that caused it.
func (s *CDCLSolver) conflict() (*Clause, bool) {
	for _, clause := range s.clauses.items {
		if clause.Complete() && !clause.Value() {
			return clause, true
		}
	}

	return nil, false
}

// bcpSingle runs a single BCP pass, returning true if we did something.
func (s *CDCLSolver) bcpSingle() bool {
	for _, clause := range s.clauses.items {
		// We only care if one is unset and it's false already, so we can infer
		// the child must be true.
		if !clause.Unit() || clause.Value() {
			continue
		}

		// Find the unset literal and make it true...
		for _, literal := range clause.literals {
			if !literal.state.defined {
				literal.Define(true)
				s.path.Push(false, s.level, literal.variable, clause)

				return true
			}
		}
	}

	return false
}

// bcp performs BCP while it can, or until a conflict is detected.
// Returns true on a conflict and the clause that caused the conflict.
func (s *CDCLSolver) bcp() (*Clause, bool) {
	for s.bcpSingle() {
		if clause, ok := s.conflict(); ok {
			return clause, true
		}
	}

	return nil, false
}

// partialVariablesAtCurrentLevel returns the number of variables that are contained in
// the partial that were set at the current level.  When this hits 1 we've finished
// resolution.  While we are at it, we also keep tabs on the asserting level we will
// need to roll back to.
func (s *CDCLSolver) partialVariablesAtCurrentLevel(partial PartialClause, assertingLevel *int) int {
	var count int

	var level int

	for _, entry := range s.path.entries {
		if _, ok := partial[entry.variable]; ok {
			if entry.level == s.level {
				count++
			} else {
				// NOTE: this will return the second largest level encountered
				// unless it's a unary partial, and this will never get called
				// and correctly be 0.
				level = max(level, entry.level)
			}
		}
	}

	*assertingLevel = level

	return count
}

func (s *CDCLSolver) handleConflict(clause *Clause) {
	partial := clause.Partial()

	var assertingLevel int

	for _, entry := range slices.Backward(s.path.entries) {
		// If the entry doesn't contain the current variable, skip it.
		if _, ok := partial[entry.variable]; !ok {
			continue
		}

		// If it does, then resolve the new partial.
		partial = partial.resolve(entry.clause.Partial())

		// If the partial only contains a single variable at the current
		// decision level, then we are done!
		if s.partialVariablesAtCurrentLevel(partial, &assertingLevel) == 1 {
			break
		}
	}

	// Perform the rollback before we add the new clause so we get the pub/sub
	// into a sane state, otherwise the new clause will probably see undefines
	// it shouldn't.
	s.level = assertingLevel
	s.path.Rollback(assertingLevel)

	// Finally add our new clause.
	l := make([]*Literal, 0, len(partial))

	// You'll thank me for this determinism when debugging...
	for _, variable := range slices.SortedFunc(maps.Keys(partial), compareVariable) {
		l = append(l, NewLiteral(variable, partial[variable]))
	}

	s.clauses.Add(NewClause(l...))
}

// Solve does the top level solving of the SAT problem.  It accepts a custom
// decision function so the client can choose how to select a candidate when
// trial and error is required.  For example, you may maintain some domain
// specific knowledge about variables and clauses and be able to make more
// sensible choices than an arbitrary selector.
func (s *CDCLSolver) Solve(decide func(*VariableSet, *ClauseList) (*Variable, bool)) bool {
	// Do an initial boolean constant propagation.
	if _, conflict := s.bcp(); conflict {
		return false
	}

	// Until we've fully defined all variables.
	for !s.variables.Complete() {
		// Increase the decision level and select a variable to set, we need
		// to guess here as BCP cannot complete the task by itself.
		s.level++

		variable, value := decide(s.variables, s.clauses)

		variable.Define(value)
		s.path.Push(true, s.level, variable, nil)

		for {
			// If BCP has done all it can after the last guess,
			// see if we're complete, otherwise make another guess.
			clause, conflict := s.bcp()
			if !conflict {
				break
			}

			s.handleConflict(clause)
		}
	}

	return true
}

func (s *CDCLSolver) Variables() iter.Seq2[string, bool] {
	return func(yield func(string, bool) bool) {
		for _, v := range s.variables.list {
			if !yield(v.extName, v.state.value) {
				return
			}
		}
	}
}

func DefaultChooser(v *VariableSet, _ *ClauseList) (*Variable, bool) {
	for _, v := range v.list {
		if !v.state.defined {
			return v, false
		}
	}

	return nil, false
}
