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
	"errors"
	"fmt"
	"iter"
	"maps"
	"slices"
	"strings"
)

var (
	ErrUnexpected = errors.New("unexpectd error")
)

// Set allows O(log N) insertion and deletion.
type Set[T comparable] map[T]any

// Add adds a new member.
func (s Set[T]) Add(t T) {
	s[t] = nil
}

// Delete removes and existing member.
func (s Set[T]) Delete(t T) {
	delete(s, t)
}

// Has checks whether a value is in the set.
func (s Set[T]) Has(t T) bool {
	_, ok := s[t]

	return ok
}

// All provides non-deterministic iteration.
func (s Set[T]) All() iter.Seq[T] {
	return func(yield func(t T) bool) {
		for k := range s {
			if !yield(k) {
				return
			}
		}
	}
}

// AllSortedFunc provides deterministic iteration.  This is a lot slower
// than non-deterministic, but useful for debugging.
func (s Set[T]) AllSortedFunc(cmp func(T, T) int) iter.Seq[T] {
	return func(yield func(t T) bool) {
		for _, k := range slices.SortedFunc(maps.Keys(s), cmp) {
			if !yield(k) {
				return
			}
		}
	}
}

// Permute returns an iterator over all possible unique pairs of a slice members.
func Permute[T any](t []T) iter.Seq2[T, T] {
	return func(yield func(T, T) bool) {
		for i := range t {
			for j := i + 1; j < len(t); j++ {
				if !yield(t[i], t[j]) {
					return
				}
			}
		}
	}
}

// Boolean wraps up a boolean variable which may be undefined.
type Boolean struct {
	// value of the boolean, nil is undefined
	value *bool
	// subscribers are the list of clients subscribed to monitor changes.
	subscribers []subscribeFn
}

type subscribeFn func(Boolean) error

func (b Boolean) Undefined() bool {
	return b.value == nil
}

func (b Boolean) Defined() bool {
	return b.value != nil
}

func (b Boolean) Value() bool {
	return b.Defined() && *b.value
}

// subscribe registers the callback function and calls it to communicate the initial value.
func (b *Boolean) subscribe(callback subscribeFn) {
	b.subscribers = append(b.subscribers, callback)
}

func (b *Boolean) notify() error {
	for _, f := range b.subscribers {
		if err := f(*b); err != nil {
			return err
		}
	}

	return nil
}

func (b *Boolean) define(value bool) error {
	b.value = &value

	return b.notify()
}

func (b *Boolean) undefine() error {
	b.value = nil

	return b.notify()
}

// variable represents a boolean variable.
type variable[T comparable] struct {
	// Boolean allows the variable to notify subscribers of updates.
	Boolean
	// id is the unique id of the variable.
	id int
	// userinfo is a user defined type used to compare variables.
	userinfo T
}

func newVariable[T comparable](id int, userinfo T) *variable[T] {
	return &variable[T]{
		id:       id,
		userinfo: userinfo,
	}
}

func (v *variable[T]) String() string {
	head := ""
	tail := ""

	if v.Defined() {
		tail = "\x1b[0m"

		if v.Value() {
			head = "\x1b[1;32m"
		} else {
			head = "\x1b[1;31m"
		}
	}

	return fmt.Sprint(head, "v", v.id, tail)
}

// variableSet controls variable allocation and mapping.
type variableSet[T comparable] struct {
	// variables is a set of variables indexed by an external naming scheme.
	// e.g. x0:y0:5 for a Sudoku solver.
	variables map[T]*variable[T]
	// list is an ordered list of variables.
	list []*variable[T]
	// counter is a monotonic counter for creating debug names for variables.
	counter int
}

func newVariableSet[T comparable]() *variableSet[T] {
	return &variableSet[T]{
		variables: map[T]*variable[T]{},
	}
}

// get returns an existing or new variable based on an external name.
func (s *variableSet[T]) get(t T) *variable[T] {
	if v, ok := s.variables[t]; ok {
		return v
	}

	v := newVariable(s.counter, t)

	s.list = append(s.list, v)
	s.variables[t] = v
	s.counter++

	return v
}

// Complete returns whether or not all variables are set.
func (s *variableSet[T]) complete() bool {
	for _, variable := range s.list {
		if variable.Undefined() {
			return false
		}
	}

	return true
}

func (s *variableSet[T]) String() string {
	t := make([]string, len(s.list))

	for i, v := range s.list {
		t[i] = v.String()
	}

	return strings.Join(t, ", ")
}

func (s *variableSet[T]) dump() {
	fmt.Println("Variables:")
	fmt.Println(s)
}

// Literal is a reference to a variable used by a clause.
type Literal[T comparable] struct {
	// Boolean allows the variable to notify subscribers of updates.
	Boolean
	// variable is a reference to the underlying variable.
	variable *variable[T]
	// negated is whether or not the boolean value is negated.
	negated bool
}

func newLiteral[T comparable](variable *variable[T], negated bool) *Literal[T] {
	l := &Literal[T]{
		variable: variable,
		negated:  negated,
	}

	variable.subscribe(l.update)

	return l
}

// update accespts updates from the underlying variable, does any necessary
// mutations due to negation, then notifies any subscribed clauses.
func (l *Literal[T]) update(v Boolean) error {
	if v.Defined() {
		return l.define(v.Value() != l.negated)
	}

	return l.undefine()
}

func (l *Literal[T]) String() string {
	head := ""
	tail := ""

	if l.Defined() {
		tail = "\x1b[0m"

		if l.Value() {
			head = "\x1b[1;32m"
		} else {
			head = "\x1b[1;31m"
		}
	}

	negation := ""

	if l.negated {
		negation = "¬"
	}

	return fmt.Sprint(head, negation, "v", l.variable.id, tail)
}

type literalCacheKey[T comparable] struct {
	variable T
	negated  bool
}

// literalCache maps a variable identifier and negation state to a literal to
// prevent extra resources to constrain memory use and prevent excessive fanout
// during BCP.
type literalCache[T comparable] struct {
	cache map[literalCacheKey[T]]*Literal[T]
}

func newLiteralCache[T comparable]() *literalCache[T] {
	return &literalCache[T]{
		cache: map[literalCacheKey[T]]*Literal[T]{},
	}
}

func (c *literalCache[T]) get(variable T, negated bool) (*Literal[T], bool) {
	v, ok := c.cache[literalCacheKey[T]{variable: variable, negated: negated}]
	return v, ok
}

func (c *literalCache[T]) set(variable T, negated bool, literal *Literal[T]) {
	c.cache[literalCacheKey[T]{variable: variable, negated: negated}] = literal
}

// clause is a logical OR of literals.
type clause[T comparable] struct {
	// Boolean allows the variable to notify subscribers of updates.
	Boolean
	// id is the unique id of the clause.
	id int
	// literals is an ordered list of all iterals that make up the clause.
	literals []*Literal[T]
	// numDefined is a count of the number of defined literals.
	numDefined int
	// literalDefined records whether a value as defined.
	literalDefined []int64
	// literalValues records the boolean values of all the literals (upto 64 for now...)
	literalValues []int64
}

func (c *clause[T]) init(id int, literals ...*Literal[T]) {
	// The maths for the values is quite simple.
	// ((1 + 63) >> 6) = (64 >> 6) = 1
	// ((64 + 63) >> 6) = (127 >> 6) = 1
	words := (len(literals) + 63) >> 6

	c.id = id
	c.literals = literals
	c.literalDefined = make([]int64, words)
	c.literalValues = make([]int64, words)

	for i := range literals {
		update := func(s Boolean) error {
			return c.update(i, s)
		}

		literals[i].subscribe(update)
	}
}

func (c clause[T]) String() string {
	s := make([]string, len(c.literals))

	for i := range c.literals {
		s[i] = c.literals[i].String()
	}

	head := ""
	tail := ""

	if c.Complete() || c.Value() {
		if c.Value() {
			head = "\x1b[1;32m"
		} else {
			head = "\x1b[1;31m"
		}

		tail = "\x1b[0m"
	}

	return fmt.Sprint(head, "c", c.id, tail, ": ", c.numDefined, " ", len(c.literals), " ", strings.Join(s, " ∨ "))
}

// Complete tells us whether all literals are set.
func (c *clause[T]) Complete() bool {
	return c.numDefined == len(c.literals)
}

// Unit tells us if one literal is unset and it has to be true.
func (c *clause[T]) Unit() bool {
	return c.numDefined == len(c.literals)-1 && !c.Value()
}

// Value tells us whether there is a conflict (false), or not.
func (c *clause[T]) Value() bool {
	for _, i := range c.literalValues {
		if i != 0 {
			return true
		}
	}

	return false
}

type ConflictError[T comparable] struct {
	clause *clause[T]
}

func (e *ConflictError[T]) Error() string {
	return fmt.Sprint("conflict error: ", e.clause)
}

//nolint:cyclop
func (c *clause[T]) update(i int, s Boolean) error {
	word := i >> 6
	bit := i & 0x3f

	// Was this already defined and do we need to do anything?
	literalDefined := c.literalDefined[word]&(1<<bit) != 0

	// Both in the same state of definedness.
	if !s.Defined() && !literalDefined {
		return nil
	}

	beingDefined := !literalDefined && s.Defined()
	beingUndefined := literalDefined && !s.Defined()

	if beingDefined {
		c.numDefined++
		c.literalDefined[word] |= 1 << bit

		if s.Value() {
			c.literalValues[word] |= 1 << bit
		}
	} else if beingUndefined {
		c.numDefined--
		c.literalDefined[word] &= ^(1 << bit)
		c.literalValues[word] &= ^(1 << bit)
	}

	// Detect a conflict early and don't do any more work than necessary.
	if c.Complete() && !c.Value() {
		return &ConflictError[T]{
			clause: c,
		}
	}

	// Propagate the new value up to any subscribers.
	if c.Complete() || c.Value() {
		return c.define(c.Value())
	}

	return c.undefine()
}

// partial returns a partial clause for conflict resolution.
func (c *clause[T]) partial() partialclause[T] {
	r := partialclause[T]{}

	for _, literal := range c.literals {
		r[literal.variable] = literal.negated
	}

	return r
}

// clauseList wraps up handling of clauses.
type clauseList[T comparable] struct {
	// items are all the clauses in list.
	items []clause[T]
	// unit are clauses that have one missing literal and have a value
	// of false, meaning the remaining one needs to be true.
	unit Set[*clause[T]]
}

func newClauseList[T comparable](capacity int) *clauseList[T] {
	return &clauseList[T]{
		items: make([]clause[T], 0, capacity),
		unit:  Set[*clause[T]]{},
	}
}

// Create makes a new clause.
func (l *clauseList[T]) create(literals []*Literal[T]) *clause[T] {
	id := len(l.items)

	// Expand the array.
	l.items = append(l.items, clause[T]{})

	c := &l.items[id]

	// Inplace create the clause, this avoids heavy memory allocation.
	c.init(id, literals...)

	update := func(s Boolean) error {
		return l.update(c, s)
	}

	c.subscribe(update)

	// If it's a unit clause add it now.
	if len(literals) == 1 {
		l.unit.Add(c)
	}

	return c
}

func (l *clauseList[T]) update(c *clause[T], s Boolean) error {
	// Do unit detection.
	if c.Unit() {
		l.unit.Add(c)
	} else {
		l.unit.Delete(c)
	}

	return nil
}

func (l *clauseList[T]) dump() {
	fmt.Println("clauses:")

	for i, c := range l.items {
		fmt.Println(i, ":", c.Value(), c)
	}
}

// partialclause is used during conflic resolution to resolve a new clause.
// It maps the variable to whether or not it's negated.
type partialclause[T comparable] map[*variable[T]]bool

// resolve combines two partial clauses such that (^A v B v C) and (A, D, ^E)
// combine to form (B v C v D v ^E) i.e. ^A and A cancel each other out.
func (p partialclause[T]) resolve(o partialclause[T]) partialclause[T] {
	r := partialclause[T]{}

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

// pathEntry remembers decisions made as we attempt to solve the SAT problem.
type pathEntry[T comparable] struct {
	// decision did this result from a decision, rather than BCP?
	decision bool
	// level that the entry was created at.
	level int
	// variable that was set.
	variable *variable[T]
	// clause (where set by BCP) that caused the inference.
	clause *clause[T]
}

func (e *pathEntry[T]) String() string {
	cause := "(decision)"

	if !e.decision {
		cause = "(clause " + e.clause.String() + ")"
	}

	return fmt.Sprint("v", e.variable.id, "@", e.level, " ", cause)
}

// path remembers decisions and inferences made and what made them.
type path[T comparable] struct {
	entries []pathEntry[T]
}

func newPath[T comparable]() *path[T] {
	return &path[T]{}
}

func (p *path[T]) dump() {
	fmt.Println("path:")

	for _, entry := range p.entries {
		fmt.Println(entry.String())
	}
}

func (p *path[T]) push(decision bool, level int, variable *variable[T], clause *clause[T]) {
	p.entries = append(p.entries, pathEntry[T]{
		decision: decision,
		level:    level,
		variable: variable,
		clause:   clause,
	})
}

// Rollback accepts a level to roll back to and removes all entries defined
// after that level, performing any cleanup necessary.
func (p *path[T]) rollback(level int) error {
	i := slices.IndexFunc(p.entries, func(entry pathEntry[T]) bool {
		return entry.level > level
	})

	if i == -1 {
		return fmt.Errorf("%w: no entries found in path level %d", ErrUnexpected, level)
	}

	for _, entry := range p.entries[i:] {
		if err := entry.variable.undefine(); err != nil {
			return err
		}
	}

	p.entries = p.entries[:i]

	return nil
}

// CDCLSolver implements CDCL (conflict driven clause learning).
type CDCLSolver[T comparable] struct {
	// variables reference by clause literals.
	variables *variableSet[T]
	// literals allows sharing of literals.
	literals *literalCache[T]
	// clauses that make up the CNF (conjunctive noraml form).
	clauses *clauseList[T]
	// path that acts as a journal of our decisions and how we arrived there.
	path *path[T]
	// level is the decision level.
	level int
}

type CDCLOptions struct {
	// ClauseCapacity allows upfront allocation of clauses.  While this is
	// not an upper limit it can have a huge impact on initialization performance
	// when defining your clauses.  Ignored if <= 0.
	ClauseCapacity int
}

func NewCDCLSolver[T comparable](o *CDCLOptions) *CDCLSolver[T] {
	// This is fine for small problems, you may need to make this quite
	// large for bigger ones.
	clauseCapacity := 1000

	if o != nil {
		if o.ClauseCapacity > 0 {
			clauseCapacity = o.ClauseCapacity
		}
	}

	return &CDCLSolver[T]{
		variables: newVariableSet[T](),
		literals:  newLiteralCache[T](),
		clauses:   newClauseList[T](clauseCapacity),
		path:      newPath[T](),
	}
}

func (s *CDCLSolver[T]) literal(t T, negated bool) *Literal[T] {
	if l, ok := s.literals.get(t, negated); ok {
		return l
	}

	l := newLiteral(s.variables.get(t), negated)

	s.literals.set(t, negated, l)

	return l
}

// Literal gets a literal for use in a clause.
func (s *CDCLSolver[T]) Literal(t T) *Literal[T] {
	return s.literal(t, false)
}

// NegatedLiteral gets a negated literal for use in a clause.
func (s *CDCLSolver[T]) NegatedLiteral(t T) *Literal[T] {
	return s.literal(t, true)
}

// Clause defines a new clause from a set of literals.
func (s *CDCLSolver[T]) Clause(literals ...*Literal[T]) {
	s.clauses.create(literals)
}

// Unary adds a unary clause e.g. this must be true.
func (s *CDCLSolver[T]) Unary(t T) {
	s.Clause(s.Literal(t))
}

// NegatedUnary adds a negated unary clause e.g. this must be false.
func (s *CDCLSolver[T]) NegatedUnary(t T) {
	s.Clause(s.NegatedLiteral(t))
}

// AtLeastOneOf is a helper that defines a clause:
// x1 v x2 v x3 v ... xN.
func (s *CDCLSolver[T]) AtLeastOneOf(t ...T) {
	l := make([]*Literal[T], len(t))

	for i := range t {
		l[i] = s.Literal(t[i])
	}

	s.Clause(l...)
}

// AtMostOneOf is a helper that defines a set of clauses:
// ^x1 v ^x2, ^x1 v ^x3, ..., ^xN-1 v ^xN.
func (s *CDCLSolver[T]) AtMostOneOf(t ...T) {
	l := make([]*Literal[T], len(t))

	for i := range t {
		l[i] = s.NegatedLiteral(t[i])
	}

	for a, b := range Permute(l) {
		s.Clause(a, b)
	}
}

// ImpliesAtLeastOneOf is a helper that defines a clause:
// ^x1 v y1 v y2 v ... yN.
func (s *CDCLSolver[T]) ImpliesAtLeastOneOf(t T, ti ...T) {
	l := make([]*Literal[T], len(ti)+1)

	l[0] = s.NegatedLiteral(t)

	for i := range ti {
		l[i+1] = s.Literal(ti[i])
	}

	s.Clause(l...)
}

func (s *CDCLSolver[T]) Dump() {
	s.variables.dump()
	s.clauses.dump()
	s.path.dump()
}

// bcpSingle runs a single BCP pass, returning true if we did something.
func (s *CDCLSolver[T]) bcpSingle() (bool, error) {
	// TODO: deterministic option?
	for clause := range s.clauses.unit.All() {
		// Find the unset literal and make it true...
		for _, literal := range clause.literals {
			if literal.Undefined() {
				s.path.push(false, s.level, literal.variable, clause)

				if err := literal.variable.define(!literal.negated); err != nil {
					return false, err
				}

				return true, nil
			}
		}
	}

	return false, nil
}

// bcp performs BCP while it can, or until a conflict is detected.
// Returns true on a conflict and the clause that caused the conflict.
func (s *CDCLSolver[T]) bcp() error {
	for {
		ok, err := s.bcpSingle()
		if err != nil {
			return err
		}

		if !ok {
			break
		}
	}

	return nil
}

// partialVariablesAtCurrentLevel returns the number of variables that are contained in
// the partial that were set at the current level.  When this hits 1 we've finished
// resolution.  While we are at it, we also keep tabs on the asserting level we will
// need to roll back to.
func (s *CDCLSolver[T]) partialVariablesAtCurrentLevel(partial partialclause[T], assertingLevel *int) int {
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

func (s *CDCLSolver[T]) handleConflict(clause *clause[T]) error {
	partial := clause.partial()

	var assertingLevel int

	for _, entry := range slices.Backward(s.path.entries) {
		// If the entry doesn't contain the current variable, skip it.
		if _, ok := partial[entry.variable]; !ok {
			continue
		}

		// If it does, then resolve the new partial.
		partial = partial.resolve(entry.clause.partial())

		// If the partial only contains a single variable at the current
		// decision level, then we are done!
		if s.partialVariablesAtCurrentLevel(partial, &assertingLevel) == 1 {
			break
		}
	}

	// Perform the rollback before we add the new clause so we get the pub/sub
	// into a sane value, otherwise the new clause will probably see undefines
	// it shouldn't.
	s.level = assertingLevel

	if err := s.path.rollback(assertingLevel); err != nil {
		s.path.dump()
		return err
	}

	// Finally add our new clause.
	l := make([]*Literal[T], 0, len(partial))

	// TODO: deterministic option?
	for variable := range partial {
		l = append(l, newLiteral(variable, partial[variable]))
	}

	s.clauses.create(l)

	for variable := range partial {
		if err := variable.notify(); err != nil {
			return err
		}
	}

	return nil
}

// Solve does the top level solving of the SAT problem.  It accepts a custom
// decision function so the client can choose how to select a candidate when
// trial and error is required.  For example, you may maintain some domain
// specific knowledge about variables and clauses and be able to make more
// sensible choices than an arbitrary selector.
func (s *CDCLSolver[T]) Solve(decide func(*CDCLSolver[T]) (T, bool)) error {
	// Do an initial boolean constant propagation.
	if err := s.bcp(); err != nil {
		return fmt.Errorf("conflict at decision level 0: %w", err)
	}

	// Until we've fully defined all variables.
	for !s.variables.complete() {
		// Increase the decision level and select a variable to set, we need
		// to guess here as BCP cannot complete the task by itself.
		s.level++

		t, value := decide(s)

		variable := s.variables.get(t)

		if err := variable.define(value); err != nil {
			return err
		}

		s.path.push(true, s.level, variable, nil)

		for {
			// If BCP has done all it can after the last guess,
			// see if we're complete, otherwise make another guess.
			err := s.bcp()
			if err == nil {
				break
			}

			var cerr *ConflictError[T]

			if !errors.As(err, &cerr) {
				return fmt.Errorf("unexpected error type: %w", err)
			}

			if err := s.handleConflict(cerr.clause); err != nil {
				return fmt.Errorf("unexpected conflict error: %w", err)
			}
		}
	}

	return nil
}

func (s *CDCLSolver[T]) Variables() iter.Seq2[T, Boolean] {
	return func(yield func(T, Boolean) bool) {
		for _, v := range s.variables.list {
			if !yield(v.userinfo, v.Boolean) {
				return
			}
		}
	}
}

func DefaultChooser[T comparable](s *CDCLSolver[T]) (T, bool) {
	for t, v := range s.Variables() {
		if v.Undefined() {
			return t, true
		}
	}

	panic("failed to select a variable")
}
