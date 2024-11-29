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

package cdcl

import (
	"fmt"
	"iter"
	"strings"

	"github.com/spjmurray/go-util/pkg/set"
	"github.com/spjmurray/go-util/pkg/slices"
)

// Boolean wraps up a boolean variable which may be undefined.
type Boolean struct {
	// value of the boolean, nil is undefined
	value *bool
	// handle is the handle to a subscription.
	handle int
	// subscribers are the list of clients subscribed to monitor changes.
	subscribers map[int]subscribeFn
}

// NewBoolean creates a new boolean value.
func NewBoolean() Boolean {
	return Boolean{
		subscribers: map[int]subscribeFn{},
	}
}

type subscribeFn func(Boolean) error

// Undefined returns whether the variable is unset.
func (b Boolean) Undefined() bool {
	return b.value == nil
}

// Defined returns whether the variable is set.
func (b Boolean) Defined() bool {
	return b.value != nil
}

// Value returns the boolean value.  Defaults to false if unset.
func (b Boolean) Value() bool {
	return b.Defined() && *b.value
}

// subscribe registers the callback function and calls it to communicate the initial value.
func (b *Boolean) subscribe(callback subscribeFn) int {
	handle := b.handle
	b.handle++

	b.subscribers[handle] = callback

	return handle
}

func (b *Boolean) unsubscribe(handle int) {
	delete(b.subscribers, handle)
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

func (b *Boolean) reset() {
	b.value = nil
}

// variable represents a boolean variable.
type variable struct {
	// Boolean allows the variable to notify subscribers of updates.
	Boolean
	// id is the unique id of the variable.
	id int
}

func newVariable(id int) *variable {
	return &variable{
		Boolean: NewBoolean(),
		id:      id,
	}
}

// String formats a variable.
func (v *variable) String() string {
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
	// userIDToIDMap maps from user ID to an index.
	userIDToIDMap map[T]int
	// idToUserIDMap maps from index to user ID.
	idToUserIDMap map[int]T
	// variables is a set of variables.
	variables []*variable
}

func newVariableSet[T comparable]() *variableSet[T] {
	return &variableSet[T]{
		userIDToIDMap: map[T]int{},
		idToUserIDMap: map[int]T{},
	}
}

// get returns an existing or new variable based on an external name.
func (s *variableSet[T]) get(t T) *variable {
	if id, ok := s.userIDToIDMap[t]; ok {
		return s.variables[id]
	}

	id := len(s.variables)
	v := newVariable(id)

	s.userIDToIDMap[t] = id
	s.idToUserIDMap[id] = t
	s.variables = append(s.variables, v)

	return v
}

// Complete returns whether or not all variables are set.
func (s *variableSet[T]) complete() bool {
	for _, variable := range s.variables {
		if variable.Undefined() {
			return false
		}
	}

	return true
}

func (s *variableSet[T]) reset() {
	for _, v := range s.variables {
		v.reset()
	}
}

func (s *variableSet[T]) String() string {
	t := make([]string, len(s.variables))

	for i, v := range s.variables {
		t[i] = v.String()
	}

	return strings.Join(t, ", ")
}

//nolint:unused
func (s *variableSet[T]) dump() {
	fmt.Println("Variables:")
	fmt.Println(s)
}

// literal is a reference to a variable used by a clause.
type literal struct {
	// Boolean allows the variable to notify subscribers of updates.
	Boolean
	// variable is a reference to the underlying variable.
	variable *variable
	// negated is whether or not the boolean value is negated.
	negated bool
}

func newLiteral(variable *variable, negated bool) *literal {
	l := &literal{
		Boolean:  NewBoolean(),
		variable: variable,
		negated:  negated,
	}

	variable.subscribe(l.update)

	return l
}

// update accespts updates from the underlying variable, does any necessary
// mutations due to negation, then notifies any subscribed clauses.
func (l *literal) update(v Boolean) error {
	if v.Defined() {
		return l.define(v.Value() != l.negated)
	}

	return l.undefine()
}

// String formats a literal.
func (l *literal) String() string {
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
	cache map[literalCacheKey[T]]*literal
}

func newLiteralCache[T comparable]() *literalCache[T] {
	return &literalCache[T]{
		cache: map[literalCacheKey[T]]*literal{},
	}
}

func (c *literalCache[T]) get(variable T, negated bool) (*literal, bool) {
	v, ok := c.cache[literalCacheKey[T]{variable: variable, negated: negated}]
	return v, ok
}

func (c *literalCache[T]) set(variable T, negated bool, literal *literal) {
	c.cache[literalCacheKey[T]{variable: variable, negated: negated}] = literal
}

func (c *literalCache[T]) reset() {
	for _, l := range c.cache {
		l.reset()
	}
}

// clause is a logical OR of literals.
type clause struct {
	// Boolean allows the variable to notify subscribers of updates.
	Boolean
	// id is the unique id of the clause.
	id int
	// literals is an ordered list of all iterals that make up the clause.
	literals []*literal
	// handles remembers all the subsriptions so we can remove them on
	// destruction.
	handles []int
	// numDefined is a count of the number of defined literals.
	numDefined int
	// literalDefined records whether a value as defined.
	literalDefined []int64
	// literalValues records the boolean values of all the literals (upto 64 for now...)
	literalValues []int64
}

func newClause(id int, literals []*literal) *clause {
	// The maths for the values is quite simple.
	// ((1 + 63) >> 6) = (64 >> 6) = 1
	// ((64 + 63) >> 6) = (127 >> 6) = 1
	words := (len(literals) + 63) >> 6

	c := &clause{
		Boolean:        NewBoolean(),
		id:             id,
		literals:       literals,
		handles:        make([]int, len(literals)),
		literalDefined: make([]int64, words),
		literalValues:  make([]int64, words),
	}

	for i := range literals {
		update := func(s Boolean) error {
			return c.update(i, s)
		}

		c.handles[i] = literals[i].subscribe(update)
	}

	return c
}

// String formats a clause.
func (c clause) String() string {
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
func (c *clause) Complete() bool {
	return c.numDefined == len(c.literals)
}

// Unit tells us if one literal is unset and it has to be true.
func (c *clause) Unit() bool {
	return c.numDefined == len(c.literals)-1 && !c.Value()
}

// Value tells us whether there is a conflict (false), or not.
func (c *clause) Value() bool {
	for _, i := range c.literalValues {
		if i != 0 {
			return true
		}
	}

	return false
}

func (c *clause) reset() {
	c.Boolean.reset()

	for i := range c.literalDefined {
		c.literalDefined[i] = 0
		c.literalValues[i] = 0
	}
}

func (c *clause) destroy() {
	for i := range c.literals {
		c.literals[i].unsubscribe(c.handles[i])
	}
}

// ConflictError is returned when a clause resolves to false.
type ConflictError struct {
	clause *clause
}

// Error implements the error interface.
func (e *ConflictError) Error() string {
	return fmt.Sprint("conflict error: ", e.clause)
}

//nolint:cyclop
func (c *clause) update(i int, s Boolean) error {
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
		return &ConflictError{
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
func (c *clause) partial() partialclause {
	r := partialclause{}

	for _, literal := range c.literals {
		r[literal.variable] = literal.negated
	}

	return r
}

// clauseList wraps up handling of clauses.
type clauseList struct {
	// items are all the clauses in list.
	items []*clause
	// unit are clauses that have one missing literal and have a value
	// of false, meaning the remaining one needs to be true.
	unit set.Set[*clause]
}

func newClauseList() *clauseList {
	return &clauseList{
		unit: set.New[*clause](),
	}
}

// Create makes a new clause.
func (l *clauseList) create(literals []*literal) *clause {
	id := len(l.items)

	c := newClause(id, literals)

	l.items = append(l.items, c)

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

func (l *clauseList) update(c *clause, s Boolean) error {
	// Do unit detection.
	if c.Unit() {
		l.unit.Add(c)
	} else {
		l.unit.Delete(c)
	}

	return nil
}

func (l *clauseList) reset() {
	for _, c := range l.items {
		c.reset()
	}

	l.unit.Clear()
}

func (l *clauseList) destroy() {
	for _, c := range l.items {
		c.destroy()
	}
}

//nolint:unused
func (l *clauseList) dump() {
	fmt.Println("clauses:")

	for i, c := range l.items {
		fmt.Println(i, ":", c.Value(), c)
	}
}

// ModelInterface provides a type agnostic interface for the main solver algorithm.
type ModelInterface interface {
	// variablesByID iterates over variables by generic ID.
	variablesByID() iter.Seq2[int, Boolean]
	// complete is true of all variables are defined.
	complete() bool
	// unit returns an iterator over all unit clauses.
	unit() iter.Seq[*clause]
	// createLearnedClause adds a new clause.
	createLearnedClause(l []*literal)
	// getVariable maps from variable ID to variable.
	getVariable(id int) *variable
}

// Model implements a CNF model.
type Model[T comparable] struct {
	// variables reference by clause literals.
	variables *variableSet[T]
	// literals allows sharing of literals.
	literals *literalCache[T]
	// clauses that make up the CNF (conjunctive noraml form).
	clauses *clauseList
	// learnedClauses are those defined by the CDCL algoithm.
	learnedClauses *clauseList
}

// New returns a new model.
func NewModel[T comparable]() *Model[T] {
	return &Model[T]{
		variables:      newVariableSet[T](),
		literals:       newLiteralCache[T](),
		clauses:        newClauseList(),
		learnedClauses: newClauseList(),
	}
}

func (m *Model[T]) complete() bool {
	return m.variables.complete()
}

func (m *Model[T]) createLearnedClause(l []*literal) {
	m.learnedClauses.create(l)
}

func (m *Model[T]) getVariable(id int) *variable {
	return m.variables.variables[id]
}

func (m *Model[T]) literal(t T, negated bool) *literal {
	if l, ok := m.literals.get(t, negated); ok {
		return l
	}

	l := newLiteral(m.variables.get(t), negated)

	m.literals.set(t, negated, l)

	return l
}

// Clause defines a new clause from a set of literals.
func (m *Model[T]) Clause(literals ...*literal) {
	m.clauses.create(literals)
}

// Unary adds a unary clause e.g. this must be true.
// NOTE: The assumption here is this is an initial condition for the problem
// being solved, and should not be preserved across resets.
func (m *Model[T]) Unary(t T) {
	m.learnedClauses.create([]*literal{m.literal(t, false)})
}

// NegatedUnary adds a negated unary clause e.g. this must be false.
// NOTE: The assumption here is this is an initial condition for the problem
// being solved, and should not be preserved across resets.
func (m *Model[T]) NegatedUnary(t T) {
	m.learnedClauses.create([]*literal{m.literal(t, true)})
}

// AtLeastOneOf is a helper that defines a clause:
// x1 v x2 v x3 v ... xN.
func (m *Model[T]) AtLeastOneOf(t ...T) {
	l := make([]*literal, len(t))

	for i := range t {
		l[i] = m.literal(t[i], false)
	}

	m.Clause(l...)
}

// AtMostOneOf is a helper that defines a set of clauses:
// ^x1 v ^x2, ^x1 v ^x3, ..., ^xN-1 v ^xN.
func (m *Model[T]) AtMostOneOf(t ...T) {
	l := make([]*literal, len(t))

	for i := range t {
		l[i] = m.literal(t[i], true)
	}

	for a, b := range slices.Permute(l) {
		m.Clause(a, b)
	}
}

// ImpliesAtLeastOneOf is a helper that defines a clause:
// ^x1 v y1 v y2 v ... yN.
func (m *Model[T]) ImpliesAtLeastOneOf(t T, ti ...T) {
	l := make([]*literal, len(ti)+1)

	l[0] = m.literal(t, true)

	for i := range ti {
		l[i+1] = m.literal(ti[i], false)
	}

	m.Clause(l...)
}

func (m *Model[T]) variablesByID() iter.Seq2[int, Boolean] {
	return func(yield func(int, Boolean) bool) {
		for i, v := range m.variables.variables {
			if !yield(i, v.Boolean) {
				return
			}
		}
	}
}

func (m *Model[T]) Variables() iter.Seq2[T, Boolean] {
	return func(yield func(T, Boolean) bool) {
		for i, v := range m.variables.variables {
			if !yield(m.variables.idToUserIDMap[i], v.Boolean) {
				return
			}
		}
	}
}

func (m *Model[T]) unit() iter.Seq[*clause] {
	return func(yield func(*clause) bool) {
		for c := range m.clauses.unit.All() {
			if !yield(c) {
				return
			}
		}

		for c := range m.learnedClauses.unit.All() {
			if !yield(c) {
				return
			}
		}
	}
}

// Reset resets the mode for reuse.  Any unary clauses will be deleted.
func (m *Model[T]) Reset() {
	m.variables.reset()
	m.literals.reset()
	m.clauses.reset()

	m.learnedClauses.destroy()
	m.learnedClauses = newClauseList()
}

// dump prints the model state to the console.
//
//nolint:unused
func (m *Model[T]) dump() {
	m.variables.dump()
	m.clauses.dump()
}
