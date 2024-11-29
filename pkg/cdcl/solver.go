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
	"errors"
	"fmt"
	"slices"
)

var (
	ErrUnexpected = errors.New("unexpected error")
)

// partialclause is used during conflic resolution to resolve a new clause.
// It maps the variable to whether or not it's negated.
type partialclause map[*variable]bool

// resolve combines two partial clauses such that (^A v B v C) and (A, D, ^E)
// combine to form (B v C v D v ^E) i.e. ^A and A cancel each other out.
func (p partialclause) resolve(o partialclause) partialclause {
	r := partialclause{}

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
type pathEntry struct {
	// decision did this result from a decision, rather than BCP?
	decision bool
	// level that the entry was created at.
	level int
	// variable that was set.
	variable *variable
	// clause (where set by BCP) that caused the inference.
	clause *clause
}

func (e *pathEntry) String() string {
	cause := "(decision)"

	if !e.decision {
		cause = "(clause " + e.clause.String() + ")"
	}

	return fmt.Sprint("v", e.variable.id, "@", e.level, " ", cause)
}

// path remembers decisions and inferences made and what made them.
type path struct {
	entries []pathEntry
}

func newPath() *path {
	return &path{}
}

//nolint:unused
func (p *path) dump() {
	fmt.Println("path:")

	for _, entry := range p.entries {
		fmt.Println(entry.String())
	}
}

func (p *path) push(decision bool, level int, variable *variable, clause *clause) {
	p.entries = append(p.entries, pathEntry{
		decision: decision,
		level:    level,
		variable: variable,
		clause:   clause,
	})
}

// Rollback accepts a level to roll back to and removes all entries defined
// after that level, performing any cleanup necessary.
func (p *path) rollback(level int) error {
	i := slices.IndexFunc(p.entries, func(entry pathEntry) bool {
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

// Solver implements CDCL (conflict driven clause learning).
type Solver struct {
	// path that acts as a journal of our decisions and how we arrived there.
	path *path
	// level is the decision level.
	level int
}

// New creates a new CDCL solver.
func New() *Solver {
	return &Solver{
		path: newPath(),
	}
}

// dump prints solver state to the console.
//
//nolint:unused
func (s *Solver) dump() {
	s.path.dump()
}

// bcpSingle runs a single BCP pass, returning true if we did something.
func (s *Solver) bcpSingle(m ModelInterface) (bool, error) {
	// TODO: deterministic option?
	for clause := range m.unit() {
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
func (s *Solver) bcp(m ModelInterface) error {
	for {
		ok, err := s.bcpSingle(m)
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
func (s *Solver) partialVariablesAtCurrentLevel(partial partialclause, assertingLevel *int) int {
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

func (s *Solver) handleConflict(m ModelInterface, clause *clause) error {
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
		return err
	}

	// Finally add our new clause.
	l := make([]*literal, 0, len(partial))

	for variable := range partial {
		l = append(l, newLiteral(variable, partial[variable]))
	}

	m.createLearnedClause(l)

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
func (s *Solver) Solve(m ModelInterface, decide func(ModelInterface) (int, bool)) error {
	// Do an initial boolean constant propagation.
	if err := s.bcp(m); err != nil {
		return fmt.Errorf("conflict at decision level 0: %w", err)
	}

	// Until we've fully defined all variables.
	for !m.complete() {
		// Increase the decision level and select a variable to set, we need
		// to guess here as BCP cannot complete the task by itself.
		s.level++

		id, value := decide(m)

		variable := m.getVariable(id)

		if err := variable.define(value); err != nil {
			return err
		}

		s.path.push(true, s.level, variable, nil)

		for {
			// If BCP has done all it can after the last guess,
			// see if we're complete, otherwise make another guess.
			err := s.bcp(m)
			if err == nil {
				break
			}

			var cerr *ConflictError

			if !errors.As(err, &cerr) {
				return fmt.Errorf("unexpected error type: %w", err)
			}

			if err := s.handleConflict(m, cerr.clause); err != nil {
				return fmt.Errorf("unexpected conflict error: %w", err)
			}
		}
	}

	return nil
}

// DefaultChooser selects a variable to set.  This defaults to the first one
// found that is unset, and sets it to false.
func DefaultChooser(m ModelInterface) (int, bool) {
	for i, v := range m.variablesByID() {
		if v.Undefined() {
			return i, false
		}
	}

	panic("failed to select a variable")
}
