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
	"iter"
	"maps"
	"slices"
)

// Set allows O(log N) insertion and deletion.
type Set[T comparable] map[T]any

func NewSet[T comparable]() Set[T] {
	return map[T]any{}
}

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

func (s *Set[T]) Clear() {
	*s = map[T]any{}
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
