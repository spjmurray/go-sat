/*
Copyright 2024 the Unikorn Authors.

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

package sat_test

import (
	"fmt"
	"iter"
	"testing"

	sat "github.com/spjmurray/go-sat"
)

//nolint:gochecknoglobals
var sudoku = [9][9]int{
	{6, 0, 0, 0, 0, 3, 2, 0, 4},
	{0, 4, 0, 2, 0, 0, 0, 9, 0},
	{0, 0, 8, 0, 0, 0, 0, 5, 0},
	{0, 0, 9, 0, 3, 0, 0, 0, 0},
	{0, 0, 0, 6, 0, 0, 0, 0, 0},
	{3, 0, 6, 0, 0, 0, 5, 4, 0},
	{8, 0, 3, 0, 0, 2, 4, 0, 0},
	{0, 0, 0, 1, 8, 0, 0, 6, 0},
	{1, 6, 5, 0, 7, 0, 0, 0, 8},
}

// Generates a useful name for our variables so we can map them back
// to aSudoku board.
func varName(i, j, n int) string {
	return fmt.Sprintf("%d:%d:%d", i, j, n)
}

func permute[T any](t []T) iter.Seq2[T, T] {
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

// sudokuRules adds Sudoku rules to the solver.
//
//nolint:gocognit,cyclop
func sudokuRules(s *sat.CDCLSolver) {
	for i := range 9 {
		for j := range 9 {
			literals := make([]*sat.Literal, 9)
			negated := make([]*sat.Literal, 9)

			for n := range 9 {
				literals[n] = s.Literal(varName(i, j, n))
				negated[n] = s.NegatedLiteral(varName(i, j, n))
			}

			// Every cell must have a value. e.g:
			//
			//   0 v 2 v 3 v 4 v 5 v 6 v 7 v 8
			s.Clause(literals...)

			// Every cell can only have one value.  e.g.
			//
			//   ^0 v ^1 (false if both 0 and 1 are set)
			//   ^0 v ^2 (false if both 0 and 2 are set)
			//   ...
			for a, b := range permute(negated) {
				s.Clause(a, b)
			}
		}

		// In every row a value can only occur once.
		for n := range 9 {
			literals := make([]*sat.Literal, 9)

			for j := range 9 {
				literals[j] = s.NegatedLiteral(varName(i, j, n))
			}

			for a, b := range permute(literals) {
				s.Clause(a, b)
			}
		}
	}

	// In every column a value can only occur once.
	for j := range 9 {
		for n := range 9 {
			literals := make([]*sat.Literal, 9)

			for i := range 9 {
				literals[i] = s.NegatedLiteral(varName(i, j, n))
			}

			for a, b := range permute(literals) {
				s.Clause(a, b)
			}
		}
	}

	// For evrer 3 * 3 block, a number can only occur once.
	for i := 0; i < 9; i += 3 {
		for j := 0; j < 9; j += 3 {
			for n := range 9 {
				literals := make([]*sat.Literal, 0, 9)

				for x := range 3 {
					for y := range 3 {
						literals = append(literals, s.NegatedLiteral(varName(i+x, j+y, n)))
					}
				}

				for a, b := range permute(literals) {
					s.Clause(a, b)
				}
			}
		}
	}
}

func sudokuInitialize(s *sat.CDCLSolver) {
	for i := range 9 {
		for j := range 9 {
			if sudoku[i][j] > 0 {
				s.Clause(s.Literal(varName(i, j, sudoku[i][j]-1)))
			}
		}
	}
}

func sudokuPrint(s *sat.CDCLSolver) {
	result := [9][9]int{}

	for name, value := range s.Variables() {
		if value {
			var i, j, n int

			_, _ = fmt.Sscanf(name, "%d:%d:%d", &i, &j, &n)

			result[i][j] = n + 1
		}
	}

	fmt.Println("\u250c\u2500\u2500\u2500\u252c\u2500\u2500\u2500\u252c\u2500\u2500\u2500\u2510")

	for i := range 9 {
		if i != 0 && i%3 == 0 {
			fmt.Println("\u251c\u2500\u2500\u2500\u253c\u2500\u2500\u2500\u253c\u2500\u2500\u2500\u2524")
		}

		for j := range 9 {
			if j%3 == 0 {
				fmt.Print("\u2502")
			}

			if result[i][j] == 0 {
				fmt.Print(" ")
			} else {
				fmt.Print(result[i][j])
			}
		}

		fmt.Println("\u2502")
	}

	fmt.Println("\u2514\u2500\u2500\u2500\u2534\u2500\u2500\u2500\u2534\u2500\u2500\u2500\u2518")
}

func ExampleCDCLSolver() {
	s := sat.NewCDCLSolver()

	// Add implicit rules that apply to all Sudoku problems.
	sudokuRules(s)

	// Add unit clauses from the initial state.
	sudokuInitialize(s)

	if !s.Solve(sat.DefaultChooser) {
		panic("unsolvable")
	}

	sudokuPrint(s)

	// Output:
	// ┌───┬───┬───┐
	// │691│753│284│
	// │547│218│396│
	// │238│496│157│
	// ├───┼───┼───┤
	// │489│531│672│
	// │752│649│831│
	// │316│827│549│
	// ├───┼───┼───┤
	// │873│962│415│
	// │924│185│763│
	// │165│374│928│
	// └───┴───┴───┘
}

func BenchmarkSudoku(b *testing.B) {
	for range b.N {
		s := sat.NewCDCLSolver()

		sudokuRules(s)
		sudokuInitialize(s)

		if !s.Solve(sat.DefaultChooser) {
			b.Fatal()
		}
	}
}
