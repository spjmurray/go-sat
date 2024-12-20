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

package cdcl_test

import (
	"fmt"
	"testing"

	"github.com/spjmurray/go-sat/pkg/cdcl"
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

// variable maps to a location on the grid and a value.
type variable struct {
	i int
	j int
	n int
}

// sudokuRules adds Sudoku rules to the solver.
//
//nolint:cyclop
func sudokuRules(m *cdcl.Model[variable]) {
	for i := range 9 {
		for j := range 9 {
			names := make([]variable, 9)

			for n := range 9 {
				names[n] = variable{i, j, n}
			}

			// Every cell must have one value.
			m.AtLeastOneOf(names...)
			m.AtMostOneOf(names...)
		}

		// In every row a value can only occur once.
		for n := range 9 {
			names := make([]variable, 9)

			for j := range 9 {
				names[j] = variable{i, j, n}
			}

			m.AtMostOneOf(names...)
		}
	}

	// In every column a value can only occur once.
	for j := range 9 {
		for n := range 9 {
			names := make([]variable, 9)

			for i := range 9 {
				names[i] = variable{i, j, n}
			}

			m.AtMostOneOf(names...)
		}
	}

	// For evrer 3 * 3 block, a number can only occur once.
	for i := 0; i < 9; i += 3 {
		for j := 0; j < 9; j += 3 {
			for n := range 9 {
				names := make([]variable, 9)

				for x := range 9 {
					names[x] = variable{i + x/3, j + x%3, n}
				}

				m.AtMostOneOf(names...)
			}
		}
	}
}

func sudokuInitialize(m *cdcl.Model[variable]) {
	for i := range 9 {
		for j := range 9 {
			if sudoku[i][j] > 0 {
				m.Unary(variable{i, j, sudoku[i][j] - 1})
			}
		}
	}
}

func sudokuPrint(m *cdcl.Model[variable]) {
	result := [9][9]int{}

	for variable, value := range m.Variables() {
		if value.Value() {
			result[variable.i][variable.j] = variable.n + 1
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

func ExampleSolver() {
	m := cdcl.NewModel[variable]()

	// Add implicit rules that apply to all Sudoku problems.
	sudokuRules(m)

	sudokuInitialize(m)

	s := cdcl.New()

	if err := s.Solve(m, cdcl.DefaultChooser); err != nil {
		fmt.Println(err)
	}

	sudokuPrint(m)

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
	b.StopTimer()

	m := cdcl.NewModel[variable]()

	sudokuRules(m)

	b.StartTimer()

	for range b.N {
		sudokuInitialize(m)

		s := cdcl.New()

		if err := s.Solve(m, cdcl.DefaultChooser); err != nil {
			b.Fatal(err)
		}

		m.Reset()
	}
}
