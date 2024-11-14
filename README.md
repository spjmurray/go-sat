# go-sat

A boolean satisfiability (SAT) solver for Go!

## Details

This uses provides a CDCL (conflict driven clause learning) SAT solver.

There is provision for custom variable selection logic, so you can make more intelligent descisions about which variables to guess values for, and the values themselves.

And it's pretty quick, the provided Sudoku benchmark is configured and solved in ~9ms, and that's doing an "extreme" problem sourced from [sudoku.com](sudoku.com).

```
goos: linux
goarch: amd64
pkg: github.com/spjmurray/go-sat
cpu: 12th Gen Intel(R) Core(TM) i7-1270P
BenchmarkSudoku-16    	     138	   8952452 ns/op
PASS
```
