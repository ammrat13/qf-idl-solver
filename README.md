# `QF_IDL` Solver

Solver for quantifier-free integer difference logic, named `QF_IDL` in the
[SMT-LIB Specification][1]. It was built to profile different strategies for
theory solving.

It uses an off-the-shelf SAT solver as a black box, meaning it doesn't implement
all of DPLL(T). Furthermore, while the parser handles `let` bindings correctly,
it only parses the "official" syntax for `QF_IDL`. That means this program
doesn't accept atoms of the following forms:
```
(op x (+ y n))
(op x (- y n))
(op x (+ y (- n)))
(op x (- y (- n)))
```

## Usage

This program accepts one SMT-LIB file as input. The input is expected to be
`QF_IDL`. If it isn't, the program will either fail to parse it or throw an
error.

In addition to the input file, this program accepts a few command-line flags:
* `stats`: prints statistics at the end of a run instead of `sat` / `unsat`.
* `csv`: prints statistics in CSV format instead of the default human-readable
  format. This flag has no effect if `stats` is not specified.
* `soft-timeout` and `hard-timeout`: accept a duration as an argument, and give
  up solving after that duration. If the program gives up, the returned status
  is `unknown`. Otherwise, the status is either `sat` or `unsat`. Also, the
  timeout doesn't count the time taken to ingest and preprocess the file.
  * `soft-timeout`: waits for the current iteration of the solver to complete
    before terminating.
  * `hard-timeout`: kills the process after the duration elapses, possibly
    leaving the statistics in an inconsistent state.

Command-line flags can also be used to specify the preprocessing and theory
solving strategies. The available preprocessing strategies, specified with the
`preprocessor` flag, are:

* `nil`: no preprocessing
* `t-lin`: apply the T rule to consecutive inequalities, thereby adding a linear
  number of clauses.
* `t-quad`: apply the T rule to all possible inequalities, thereby adding a
  quadratic number of clauses.
* `tie-lin`: apply the T, I, and E rules with linear blowup.
* `tie-quad`: apply the T, I, and E rules with quadratic blowup.

The available theory solving strategies, specified with `solver`, are:
* `bf-basic`: [Bellman-Ford][2]
* `bf-full`: [Bellman-Ford][2] with the [early-stopping optimization][2]
* `spfa-basic`: [Shortest Path Faster Algorithm][3]
* `spfa-full`: [Shortest Path Faster Algorithm][3] with [amortized parent-graph
  search][4]
* `tarjan`: [Tarjan's Algorithm][5]

## Building

The program can be built with the standard `go build` command. The only extra
consideration is if the lexer - in `internal/file/lexing.go` - is modified. When
it is, it has to be regenerated with the following commands:
```
$ go generate ./...
$ go fmt ./...
```
The generate script requires both `bash` and [`participle`][6] be on the `PATH`.
To install the latter, clone it from its [GitHub][6], then run:
```
$ pushd cmd/participle/
$ go install github.com/alecthomas/participle/v2/cmd/participle
$ popd
```

## Testing

Unit tests can be run with:
```
$ go test -short ./...
```

Long tests try parsing all the benchmarks in the `bench/` directory to check
that ingestion works. Follow the instruction in the `bench/` folder to set it
up, then run:
```
$ go test ./...
```
When running the long tests, you'll probably need to set `GOMAXPROCS` so as to
not run out of RAM.

Theory solvers are tested via fuzzing. The fuzz targets are in
`internal/theory_test/theory_test.go`, and the functions available are:
* `FuzzBFBasic`
* `FuzzBFFull`
* `FuzzSPFABasic`
* `FuzzSPFAFull`
* `FuzzTarjan`

To start fuzzing, pick a target and run:
```
$ go test -fuzz ${TARGET} ./internal/theory_test/
```

[1]: https://smtlib.cs.uiowa.edu/logics-all.shtml#QF_IDL
[2]: https://en.wikipedia.org/wiki/Bellman%E2%80%93Ford_algorithm
[3]: https://en.wikipedia.org/wiki/Shortest_path_faster_algorithm
[4]: https://konaeakira.github.io/posts/using-the-shortest-path-faster-algorithm-to-find-negative-cycles.html
[5]: https://doi.org/10.1007/s101070050058
[6]: https://github.com/alecthomas/participle
