// Package config provides a struct with global options passed on the
// command-line.
package config

import (
	"flag"
	"fmt"
	"io"
	"os"
	"time"

	"github.com/ammrat13/qf-idl-solver/internal/preprocess"
	"github.com/ammrat13/qf-idl-solver/internal/theory"
)

// The ConfigurationErrorExit value is the exit code when this program fails to
// parse command-line arguments.
const ConfigurationErrorExit = 2

// The Configuration struct describes the arguments to one run of the program.
type Configuration struct {
	// Input is the reader from which the input file is read.
	Input io.Reader
	// InputName is the name of the input file.
	InputName string

	// Preprocessor is the object we will use to preprocess the clauses.
	Preprocessor preprocess.Preprocessor
	// PreprocessorName is the name of the preprocessor we will use.
	PreprocessorName string

	// Solver is the theory solver we will use.
	Solver theory.Solver
	// SolverName is the name of the theory solver we will use.
	SolverName string

	// PrintStats reports whether we should print out statistics at the end
	// rather than the result.
	PrintStats bool
	// CSVStats reports whether we should print statistics in CSV format instead
	// of human-readable format. This value only matters when PrintStats is set.
	CSVStats bool

	// SoftTimeout is how long to try solving before stopping instead of
	// looping.
	SoftTimeout time.Duration
	// HardTimeout is how long to try solving for before killing ourselves.
	HardTimeout time.Duration
}

// GetConfiguration looks at the command-line arguments passed to the program
// and extracts a [Configuration] struct from them. If that fails, this function
// exits with code [ConfigurationErrorExit].
func GetConfiguration() (ret Configuration) {

	// Define for error handling
	var err error
	var ok bool

	flag.Usage = func() {
		// Define usage message. This way, we can get a nice message if the user
		// gives bad arguments.
		const usg = "Usage: qf-idl-solver [OPTIONS] INPUT.smt2\n"

		// Actually print it, along with the auto-generated documentation for
		// all the options.
		fmt.Fprint(os.Stderr, usg)
		flag.PrintDefaults()
	}

	// Handle command-line flags.
	flag.StringVar(&ret.PreprocessorName, "preprocessor", "", "What preprocessor to use on the database")
	flag.StringVar(&ret.SolverName, "solver", "", "What theory to use")
	flag.BoolVar(&ret.PrintStats, "stats", false, "Print statistics instead of problem status")
	flag.BoolVar(&ret.CSVStats, "csv", false, "Print statistics in CSV format")
	flag.DurationVar(&ret.SoftTimeout, "soft-timeout", 0, "How long to wait before stopping iterations")
	flag.DurationVar(&ret.HardTimeout, "hard-timeout", 0, "How long to wait before killing ourselves")
	flag.Parse()

	// Now we have to handle the input file. First, check that we actually got
	// an input file to parse. If we weren't print the usage before bailing.
	if len(flag.Args()) == 0 {
		fmt.Fprintln(os.Stderr, "input file not supplied")
		flag.Usage()
		os.Exit(ConfigurationErrorExit)
	}
	// Next, try to open the file. It's a hard error if it doesn't exist, so
	// don't print the usage here
	ret.InputName = flag.Arg(0)
	ret.Input, err = os.Open(ret.InputName)
	if err != nil {
		fmt.Fprintf(os.Stderr, "could not open input file '%s'\n", ret.InputName)
		os.Exit(ConfigurationErrorExit)
	}

	// Lookup the preprocessor and set it.
	ret.Preprocessor, ok = preprocess.Preprocessors[ret.PreprocessorName]
	if !ok {
		if ret.PreprocessorName == "" {
			fmt.Fprint(os.Stderr, "no preprocessor supplied")
		} else {
			fmt.Fprintf(os.Stderr, "unknown preprocessor '%s'", ret.PreprocessorName)
		}
		fmt.Fprintln(os.Stderr, "; select from:")
		for n := range preprocess.Preprocessors {
			fmt.Fprintf(os.Stderr, "  - '%s'\n", n)
		}
		os.Exit(ConfigurationErrorExit)
	}
	// Do the same for the theory solver
	ret.Solver, ok = theory.Solvers[ret.SolverName]
	if !ok {
		if ret.SolverName == "" {
			fmt.Fprint(os.Stderr, "no solver supplied")
		} else {
			fmt.Fprintf(os.Stderr, "unknown solver '%s'", ret.SolverName)
		}
		fmt.Fprintln(os.Stderr, "; select from:")
		for n := range theory.Solvers {
			fmt.Fprintf(os.Stderr, "  - '%s'\n", n)
		}
		os.Exit(ConfigurationErrorExit)
	}

	return
}
