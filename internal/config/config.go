// Package config provides a struct with global options passed on the
// command-line.
package config

import (
	"flag"
	"fmt"
	"io"
	"os"
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
}

// GetConfiguration looks at the command-line arguments passed to the program
// and extracts a [Configuration] struct from them. If that fails, this function
// exits with code [ConfigurationErrorExit].
func GetConfiguration() (ret Configuration) {

	// Define for error handling
	var err error

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

	return
}
