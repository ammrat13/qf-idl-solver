// Package parse takes an input stream and outputs an AST. It also provides the
// types to interface with the generated tree.
//
// The parser here is for a subset of SMTLIB, called QFIDL-LIB. Not all SMT-LIB
// files will be handled by this, and it may throw an error. Additionally,
// QFIDL-LIB is more permissive than SMT-LIB in some aspects. See grammar.go for
// more details about what is accepted.
package qfidllib

import (
	"fmt"
	"io"
	"os"

	"github.com/alecthomas/participle/v2"
)

// The ParseErrorExit value is the exit code when this program fails to parse an
// input file.
const ParseErrorExit = 3

// The Parse function parses a QFIDL-LIB file from an input stream, returning
// the AST. If the parse fails, this function exits with code [ParseErrorExit].
func Parse(input io.Reader) (ret *File) {

	// Do the parse.
	ret, err := theParser.Parse("INPUT", input)
	// If there was an error, print it out and die.
	if err != nil {
		erp := err.(participle.Error)
		pos := erp.Position()
		fmt.Fprintf(
			os.Stderr,
			"failed to parse at :%d:%d: %s\n",
			pos.Line,
			pos.Column,
			erp.Message(),
		)
		os.Exit(ParseErrorExit)
	}

	// Check that the logic type is QF_IDL. We can't work with anything else.
	if ret.Logic != "QF_IDL" {
		fmt.Fprintf(os.Stderr, "failed to parse: expected logic to be 'QF_IDL', not '%s'\n", ret.Logic)
		os.Exit(ParseErrorExit)
	}
	// Check that we got a footer. The parser should make sure that the field is
	// true, so panic if that's not the case.
	if !ret.Footer {
		panic("Should have a footer")
	}

	return
}
