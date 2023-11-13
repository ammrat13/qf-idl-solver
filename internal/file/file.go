// Package file takes an input stream and outputs an AST for the file. It also
// provides the types to interface with the generated tree.
//
// The parser here is for a subset of SMT-LIB. Not all SMT-LIB files will be
// handled by this, and it may throw an error. Additionally, this grammar is
// more permissive than SMT-LIB in some aspects. See grammar.go for more details
// about what is accepted.
package file

import (
	"fmt"
	"io"
)

// The Parse function parses a QFIDL-LIB file from an input stream, returning
// the AST. If the parse fails, this function exits with code [ParseErrorExit].
func Parse(input io.Reader) (ret *File, err error) {

	// Do the parse.
	ret, err = Parser.Parse("INPUT", input)
	// If there was an error, return it.
	if err != nil {
		return
	}

	// Check that the logic type is QF_IDL. We can't work with anything else.
	if ret.Logic != "QF_IDL" {
		err = fmt.Errorf(
			"failed to parse: expected logic to be 'QF_IDL', not '%s'",
			ret.Logic,
		)
		return
	}
	// Check that we got a footer. The parser should make sure that the field is
	// true, so panic if that's not the case.
	if !ret.Footer {
		panic("Should have a footer")
	}

	return
}
