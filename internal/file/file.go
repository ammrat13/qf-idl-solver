// Package file takes an input stream and outputs an AST for the file. It also
// provides the types to interface with the generated tree.
//
// The parser here is for a subset of SMT-LIB. It is more restrictive in most
// aspects, but more permissive in others. See grammar.go for more details about
// what is accepted. Most of the QF_IDL benchmarks parse correctly. It just
// doesn't support atoms of the form (op x (+ y c)).
package file

import (
	"fmt"
	"io"
)

// The Parse function parses an input stream, returning the AST. If the parse
// fails, this function exits with the appropriate err.
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
			"expected logic to be 'QF_IDL', not '%s'",
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

// The GetStatus method returns the solution status of the given file, if known.
// To find this, the method looks over all the metadata and takes the first one.
func (file File) GetStatus() Status {
	for _, mtd := range file.Metadata {
		if mtdStatus, ok := mtd.(MetadataStatus); ok {
			return mtdStatus.Status
		}
	}
	return StatusUnknown
}
