// Package parse takes an input stream and outputs an AST. It also provides the
// types to interface with the generated tree.
//
// The parser here is for a subset of SMTLIB, called QFIDLLIB. Not all SMTLIB
// files will be handled by this, and it may throw an error. See [grammar.go]
// for more details about what is accepted.
package qfidllib

import (
	"github.com/ammrat13/qf-idl-solver/internal/config"
)

// The ParseErrorExit value is the exit code when this program fails to parse an
// input file.
const ParseErrorExit = 3

// The Parse function parses a QFIDLLIB file, returning the AST. If the parse
// fails, this function exits with code [ParseErrorExit]. This function also
// modifies the supplied Configuration with the expected satisfiability state.
func Parse(cfg *config.Configuration) File {
	return File{}
}
