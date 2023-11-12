package qfidllib

import (
	"errors"
	"strings"

	"github.com/alecthomas/participle/v2/lexer"
)

// This variable defines the lexer we use for QFIDL-LIB files
var theLexer = lexer.MustSimple([]lexer.SimpleRule{

	// These rules match whitespace. The lowercase at the front means these
	// are elided from the lexer's output.
	{Name: "whitespace", Pattern: `[ \t\n\r]+`},

	// Pparse the version number. This is a special case since identifiers can
	// start with a dot. Also, this has to come before we parse numbers because
	// rules are processed in order.
	{Name: "VersionNum", Pattern: `(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)`},
	// These are to parse literals. We parse integer and string literals,
	// but we don't parse floats (decimals in the spec). We also disregard
	// hexadecimal and binary literals, since QF_IDL doesn't allow them.
	{Name: "NumberLit", Pattern: `0|[1-9][0-9]*`},
	{Name: "StringLit", Pattern: `"([^"]|"")+"`},

	// These rules are to parse simple and complex symbols. Essentially, these
	// are identifiers and quoted identifiers respectively.
	{Name: "Symbol", Pattern: `\|[^|\\]*\||[A-Za-z~!@$%^&*_\-+=<>.?\/][A-Za-z0-9~!@$%^&*_\-+=<>.?\/]*`},
	// This rule parses attributes (keywords in the spec).
	{Name: "Attribute", Pattern: `:[A-Za-z~!@$%^&*_\-+=<>.?\/][A-Za-z0-9~!@$%^&*_\-+=<>.?\/]*`},

	// Finally, match parentheses.
	{Name: "ParenOpen", Pattern: `\(`},
	{Name: "ParenClose", Pattern: `\)`},
})

// Symbol is a wrapper type for identifiers. We need to have custom parsing
// logic due to complex symbols, so we use this type to do the conversion.
type Symbol string

func (sym *Symbol) Capture(values []string) error {

	// We should always get exactly one value, so panic if this doesn't happen
	if len(values) != 1 {
		panic("Should have gotten exactly one value")
	}
	// The value we get should be non-empty because of the Regex we use, so
	// check that.
	value := values[0]
	if len(value) == 0 {
		panic("Symbol should be non-empty")
	}

	// If the value isn't a quoted symbol, we're done
	if value[0] != '|' {
		*sym = Symbol(value)
		return nil
	}

	// Otherwise, check that the string has length at least two, and that it
	// ends with a `|`. These should be guaranteed by the regex.
	if len(value) < 2 || value[len(value)-1] != '|' {
		panic("Malformed complex symbol")
	}
	// If it works, assign it
	*sym = Symbol(value[1 : len(value)-1])
	return nil
}

// StringLit is a wrapper type around string literals. We need this to allow for
// escaping.
type StringLit string

func (str *StringLit) Capture(values []string) error {
	// We should always get exactly one value, so panic if this doesn't happen
	if len(values) != 1 {
		panic("Should have gotten exactly one value")
	}
	// The value we get should have length at least two, and should start and
	// end with a double quote. This is guaranteed by the regex, so check it.
	value := values[0]
	if len(value) < 2 || value[0] != '"' || value[len(value)-1] != '"' {
		panic("Malformed string literal")
	}
	// Return with substitutions, and strip away the surrounding quotation
	// marks.
	*str = StringLit(strings.Replace(value[1:len(value)-1], "\"\"", "\"", -1))
	return nil
}

// BoolLit is a wrapper type around symbols. These are expected to be either
// true or false, and it's a user error if that's not the case.
type BooleanLit bool

func (b *BooleanLit) Capture(values []string) error {
	// We should always get exactly one value, so panic if this doesn't happen
	if len(values) != 1 {
		panic("Should have gotten exactly one value")
	}
	// Switch on the value we got, and check that it is valid. The input is a
	// raw symbol, so the user may have entered something else. Check for that,
	switch value := values[0]; value {
	case "true":
		fallthrough
	case "|true|":
		*b = BooleanLit(true)
		return nil
	case "false":
		fallthrough
	case "|false|":
		*b = BooleanLit(false)
		return nil
	default:
		return errors.New("boolean literal should be either true or false")
	}
}
