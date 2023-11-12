package qfidllib

import (
	"errors"
	"strconv"

	"github.com/alecthomas/participle/v2/lexer"
)

// Enumeration constants for [DiffOp], [BoolOp], [EqualityOp]. Not all the
// operations are present since some of them are handled with custom parse
// rules.
const (
	DiffOpLE = iota
	DiffOpLT
	DiffOpGE
	DiffOpGT
	BoolOpIMP
	BoolOpAND
	BoolOpOR
	BoolOpXOR
	OpEQ
	OpNE
)

// The Formula interface expresses all of the well-formed-formulas we can
// express in QF_IDL.
type Formula interface {
	formula()
}

// go-sumtype:decl Formula

// LitAtom represents the literal values for true and false.
type LitAtom struct {
	Value BooleanLit `parser:"@( 'true':Symbol | 'false':Symbol )"`
}

// VarAtom represents a bare variable. This must be of sort Bool, but that's
// checked later.
type VarAtom struct {
	Name Symbol `parser:"@Symbol"`
	Pos  lexer.Position
}

func (a LitAtom) formula() {}
func (a VarAtom) formula() {}

// DiffOp represents the different operations we can apply to difference atoms.
// Recall that difference atoms are of the form (op (- x y) n).
type DiffOp int

func (d DiffOp) String() string {
	switch d {
	case DiffOpLE:
		return "<="
	case DiffOpLT:
		return "<"
	case DiffOpGE:
		return ">="
	case DiffOpGT:
		return ">"
	case OpEQ:
		return "="
	case OpNE:
		return "distinct"
	default:
		panic("Invalid difference operation")
	}
}

func (d *DiffOp) Capture(values []string) error {
	// We should always get exactly one value, so panic if this doesn't happen
	if len(values) != 1 {
		panic("Should have gotten exactly one value")
	}
	// Switch on the value we got, and notify the user if they put something
	// invalid.
	switch value := values[0]; value {
	case "<=":
		*d = DiffOpLE
		return nil
	case "<":
		*d = DiffOpLT
		return nil
	case ">=":
		*d = DiffOpGE
		return nil
	case ">":
		*d = DiffOpGT
		return nil
	case "=":
		*d = OpEQ
		return nil
	case "distinct":
		*d = OpNE
		return nil
	default:
		return errors.New("invalid difference operation '" + value + "'")
	}
}

// NumberExpr represents either a positive or negative number. The grammar
// doesn't allow raw negative numbers, so they always have the form (- n).
type NumberExpr int64

func (n *NumberExpr) Capture(values []string) error {

	// We should only have one or four values, corresponding to a positive or
	// negative number respectively. Parse each case, determining what value to
	// parse and whether to negate.
	var numberString string
	var negate bool
	switch numValues := len(values); numValues {
	case 1:
		numberString = values[0]
		negate = false
	case 4:
		// Check that all the other tokens are what we expect
		if values[0] != "(" || values[1] != "-" || values[3] != ")" {
			panic("Malformed negative number")
		}
		// Otherwise, set.
		numberString = values[2]
		negate = true
	default:
		panic("Should have gotten one or four values")
	}

	// Try to parse the integer.
	number, err := strconv.ParseInt(numberString, 10, 64)
	if err != nil {
		// Check if we're actually out of range. If we are, that's a user error
		// and not a panic
		if err.(*strconv.NumError).Err == strconv.ErrRange {
			return errors.New("integer " + numberString + " is out-of-range")
		}
		// Otherwise, it's on us
		panic("Could not parse integer")
	}

	// Write and return.
	if negate {
		*n = NumberExpr(-number)
	} else {
		*n = NumberExpr(number)
	}
	return nil
}

// A DiffAtom represents the main building block of difference logic. It has two
// symbols and compares their difference to a constant. The comparison operator
// is given by a [DiffOp]. The symbols have to have sort Int, which is checked
// later.
type DiffAtom struct {
	Operation DiffOp     `parser:"'(':ParenOpen @Symbol '(':ParenOpen '-':Symbol"`
	LHS       Symbol     `parser:"@Symbol"`
	RHS       Symbol     `parser:"@Symbol ')':ParenClose"`
	Value     NumberExpr `parser:"@( NumberLit | '(':ParenOpen '-':Symbol NumberLit ')':ParenClose ) ')':ParenClose"`
	Pos       lexer.Position
}

func (a DiffAtom) formula() {}

// EqualityOp represents the different operations we can apply to equalities or
// disequalities of two symbols. They are a subset of [DiffOp], and they use the
// same constants.
type EqualityOp int

func (e EqualityOp) String() string {
	switch e {
	case OpEQ:
		return "="
	case OpNE:
		return "distinct"
	default:
		panic("Invalid equality operation")
	}
}

func (e *EqualityOp) Capture(values []string) error {
	// We should always get exactly one value, so panic if this doesn't happen
	if len(values) != 1 {
		panic("Should have gotten exactly one value")
	}
	// Switch on the value we got, and notify the user if they put something
	// invalid.
	switch value := values[0]; value {
	case "=":
		*e = OpEQ
		return nil
	case "distinct":
		*e = OpNE
		return nil
	default:
		return errors.New("invalid equality operation '" + value + "'")
	}
}

// An EqualityAtom represents an atom that asserts the equality or disequality
// between two symbols. The operation is given by an [EqualityOp]. These can
// apply to both Bool and Int arguments, and well-sortedness is checked later.
type EqualityAtom struct {
	Operation EqualityOp `parser:"'(':ParenOpen @( '=':Symbol | 'distinct':Symbol )"`
	LHS       Symbol     `parser:"@Symbol"`
	RHS       Symbol     `parser:"@Symbol ')':ParenClose"`
	Pos       lexer.Position
}

func (a EqualityAtom) formula() {}

// NotBuilder represents the formula building operator for boolean negation. It
// only takes one argument - the thing to negate.
type NotBuilder struct {
	Argument Formula `parser:"'(':ParenOpen 'not':Symbol @@ ')':ParenClose"`
}

// ITEBuilder is the formula building operator for if-then-else. It takes
// exactly three arguments because anything else doesn't really make sense.
type ITEBuilder struct {
	If   Formula `parser:"'(':ParenOpen 'ite':Symbol @@"`
	Then Formula `parser:"@@"`
	Else Formula `parser:"@@ ')':ParenClose"`
}

// EqualityBuilder represents a formula building operator that asserts the
// equality or disequality between some subformulas. This is distinct from
// [EqualityAtom] since that:
//   - Can only be between two symbols
//   - Can work on either integers or booleans
//
// We should always try to parse an [EqualityAtom] first, so that legal integer
// comparisons don't get rejected.
type EqualityBuilder struct {
	Operation   EqualityOp `parser:"'(':ParenOpen @( '=':Symbol | 'distinct':Symbol )"`
	Subformulas []Formula  `parser:"@@ @@+ ')':ParenClose"`
}

func (b NotBuilder) formula()      {}
func (b ITEBuilder) formula()      {}
func (b EqualityBuilder) formula() {}

// Formula building operator for let expressions. These consist of at least one
// [LetBinding], and well as the final formula to substitute them into.
type LetBuilder struct {
	Bindings   []LetBinding `parser:"'(':ParenOpen 'let':Symbol '(':ParenOpen @@+ ')':ParenClose"`
	Subformula Formula      `parser:"@@ ')':ParenClose"`
}

// A single binding for a [LetBuilder] expression. It has a name and what
// formula that is bound to.
type LetBinding struct {
	Name Symbol  `parser:"'(':ParenOpen @Symbol"`
	Bind Formula `parser:"@@ ')':ParenClose"`
}

func (b LetBuilder) formula() {}

// The BoolOp type represents the the associative boolean operations - i.e. all
// the operations we haven't covered so far. This is:
//   - Impliciation
//   - AND
//   - OR
//   - XOR
type BoolOp int

func (b BoolOp) String() string {
	switch b {
	case BoolOpIMP:
		return "=>"
	case BoolOpAND:
		return "and"
	case BoolOpOR:
		return "or"
	case BoolOpXOR:
		return "xor"
	default:
		panic("Invalid boolean operation")
	}
}

func (b *BoolOp) Capture(values []string) error {
	// We should always get exactly one value, so panic if this doesn't happen
	if len(values) != 1 {
		panic("Should have gotten exactly one value")
	}
	// Switch on the value we got, and notify the user if they put something
	// invalid.
	switch value := values[0]; value {
	case "=>":
		*b = BoolOpIMP
		return nil
	case "and":
		*b = BoolOpAND
		return nil
	case "or":
		*b = BoolOpOR
		return nil
	case "xor":
		*b = BoolOpXOR
		return nil
	default:
		return errors.New("invalid boolean operation '" + value + "'")
	}
}

// OperationBuilder is a formula building operator that uses [BoolOp] as the
// operation. All of the operations are associative, and they take at least two
// arguments.
type OperationBuilder struct {
	Operation   BoolOp    `parser:"'(':ParenOpen @Symbol"`
	Subformulas []Formula `parser:"@@ @@+ ')':ParenClose"`
}

func (b OperationBuilder) formula() {}