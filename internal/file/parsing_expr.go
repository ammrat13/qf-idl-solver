package file

import (
	"errors"
	"math/big"

	"github.com/alecthomas/participle/v2/lexer"
)

// Enumeration constants for [EquOp], [CmpOp], and [BoolOp]. Not all the
// operations are present since some of them are handled with custom parse
// rules.
const (
	EquOpEQ = iota
	EquOpNE
	CmpOpLE
	CmpOpLT
	CmpOpGE
	CmpOpGT
	BoolOpIMP
	BoolOpAND
	BoolOpOR
	BoolOpXOR
)

// An EquOp represents the different operations we can apply to equalities or
// disequalities of two symbols. That is:
//   - Equals
//   - Distinct
type EquOp int

func (e EquOp) String() string {
	switch e {
	case EquOpEQ:
		return "="
	case EquOpNE:
		return "distinct"
	default:
		panic("Invalid equality operation")
	}
}

func (e *EquOp) Capture(values []string) error {
	// We should always get exactly one value, so panic if this doesn't happen
	if len(values) != 1 {
		panic("Should have gotten exactly one value")
	}
	// Switch on the value we got, and notify the user if they put something
	// invalid.
	switch value := values[0]; value {
	case "=":
		*e = EquOpEQ
	case "distinct":
		*e = EquOpNE
	default:
		return errors.New("invalid equality operation '" + value + "'")
	}
	return nil
}

// CmpOp represents the different operations we can apply to difference atoms.
// Recall that difference atoms are of the form (op (- x y) n). However, it does
// not include equality operations. Those are handled separately.
type CmpOp int

func (c CmpOp) String() string {
	switch c {
	case CmpOpLE:
		return "<="
	case CmpOpLT:
		return "<"
	case CmpOpGE:
		return ">="
	case CmpOpGT:
		return ">"
	default:
		panic("Invalid comparison operation")
	}
}

func (c *CmpOp) Capture(values []string) error {
	// We should always get exactly one value, so panic if this doesn't happen
	if len(values) != 1 {
		panic("Should have gotten exactly one value")
	}
	// Switch on the value we got, and notify the user if they put something
	// invalid.
	switch value := values[0]; value {
	case "<=":
		*c = CmpOpLE
	case "<":
		*c = CmpOpLT
	case ">=":
		*c = CmpOpGE
	case ">":
		*c = CmpOpGT
	default:
		return errors.New("invalid difference operation '" + value + "'")
	}
	return nil
}

// The BoolOp type represents the the associative boolean operations. That is:
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
	case "and":
		*b = BoolOpAND
	case "or":
		*b = BoolOpOR
	case "xor":
		*b = BoolOpXOR
	default:
		return errors.New("invalid boolean operation '" + value + "'")
	}
	return nil
}

// Number represents either a positive or negative number. It's wrapped by a
// [NumberAtom].
type Number struct {
	Value *big.Int
}

func (n *Number) Capture(values []string) error {

	// We should only have two or four values, corresponding to a positive or
	// negative number respectively. Parse each case, determining what value to
	// parse and whether to negate.
	var nStr string
	var neg bool
	switch numValues := len(values); numValues {
	case 1:
		nStr = values[0]
		neg = false
	case 2:
		// Check that all the other tokens are what we expect
		if values[0] != "-" {
			panic("Malformed negative number")
		}
		// Otherwise, set.
		nStr = values[1]
		neg = true
	default:
		panic("Should have gotten one or two values")
	}

	// Try to parse the integer.
	nInt, success := new(big.Int).SetString(nStr, 10)
	if !success {
		panic("Couldn't parse integer '" + nStr + "'")
	}

	// Write and return.
	if neg {
		nInt.Mul(nInt, new(big.Int).SetInt64(-1))
	}
	n.Value = nInt
	return nil
}

// The Expr interface expresses the set of expressions we will attempt to parse.
// Ideally, this approximates the set of well-formed-formulas in QF_IDL.
type Expr interface {
	// The Position method returns the starting position of this expression.
	Position() lexer.Position
	expr()
}

//go-sumtype:decl Expr

// The DiffExpr interface represents a difference expression - an expression of
// the form (- x y). It also includes symbols because of let bindings.
type DiffExpr interface {
	Position() lexer.Position
	diffExpr()
}

//go-sumtype:decl DiffExpr

// NotBuilder represents the formula building operator for boolean negation. It
// only takes one argument - the thing to negate.
type NotBuilder struct {
	Argument Expr `parser:"'(':ParenOpen 'not':Symbol @@ ')':ParenClose"`
	Pos      lexer.Position
}

// ITEBuilder is the formula building operator for if-then-else. It takes
// exactly three arguments because anything else doesn't really make sense.
type ITEBuilder struct {
	If   Expr `parser:"'(':ParenOpen 'ite':Symbol @@"`
	Then Expr `parser:"@@"`
	Else Expr `parser:"@@ ')':ParenClose"`
	Pos  lexer.Position
}

// EquOpBuilder represents the formula building operators for equalities and
// disequalities. That is, it wraps an [EquOp] and its arguments, of which there
// are at least two.
//
// This is very similar in structure to [BoolOpBuilder], but it has different
// semantics, so we separate it in the grammar. For example, it has to deal with
// both boolean arguments and difference arguments.
type EquOpBuilder struct {
	Operation EquOp  `parser:"'(':ParenOpen @( '=':Symbol | 'distinct':Symbol )"`
	Arguments []Expr `parser:"@@ @@+ ')':ParenClose"`
	Pos       lexer.Position
}

// BoolOpBuilder represents all of the formula building operators for
// associative boolean operations. It wraps a [BoolOp] and its arguments, of
// which there are at least two.
type BoolOpBuilder struct {
	Operation BoolOp `parser:"'(':ParenOpen @( '=>':Symbol | 'and':Symbol | 'or':Symbol | 'xor':Symbol )"`
	Arguments []Expr `parser:"@@ @@+ ')':ParenClose"`
	Pos       lexer.Position
}

func (b NotBuilder) Position() lexer.Position    { return b.Pos }
func (b ITEBuilder) Position() lexer.Position    { return b.Pos }
func (b EquOpBuilder) Position() lexer.Position  { return b.Pos }
func (b BoolOpBuilder) Position() lexer.Position { return b.Pos }
func (b NotBuilder) expr()                       {}
func (b ITEBuilder) expr()                       {}
func (b EquOpBuilder) expr()                     {}
func (b BoolOpBuilder) expr()                    {}

type CmpOpBuilder struct {
	Operation CmpOp        `parser:"'(':ParenOpen @( '<=':Symbol | '<':Symbol | '>=':Symbol | '>':Symbol )"`
	Arguments CmpArguments `parser:"@@ ')':ParenClose"`
	Pos       lexer.Position
}

type CmpArguments interface {
	cmpArguments()
}

type CmpDiff struct {
	Difference DiffExpr   `parser:"@@"`
	Constant   NumberAtom `parser:"@@"`
}

type CmpSym struct {
	LHS Symbol `parser:"@Symbol"`
	RHS Symbol `parser:"@Symbol"`
}

//go-sumtype:decl CmpArguments

func (b CmpOpBuilder) Position() lexer.Position { return b.Pos }
func (b CmpOpBuilder) expr()                    {}
func (a CmpDiff) cmpArguments()                 {}
func (a CmpSym) cmpArguments()                  {}

// Formula building operator for let expressions. These consist of at least one
// [LetBinding], and well as the final formula to substitute them into.
type LetBuilder struct {
	Bindings []LetBinding `parser:"'(':ParenOpen 'let':Symbol '(':ParenOpen @@+ ')':ParenClose"`
	Expr     Expr         `parser:"@@ ')':ParenClose"`
	Pos      lexer.Position
}

// A single binding for a [LetBuilder] expression. It has a name and what
// formula that is bound to.
type LetBinding struct {
	Name Symbol `parser:"'(':ParenOpen @Symbol"`
	Bind Expr   `parser:"@@ ')':ParenClose"`
	Pos  lexer.Position
}

func (b LetBuilder) Position() lexer.Position { return b.Pos }
func (b LetBuilder) expr()                    {}

// A DiffAtom represents the difference of two symbols. Both of these symbols
// should have sort Int, but we'll check this later.
type DiffAtom struct {
	LHS Symbol `parser:"'(':ParenOpen '-':Symbol @Symbol"`
	RHS Symbol `parser:"@Symbol ')':ParenClose"`
	Pos lexer.Position
}

func (a DiffAtom) Position() lexer.Position { return a.Pos }
func (a DiffAtom) expr()                    {}
func (a DiffAtom) diffExpr()                {}

// SymbolAtom represents a bare symbol. It can sort Bool or Int, depending on
// context.
type SymbolAtom struct {
	Name Symbol `parser:"@Symbol"`
	Pos  lexer.Position
}

func (a SymbolAtom) Position() lexer.Position { return a.Pos }
func (a SymbolAtom) expr()                    {}
func (a SymbolAtom) diffExpr()                {}

// NumberAtom represents either a numeral or its negation. Remember that the
// grammar has no support for negative numbers, so they are built with the
// negation operator.
type NumberAtom struct {
	Num Number `parser:"( @NumberLit | '(':ParenOpen @( '-':Symbol NumberLit ) ')':ParenClose )"`
	Pos lexer.Position
}

func (a NumberAtom) Position() lexer.Position { return a.Pos }
func (a NumberAtom) expr()                    {}
