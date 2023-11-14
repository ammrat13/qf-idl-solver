package db

import (
	"errors"
	"fmt"
	"math/big"

	"github.com/alecthomas/participle/v2/lexer"
)

// An expr represents the possible values we can get after fully parsing a
// subexpression. These values can be:
//   - a constant with [exprConst]
//   - a variable with [exprVar]
//   - a difference of two variables with [exprDiff]
//   - a boolean literal with [exprLit]
type expr interface {
	expr()
}

//go-sumtype:decl expr

type exprConst struct {
	val *big.Int
}

type exprVar struct {
	vr VariableID
}

type exprDiff struct {
	x VariableID
	y VariableID
}

type exprLit struct {
	lit Lit
}

// The convertExpr function tries to convert an [expr] to one of its subtypes,
// specified by T. It returns an error if the conversion failed.
func convertExpr[T expr](e expr) (ret T, err error) {
	// Try to do the conversion
	ret, ok := e.(T)
	// Populate err if it failed
	if !ok {
		// Compute the error message based on the type. We have to use a hack to
		// figure out what the target type is.
		//
		// See: https://appliedgo.com/blog/a-tip-and-a-trick-when-working-with-generics
		var test T
		switch any(test).(type) {
		case exprConst:
			err = errors.New("expected constant")
		case exprVar:
			err = errors.New("expected variable")
		case exprDiff:
			err = errors.New("expected difference of two symbols")
		case exprLit:
			err = errors.New("expected Bool")
		}
	}
	return
}

// The convertExprAt function is a wrapper around [convertExpr], which adds
// location information to the error on failure.
func convertExprAt[T expr](e expr, pos lexer.Position) (ret T, err error) {
	// Do the normal convertion.
	ret, err = convertExpr[T](e)
	// If it failed, append location information.
	if err != nil {
		err = fmt.Errorf("%s at :%d:%d", err.Error(), pos.Line, pos.Column)
	}
	return
}

func (e exprConst) expr() {}
func (e exprVar) expr()   {}
func (e exprDiff) expr()  {}
func (e exprLit) expr()   {}

// A context stores all the names in scope at any given time, and what [expr]
// they map to. It also has a parent context, which is nil for the root.
type context struct {
	Names  map[string]expr
	Parent *context
}

// The AddName method associates a name with a value in the current context.
// It throws an error if the name has already been defined at the current level.
// It's fine if the name has been defined on previous levels - that's shadowing.
func (ctx *context) AddName(name string, value expr) error {
	// Check if the name is already in
	_, ok := ctx.Names[name]
	if ok {
		return fmt.Errorf("duplicate name '%s'", name)
	}
	// Otherwise, add it to the map
	ctx.Names[name] = value
	return nil
}

// The Lookup method looks up a name in the given context. It returns the
// value of that name, or an error if the name could not be found.
func (ctx context) Lookup(name string) (expr, error) {
	// Check to see if we know it.
	val, ok := ctx.Names[name]
	if ok {
		return val, nil
	}
	// Otherwise, check our parent.
	if ctx.Parent != nil {
		return ctx.Parent.Lookup(name)
	}
	// If we don't have a parent, that's an error.
	return exprLit{}, fmt.Errorf("unknown symbol '%s'", name)
}

// The LookupAt function is a wrapper around [Lookup] that adds position
// information to the error. If no error occurred, it is identical to [Lookup].
func (ctx context) LookupAt(name string, pos lexer.Position) (ret expr, err error) {
	// Do the normal lookup.
	ret, err = ctx.Lookup(name)
	// If it failed, append location information.
	if err != nil {
		err = fmt.Errorf("%s at :%d:%d", err.Error(), pos.Line, pos.Column)
	}
	// Done
	return
}
