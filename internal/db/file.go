package db

import (
	"fmt"
	"log"
	"math/big"

	"github.com/alecthomas/participle/v2/lexer"
	"github.com/ammrat13/qf-idl-solver/internal/file"
)

// The FromFile function ingests a parsed AST and outputs a database. In
// essence, this function applies Tsieten's transformation. It returns an error
// if the same scope defines the same variable twice, if we use an undeclared
// variable, or if we don't have well-sortedness.
func FromFile(ast file.File) (db DB, err error) {

	// Literals must be at least one to be valid CNF. Therefore, set the next
	// atom to start there.
	db.nextAtomID = 1

	// Create the root context in which symbol lookups will happen. Boolean
	// declarations get atom identifiers, and integer declarations get symbols.
	var ctx context
	ctx.names = make(map[string]parsedExpr)
	ctx.parent = nil
	for _, decl := range ast.Declarations {
		name := string(decl.Name)
		switch decl.Sort {
		case file.SortBool:
			// Create a new atom for the symbol, and add it to the context.
			atm := db.getNewAtom()
			ctx.addName(name, litExpr{lit: atm.Positive()})
			log.Printf("Assigned %s as %d\n", name, atm.Positive())
		case file.SortInt:
			// Just add it to the context.
			ctx.addName(name, symExpr{name: name})
		default:
			panic("Invalid sort")
		}
	}

	// Process each of the assertions. If we get an error, die.
	for _, ass := range ast.Assertions {
		var valExpr parsedExpr
		valExpr, err = db.processExpr(ass, ctx)
		if err != nil {
			return
		}
		// The value we get should be a literal
		var valLit litExpr
		valLit, err = convertAt[litExpr](valExpr, ass.Position())
		if err != nil {
			return
		}
		// If it was, add it to the list of constraints
		db.clauses = append(db.clauses, []AtomLit{valLit.lit})
	}

	return
}

// The processExpr function processes a single expression, updating the state of
// the database with its constraints. It returns what the expression ultimately
// evaluates to, along with any errors.
func (db *DB) processExpr(ex file.Expr, ctx context) (ret parsedExpr, err error) {

	log.Printf("Processing %v\n", ex)

	// Break into cases on what the expression actually is
	switch expr := ex.(type) {

	case file.NumberAtom:
		log.Println("Got NumberAtom")
		// If it's a raw number, just return it
		ret, err = constExpr{value: expr.Num.Value}, nil
		return

	case file.SymbolAtom:
		log.Println("Got SymbolAtom")
		// If it's a symbol, look it up and return it. Error if not found.
		ret, err = ctx.lookupAt(string(expr.Name), expr.Position())
		return

	case file.DiffAtom:
		log.Println("Got DiffAtom")
		var exprX, exprY parsedExpr
		var symX, symY symExpr
		nameX := string(expr.LHS)
		nameY := string(expr.RHS)
		// Lookup the LHS
		exprX, err = ctx.lookupAt(nameX, expr.Position())
		if err != nil {
			return
		}
		symX, err = convertAt[symExpr](exprX, expr.Position())
		if err != nil {
			return
		}
		// Lookup the RHS
		exprY, err = ctx.lookupAt(nameY, expr.Position())
		if err != nil {
			return
		}
		symY, err = convertAt[symExpr](exprY, expr.Position())
		if err != nil {
			return
		}
		// Return with those symbol names
		return diffExpr{x: symX.name, y: symY.name}, nil

	case file.NotBuilder:
		log.Println("Got NotBuilder")
		var exprA parsedExpr
		var litA litExpr
		// Recursively process the argument, and check that it is the correct
		// type.
		exprA, err = db.processExpr(expr.Argument, ctx)
		if err != nil {
			return
		}
		litA, err = convertAt[litExpr](exprA, expr.Position())
		if err != nil {
			return
		}
		// Return the negation.
		return litExpr{lit: -litA.lit}, nil

	case file.ITEBuilder:
		log.Println("Got ITEBuilder")
		var exprI, exprT, exprE parsedExpr
		var litI, litT, litE litExpr
		// For each argument, process it and assert that it is a literal.
		exprI, err = db.processExpr(expr.If, ctx)
		if err != nil {
			return
		}
		litI, err = convertAt[litExpr](exprI, expr.If.Position())
		if err != nil {
			return
		}
		exprT, err = db.processExpr(expr.Then, ctx)
		if err != nil {
			return
		}
		litT, err = convertAt[litExpr](exprT, expr.Then.Position())
		if err != nil {
			return
		}
		exprE, err = db.processExpr(expr.Else, ctx)
		if err != nil {
			return
		}
		litE, err = convertAt[litExpr](exprE, expr.Else.Position())
		if err != nil {
			return
		}
		// Create a new atom that we will return, then install it in clauses
		// that execute the if-then-else.
		retAtom := db.getNewAtom()
		db.clauses = append(
			db.clauses,
			[]AtomLit{-litI.lit, -litT.lit, retAtom.Positive()},
			[]AtomLit{-litI.lit, litT.lit, retAtom.Negative()},
			[]AtomLit{litI.lit, -litE.lit, retAtom.Positive()},
			[]AtomLit{litI.lit, litE.lit, retAtom.Negative()},
		)
		return litExpr{lit: retAtom.Positive()}, nil
	}

	panic("Unhandled case")
}

// A parsedExpr represents the possible values we can get after fully parsing a
// subexpression. These values can be:
//   - a constant with [constExpr]
//   - a symbol with [symExpr]
//   - a difference of two symbols with [diffExpr]
//   - a boolean atom with [atomExpr]
type parsedExpr interface {
	parsedExpr()
}

//go-sumtype:decl parsedExpr

type constExpr struct {
	value *big.Int
}

type symExpr struct {
	name string
}

type diffExpr struct {
	x string
	y string
}

type litExpr struct {
	lit AtomLit
}

func convertAt[T parsedExpr](expr parsedExpr, pos lexer.Position) (ret T, err error) {
	// Try to do the conversion
	ret, ok := expr.(T)
	// Populate err if it failed
	if !ok {
		// Compute the error message based on the type. We have to use a hack to
		// figure out what the target type is.
		//
		// See: https://appliedgo.com/blog/a-tip-and-a-trick-when-working-with-generics
		var test T
		var msg string
		switch any(test).(type) {
		case constExpr:
			msg = "expected constant"
		case symExpr:
			msg = "expected symbol"
		case diffExpr:
			msg = "expected difference of two symbols"
		case litExpr:
			msg = "expected Bool"
		}
		// Set the error
		err = fmt.Errorf("%s at :%d:%d", msg, pos.Line, pos.Column)
	}
	return
}

func (e constExpr) parsedExpr() {}
func (e symExpr) parsedExpr()   {}
func (e diffExpr) parsedExpr()  {}
func (e litExpr) parsedExpr()   {}

// A context stores all the names in scope at any given time, and what
// expressions they map to. It also has a parent context, which is nil for the
// root.
type context struct {
	names  map[string]parsedExpr
	parent *context
}

// The addName function associates a name with a value in the current context.
// It throws an error if the name has already been defined at the current level.
// It's fine if the name has been defined on previous levels - that's shadowing.
func (ctx *context) addName(name string, value parsedExpr) error {
	// Check if the name is already in
	_, ok := ctx.names[name]
	if ok {
		return fmt.Errorf("duplicate name '%s'", name)
	}
	// Otherwise, add it to the map
	ctx.names[name] = value
	return nil
}

// The lookup method looks up a name in the given context. It returns the
// value of that name, or an error if the name could not be found.
func (ctx context) lookup(name string) (parsedExpr, error) {
	// Check to see if we know it
	val, ok := ctx.names[name]
	if ok {
		return val, nil
	}
	// Otherwise, check our parent.
	if ctx.parent != nil {
		return ctx.parent.lookup(name)
	}
	// If we don't have a parent, that's an error
	return symExpr{}, fmt.Errorf("unknown symbol '%s'", name)
}

// The lookupAt function is a wrapper around [lookup] that adds position
// information to the error.
func (ctx context) lookupAt(name string, pos lexer.Position) (ret parsedExpr, err error) {
	// Do the normal lookup
	ret, err = ctx.lookup(name)
	// If it failed, append location information
	if err != nil {
		err = fmt.Errorf(
			"%s at :%d:%d",
			err.Error(),
			pos.Line,
			pos.Column,
		)
	}
	// Done
	return
}
