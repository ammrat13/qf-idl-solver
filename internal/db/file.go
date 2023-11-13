package db

import (
	"fmt"
	"math/big"

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
	ctx := new(context)
	for _, decl := range ast.Declarations {
		name := string(decl.Name)
		switch decl.Sort {
		case file.SortBool:
			// Create a new atom for the symbol
			atm := db.getNewAtom()
			// Add it to the context
			ctx.addName(name, atomExpr{id: atm})
		case file.SortInt:
			// Just add it to the context
			ctx.addName(name, symExpr{name: name})
		default:
			panic("Invalid sort")
		}
	}

	// Process each of the assertions. If we get an error, die.
	for _, ass := range ast.Assertions {
		var valExpr parsedExpr
		valExpr, err = db.processExpr(ass)
		if err != nil {
			return
		}
		// The value we get should be an atom
		valAtm, ok := valExpr.(atomExpr)
		if !ok {
			err = fmt.Errorf(
				"sortedness error at :%d:%d: expected Bool",
				ass.Position().Line,
				ass.Position().Column,
			)
			return
		}
		// If it was, add it to the list of constraints
		db.clauses = append(db.clauses, []AtomLit{valAtm.id.Positive()})
	}

	return
}

// The processExpr function processes a single expression, updating the state of
// the database with its constraints. It returns what the expression ultimately
// evaluates to, along with any errors.
func (db *DB) processExpr(file.Expr) (ret parsedExpr, err error) {
	return atomExpr{}, nil
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

type atomExpr struct {
	id AtomID
}

func (e constExpr) parsedExpr() {}
func (e symExpr) parsedExpr()   {}
func (e diffExpr) parsedExpr()  {}
func (e atomExpr) parsedExpr()  {}

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
