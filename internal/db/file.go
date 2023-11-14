package db

import (
	"log"

	"github.com/ammrat13/qf-idl-solver/internal/file"
	"github.com/go-air/gini"
)

// The FromFile function ingests an AST and outputs a [DB] corresponding to it.
// In essence, this function applies Tsieten's transformation. It returns an
// error if the same scope defines the same variable twice, if we use an
// undeclared variable, or if we don't have well-sortedness.
func FromFile(ast file.File) (db DB, err error) {

	// Create the solver.
	db.Clauses = gini.New()

	// Setup counters for atoms and variables.
	db.NextAtom = 1
	db.NextVariable = 0

	// Create the root context for symbol lookups.
	var ctx context
	ctx.Names = make(map[string]expr)
	ctx.Parent = nil
	// Add true and false to the root context.
	err = ctx.AddName("true", exprLit{lit: db.NewAtom()})
	if err != nil {
		panic("Couldn't add true")
	}
	err = ctx.AddName("false", exprLit{lit: -db.NewAtom()})
	if err != nil {
		panic("Couldn't add false")
	}
	// Add all the other declarations. Add literals for booleans and variables
	// for integers.
	for _, decl := range ast.Declarations {
		name := string(decl.Name)
		switch decl.Sort {
		case file.SortBool:
			// Create a new atom for the symbol, and add it to the context.
			lit := db.NewAtom()
			err = ctx.AddName(name, exprLit{lit: lit})
			if err != nil {
				return
			}
			log.Printf("Associated %s : Bool with %d\n", name, lit)
		case file.SortInt:
			// Create a new variable for the symbol, and add it to the context.
			vr := db.NewVariable()
			err = ctx.AddName(name, exprVar{vr: vr})
			if err != nil {
				return
			}
			log.Printf("Associated %s : Int with %d\n", name, vr)
		default:
			panic("Invalid sort")
		}
	}

	// Process each of the assertions. If we get an error, die.
	for _, ass := range ast.Assertions {
		var e expr
		var l exprLit
		// Process the expression to get its "value".
		e, err = db.processExpr(ass, ctx)
		if err != nil {
			return
		}
		// Check that we ultimately got a literal.
		l, err = convertExprAt[exprLit](e, ass.Position())
		if err != nil {
			return
		}
		// Add the literal to the list of clauses.
		db.AddClauses([]Lit{l.lit})
	}

	return
}

// The processExpr function processes a single expression, updating the state of
// the database with its constraints. It returns what the expression ultimately
// evaluates to, or an error if it couldn't be evaluated.
func (db *DB) processExpr(e file.Expr, ctx context) (ret expr, err error) {
	// Print debug information if enabled.
	log.Printf("Processing: %v", e)
	defer func() { log.Printf("Got: %v", ret) }()

	// Break into cases depending on what the expression actually is. We handle
	// atoms inline, and handle builders in separate functions.
	switch ex := e.(type) {

	case file.NumberAtom:
		// If it's a raw number, just return it
		return exprConst{val: ex.Num.Value}, nil

	case file.SymbolAtom:
		// If it's a symbol, look it up and return it. Error if we can't find
		// it.
		ret, err = ctx.LookupAt(string(ex.Name), e.Position())
		return

	case file.DiffAtom:
		var eX, eY expr
		var vX, vY exprVar
		nameX := string(ex.LHS)
		nameY := string(ex.RHS)

		// Lookup the LHS and check that it is a variable.
		eX, err = ctx.LookupAt(nameX, e.Position())
		if err != nil {
			return
		}
		vX, err = convertExprAt[exprVar](eX, e.Position())
		if err != nil {
			return
		}
		// Do the same for the RHS.
		eY, err = ctx.LookupAt(nameY, e.Position())
		if err != nil {
			return
		}
		vY, err = convertExprAt[exprVar](eY, e.Position())
		if err != nil {
			return
		}

		// Return using those variables
		return exprDiff{x: vX.vr, y: vY.vr}, nil

	case file.NotBuilder:
		return db.processExprNotBuilder(ex, ctx)

	case file.ITEBuilder:
		return db.processExprITEBuilder(ex, ctx)

	}

	panic("Unhandled case")
}

func (db *DB) processExprNotBuilder(e file.NotBuilder, ctx context) (ret expr, err error) {
	var eA expr
	var lA exprLit
	// Recursively process the argument, and check that it is the correct
	// type.
	eA, err = db.processExpr(e.Argument, ctx)
	if err != nil {
		return
	}
	lA, err = convertExprAt[exprLit](eA, e.Position())
	if err != nil {
		return
	}
	// Return the negation.
	return exprLit{lit: -lA.lit}, nil
}

func (db *DB) processExprITEBuilder(e file.ITEBuilder, ctx context) (ret expr, err error) {
	var eI, eT, eE expr
	var lI, lT, lE exprLit
	// For each argument, process it and assert that it is a literal.
	eI, err = db.processExpr(e.If, ctx)
	if err != nil {
		return
	}
	lI, err = convertExprAt[exprLit](eI, e.If.Position())
	if err != nil {
		return
	}
	eT, err = db.processExpr(e.Then, ctx)
	if err != nil {
		return
	}
	lT, err = convertExprAt[exprLit](eT, e.Then.Position())
	if err != nil {
		return
	}
	eE, err = db.processExpr(e.Else, ctx)
	if err != nil {
		return
	}
	lE, err = convertExprAt[exprLit](eE, e.Else.Position())
	if err != nil {
		return
	}
	// Create a new atom that we will return, then install it in clauses
	// that execute the if-then-else.
	lit := db.NewAtom()
	db.AddClauses(
		[]Lit{-lI.lit, -lT.lit, lit},
		[]Lit{-lI.lit, lT.lit, -lit},
		[]Lit{lI.lit, -lE.lit, lit},
		[]Lit{lI.lit, lE.lit, -lit},
	)
	return exprLit{lit: lit}, nil
}
