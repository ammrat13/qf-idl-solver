package db

import (
	"fmt"
	"math/big"
	"slices"

	"github.com/alecthomas/participle/v2/lexer"
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
	// Create the maps.
	db.AtomID2Diff = make(map[AtomID]*DifferenceConstraint)
	db.Variables2AtomIDs = make(map[VariablePair][]AtomID)

	// Setup counters for atoms and variables.
	db.NextAtom = 1
	db.NextVariable = 0

	// Create the root context for symbol lookups.
	var ctx context
	ctx.Names = make(map[string]expr)
	ctx.Parent = nil
	// Add true and false to the root context.
	tt := exprLit{Lit: db.newAtom()}
	ff := exprLit{Lit: db.newAtom()}
	err = ctx.AddName("true", tt)
	if err != nil {
		panic("Couldn't add true")
	}
	err = ctx.AddName("false", ff)
	if err != nil {
		panic("Couldn't add false")
	}
	// Assert true and false
	db.AddClauses(
		[]Lit{tt.Lit},
		[]Lit{-ff.Lit},
	)

	// Add all the other declarations. Add literals for booleans and variables
	// for integers.
	for _, decl := range ast.Declarations {
		name := string(decl.Name)
		switch decl.Sort {
		case file.SortBool:
			// Create a new atom for the symbol, and add it to the context.
			l := db.newAtom()
			err = ctx.AddName(name, exprLit{Lit: l})
			if err != nil {
				return
			}
		case file.SortInt:
			// Create a new variable for the symbol, and add it to the context.
			v := db.newVariable()
			err = ctx.AddName(name, exprVar{Var: v})
			if err != nil {
				return
			}
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
		db.AddClauses([]Lit{l.Lit})
	}

	// Finally, sort each of the lists in the Variables2AtomIDs map. We make
	// this guarantee so that the solver can be more efficient.
	for _, atoms := range db.Variables2AtomIDs {
		slices.SortStableFunc[[]AtomID, AtomID](atoms, func(a AtomID, b AtomID) int {
			var ok bool
			// Lookup difference constraints for atoms
			ad, ok := db.AtomID2Diff[a]
			if !ok {
				panic("Atom not in AtomID2Diff")
			}
			bd, ok := db.AtomID2Diff[b]
			if !ok {
				panic("Atom not in AtomID2Diff")
			}
			// Return the comparison of the constants
			return ad.K.Cmp(bd.K)
		})
	}

	return
}

// The processExpr function processes a single expression, updating the state of
// the database with its constraints. It returns what the expression ultimately
// evaluates to, or an error if it couldn't be evaluated.
func (db *DB) processExpr(e file.Expr, ctx context) (ret expr, err error) {

	// Break into cases depending on what the expression actually is. We handle
	// atoms inline, and handle builders in separate functions.
	switch ex := e.(type) {

	case file.NumberAtom:
		// If it's a raw number, just return it
		return exprConst{Val: ex.Num.Value}, nil

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
		return exprDiff{X: vX.Var, Y: vY.Var}, nil

	case file.NotBuilder:
		return db.processNot(ex, ctx)

	case file.ITEBuilder:
		return db.processITE(ex, ctx)

	case file.EquOpBuilder:

		// Process the first argument.
		var a0 expr
		a0, err = db.processExpr(ex.Arguments[0], ctx)
		if err != nil {
			return
		}

		// Look at the first argument's type to determine what kind of equality
		// expression this is.
		switch a0.(type) {
		case exprLit:
			return db.processBoolEquOp(ex, ctx)
		case exprDiff:
			return db.processIntEquOp(ex, a0, ctx)
		case exprVar:
			return db.processIntEquOp(ex, a0, ctx)
		case exprConst:
			err = fmt.Errorf(
				"didn't expect constant at :%d:%d",
				ex.Arguments[0].Position().Line,
				ex.Arguments[0].Position().Column,
			)
			return
		}

	case file.BoolOpBuilder:
		return db.processBoolOp(ex, ctx)

	case file.CmpOpBuilder:
		return db.processCmpOp(ex, ctx)

	case file.LetBuilder:
		return db.processLet(ex, ctx)

	}

	panic("Unhandled case")
}

func (db *DB) processNot(e file.NotBuilder, ctx context) (ret exprLit, err error) {
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
	return exprLit{Lit: -lA.Lit}, nil
}

func (db *DB) processITE(e file.ITEBuilder, ctx context) (ret exprLit, err error) {
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
	ret = exprLit{Lit: db.newAtom()}
	db.AddClauses(
		[]Lit{-lI.Lit, -lT.Lit, ret.Lit},
		[]Lit{-lI.Lit, lT.Lit, -ret.Lit},
		[]Lit{lI.Lit, -lE.Lit, ret.Lit},
		[]Lit{lI.Lit, lE.Lit, -ret.Lit},
	)
	return
}

func (db *DB) processBoolOp(e file.BoolOpBuilder, ctx context) (ret exprLit, err error) {

	// Get the arguments, of which we should always have at least two.
	lArgs := make([]exprLit, len(e.Arguments))
	n := len(lArgs)
	if n < 2 {
		panic("Not enough arguments to boolean operation")
	}

	// Iterate over each of the arguments, and convert them into a literal.
	for i, arg := range e.Arguments {
		var eA expr
		var lA exprLit
		// Recursively process the argument.
		eA, err = db.processExpr(arg, ctx)
		if err != nil {
			return
		}
		lA, err = convertExprAt[exprLit](eA, arg.Position())
		if err != nil {
			return
		}
		// Set the literal
		lArgs[i] = lA
	}

	// Decide what to do based on the operation.
	switch e.Operation {

	case file.BoolOpIMP:
		// For implication, the output is false iff all of the premises are true
		// and the conclusion is false. We can treat this very similarly to an
		// AND.
		ret = exprLit{Lit: db.newAtom()}

		// Forward direction
		forward := make([]Lit, n+1)
		for iP := 0; iP < n-1; iP++ {
			forward[iP] = -lArgs[iP].Lit
		}
		forward[n-1] = lArgs[n-1].Lit
		forward[n] = -ret.Lit
		db.AddClauses(forward)

		// Reverse direction
		for iP := 0; iP < n-1; iP++ {
			db.AddClauses([]Lit{lArgs[iP].Lit, ret.Lit})
		}
		db.AddClauses([]Lit{-lArgs[n-1].Lit, ret.Lit})

	case file.BoolOpAND:
		// For the forward direction, only if all of the literals are true do
		// we get the output to be true. For the reverse direction, we can set
		// all of the input literals to true if the output is true.
		ret = exprLit{Lit: db.newAtom()}

		// Forward direction
		forward := make([]Lit, n+1)
		for i, lA := range lArgs {
			forward[i] = -lA.Lit
		}
		forward[n] = ret.Lit
		db.AddClauses(forward)

		// Reverse direction
		for _, lA := range lArgs {
			db.AddClauses([]Lit{lA.Lit, -ret.Lit})
		}

	case file.BoolOpOR:
		// The OR operation is the "reverse" of AND. If any of the inputs are
		// true we can set the output, but if the output is true we can only
		// conclude one of the inputs was true.
		ret = exprLit{Lit: db.newAtom()}

		// Forward direction
		for _, lA := range lArgs {
			db.AddClauses([]Lit{-lA.Lit, ret.Lit})
		}

		// Reverse direction
		reverse := make([]Lit, n+1)
		for i, lA := range lArgs {
			reverse[i] = lA.Lit
		}
		reverse[n] = -ret.Lit
		db.AddClauses(reverse)

	case file.BoolOpXOR:
		// For XOR, it seems the best thing to do is to fold. We create
		// intermediate atoms for the XOR of the first i terms, and then we
		// assert that the return is equal to that.

		cur := lArgs[0]
		for i := 1; i < n; i++ {
			next := lArgs[i]
			// Create a new variable and set it equal to cur XOR next.
			new := exprLit{Lit: db.newAtom()}
			db.AddClauses(
				[]Lit{cur.Lit, next.Lit, -new.Lit},
				[]Lit{cur.Lit, -next.Lit, new.Lit},
				[]Lit{-cur.Lit, next.Lit, new.Lit},
				[]Lit{-cur.Lit, -next.Lit, -new.Lit},
			)
			// Go to the next iteration.
			cur = new
		}
		// Return
		ret = cur

	default:
		panic("Invalid boolean operation")
	}
	return
}

func (db *DB) processCmpOp(e file.CmpOpBuilder, ctx context) (ret exprLit, err error) {
	// Break into cases on the type of argument
	switch arg := e.Arguments.(type) {

	case file.CmpSym:
		// If the comparison is between two symbols, we know it means their
		// subtraction and zero.
		return db.handleLookupCmp(
			e.Operation,
			string(arg.LHS),
			string(arg.RHS),
			big.NewInt(0),
			ctx,
			e.Position(),
		)

	case file.CmpDiff:
		// Otherwise, see what we got for the difference expression.
		switch diff := arg.Difference.(type) {
		case file.DiffAtom:
			// If its a difference atom, we can go on.
			return db.handleLookupCmp(
				e.Operation,
				string(diff.LHS),
				string(diff.RHS),
				arg.Constant.Num.Value,
				ctx,
				e.Position(),
			)
		case file.SymbolAtom:
			// If its a symbol, we have to look it up.
			var eD expr
			var dD exprDiff
			eD, err = ctx.LookupAt(string(diff.Name), diff.Position())
			if err != nil {
				return
			}
			dD, err = convertExprAt[exprDiff](eD, diff.Position())
			if err != nil {
				return
			}
			// Then we can handle the comparison normally
			return db.handleCmp(
				e.Operation,
				dD.X,
				dD.Y,
				arg.Constant.Num.Value,
			), nil
		}
	}

	panic("Unhandled case")
}

func (db *DB) handleLookupCmp(op file.CmpOp, nX, nY string, k *big.Int, ctx context, pos lexer.Position) (ret exprLit, err error) {
	var eX, eY expr
	var vX, vY exprVar

	// Lookup x and y before passing it to handleCmp
	eX, err = ctx.LookupAt(nX, pos)
	if err != nil {
		return
	}
	vX, err = convertExprAt[exprVar](eX, pos)
	if err != nil {
		return
	}
	eY, err = ctx.LookupAt(nY, pos)
	if err != nil {
		return
	}
	vY, err = convertExprAt[exprVar](eY, pos)
	if err != nil {
		return
	}

	// Pass it off
	return db.handleCmp(op, vX.Var, vY.Var, k), nil
}

func (db *DB) handleCmp(op file.CmpOp, x, y VariableID, k *big.Int) (ret exprLit) {

	// Normalize to <=
	if op != file.CmpOpLE {
		switch op {
		case file.CmpOpGE:
			return db.handleCmp(file.CmpOpLE, y, x, new(big.Int).Neg(k))
		case file.CmpOpLT:
			ret = db.handleCmp(file.CmpOpGE, x, y, k)
			ret.Lit = -ret.Lit
			return
		case file.CmpOpGT:
			ret = db.handleCmp(file.CmpOpLE, x, y, k)
			ret.Lit = -ret.Lit
			return
		default:
			panic("Invalid comparison operation")
		}
	}

	// Return the atom via lookup.
	return exprLit{Lit: db.makeAtomForDiff(DifferenceConstraint{X: x, Y: y, K: k})}
}

func (db *DB) processBoolEquOp(e file.EquOpBuilder, ctx context) (ret exprLit, err error) {

	// Get the arguments, of which we should always have at least two.
	lArgs := make([]exprLit, len(e.Arguments))
	n := len(lArgs)
	if n < 2 {
		panic("Not enough arguments to boolean operation")
	}

	// Iterate over each of the arguments, and convert them into a literal.
	for i, arg := range e.Arguments {
		var eA expr
		var lA exprLit
		// Recursively process the argument.
		eA, err = db.processExpr(arg, ctx)
		if err != nil {
			return
		}
		lA, err = convertExprAt[exprLit](eA, arg.Position())
		if err != nil {
			if i == 0 {
				panic("Should've checked first argument")
			}
			return
		}
		// Set the literal
		lArgs[i] = lA
	}

	// Decide what to do based on the operation.
	switch e.Operation {

	case file.EquOpEQ:
		// For boolean equality, fold over all of the terms. Initialize by
		// setting to whether the first two terms are equal, then continue from
		// there. Remember, we have at least two terms.

		// First two terms
		ret = exprLit{Lit: db.newAtom()}
		l0 := lArgs[0]
		l1 := lArgs[1]
		db.AddClauses(
			[]Lit{l0.Lit, l1.Lit, ret.Lit},
			[]Lit{l0.Lit, -l1.Lit, -ret.Lit},
			[]Lit{-l0.Lit, l1.Lit, -ret.Lit},
			[]Lit{-l0.Lit, -l1.Lit, ret.Lit},
		)

		// Fold
		for i := 1; i < n-1; i++ {
			next := exprLit{Lit: db.newAtom()}
			li := lArgs[i]
			lj := lArgs[i+1]
			db.AddClauses(
				[]Lit{ret.Lit, -next.Lit},
				[]Lit{-ret.Lit, li.Lit, lj.Lit, next.Lit},
				[]Lit{-ret.Lit, li.Lit, -lj.Lit, -next.Lit},
				[]Lit{-ret.Lit, -li.Lit, lj.Lit, -next.Lit},
				[]Lit{-ret.Lit, -li.Lit, -lj.Lit, next.Lit},
			)
			ret = next
		}
		return

	case file.EquOpNE:
		// For boolean disequality, we do much the same thing, except we have to
		// do it pairwise.

		// First two terms
		ret = exprLit{Lit: db.newAtom()}
		l0 := lArgs[0]
		l1 := lArgs[1]
		db.AddClauses(
			[]Lit{l0.Lit, l1.Lit, -ret.Lit},
			[]Lit{l0.Lit, -l1.Lit, ret.Lit},
			[]Lit{-l0.Lit, l1.Lit, ret.Lit},
			[]Lit{-l0.Lit, -l1.Lit, -ret.Lit},
		)

		// Fold
		for i := 0; i < n; i++ {
			for j := i + 1; j < n; j++ {
				// Account for the case we've already seen
				if i == 0 && j == 1 {
					continue
				}
				// Otherwise, proceed as normal
				next := exprLit{Lit: db.newAtom()}
				li := lArgs[i]
				lj := lArgs[j]
				db.AddClauses(
					[]Lit{ret.Lit, -next.Lit},
					[]Lit{-ret.Lit, li.Lit, lj.Lit, -next.Lit},
					[]Lit{-ret.Lit, li.Lit, -lj.Lit, next.Lit},
					[]Lit{-ret.Lit, -li.Lit, lj.Lit, next.Lit},
					[]Lit{-ret.Lit, -li.Lit, -lj.Lit, -next.Lit},
				)
				ret = next
			}
		}
		return

	default:
		panic("Invalid equality operation")
	}
}

func (db *DB) processIntEquOp(e file.EquOpBuilder, a0 expr, ctx context) (ret exprLit, err error) {

	// We should have exactly two arguments
	if len(e.Arguments) != 2 {
		err = fmt.Errorf(
			"too many arguments to equality operator at :%d:%d",
			e.Position().Line,
			e.Position().Column,
		)
		return
	}

	// Variables we will assert equality/disequality between, along with the
	// constant.
	var x, y VariableID
	var k *big.Int

	// Process the second argument
	var a1 expr
	a1, err = db.processExpr(e.Arguments[1], ctx)

	// Switch on the first argument
	switch arg0 := a0.(type) {
	case exprDiff:
		// We expect the second argument to be a constant.
		var arg1 exprConst
		arg1, err = convertExprAt[exprConst](a1, e.Arguments[1].Position())
		if err != nil {
			return
		}
		// Populate
		x = arg0.X
		y = arg0.Y
		k = arg1.Val
	case exprVar:
		// We expect the second argument to be a variable.
		// We expect the second argument to be a constant.
		var arg1 exprVar
		arg1, err = convertExprAt[exprVar](a1, e.Arguments[1].Position())
		if err != nil {
			return
		}
		// Populate
		x = arg0.Var
		y = arg1.Var
		k = big.NewInt(0)
	default:
		panic("Unhandled case")
	}

	// Create the return literal, and each expression.
	ret = exprLit{Lit: db.newAtom()}
	el := db.handleCmp(file.CmpOpLE, x, y, k)
	er := db.handleCmp(file.CmpOpGE, x, y, k)

	// Decide how they relate based on the operation.
	switch e.Operation {
	case file.EquOpEQ:
		db.AddClauses(
			[]Lit{el.Lit, -ret.Lit},
			[]Lit{er.Lit, -ret.Lit},
			[]Lit{-el.Lit, -er.Lit, ret.Lit},
		)
	case file.EquOpNE:
		db.AddClauses(
			[]Lit{el.Lit, ret.Lit},
			[]Lit{er.Lit, ret.Lit},
			[]Lit{-el.Lit, -er.Lit, -ret.Lit},
		)
	default:
		panic("Invalid equality operation")
	}
	return
}

func (db *DB) processLet(e file.LetBuilder, ctx context) (ret expr, err error) {

	// Create the child context
	newCtx := ctx.MakeChild()

	// Process each of the let bindings in the current context
	for _, binding := range e.Bindings {
		// Process the expression
		var val expr
		val, err = db.processExpr(binding.Bind, ctx)
		if err != nil {
			return
		}
		// Add it to the new context
		newCtx.AddName(string(binding.Name), val)
	}

	// Return the expression in the new context
	return db.processExpr(e.Expr, newCtx)
}
