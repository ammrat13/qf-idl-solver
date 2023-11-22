package db_test

import (
	"math/big"
	"reflect"
	"testing"

	"github.com/ammrat13/qf-idl-solver/internal/db"
	"github.com/ammrat13/qf-idl-solver/internal/file"
	"github.com/ammrat13/qf-idl-solver/internal/theory"
)

func TestInequality(t *testing.T) {
	tests := map[string]struct {
		ast file.File
		a2d map[db.AtomID]*db.DifferenceConstraint
		v2a map[db.VariablePair][]db.AtomID
	}{
		"le": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortInt},
					{Name: file.Symbol("y"), Sort: file.SortInt},
				},
				Assertions: []file.Expr{
					file.CmpOpBuilder{
						Operation: file.CmpOpLE,
						Arguments: file.CmpDiff{
							Difference: file.DiffAtom{
								LHS: file.Symbol("x"),
								RHS: file.Symbol("y"),
							},
							Constant: file.NumberAtom{
								Num: file.Number{Value: big.NewInt(10)},
							},
						},
					},
				},
			},
			a2d: map[db.AtomID]*db.DifferenceConstraint{
				3: {X: 0, Y: 1, K: big.NewInt(10)},
			},
			v2a: map[db.VariablePair][]db.AtomID{
				{Fst: 0, Snd: 1}: {3},
			},
		},
		"gt": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortInt},
					{Name: file.Symbol("y"), Sort: file.SortInt},
				},
				Assertions: []file.Expr{
					file.CmpOpBuilder{
						Operation: file.CmpOpLE,
						Arguments: file.CmpDiff{
							Difference: file.DiffAtom{
								LHS: file.Symbol("x"),
								RHS: file.Symbol("y"),
							},
							Constant: file.NumberAtom{
								Num: file.Number{Value: big.NewInt(10)},
							},
						},
					},
				},
			},
			a2d: map[db.AtomID]*db.DifferenceConstraint{
				3: {X: 0, Y: 1, K: big.NewInt(10)},
			},
			v2a: map[db.VariablePair][]db.AtomID{
				{Fst: 0, Snd: 1}: {3},
			},
		},
		"ge": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortInt},
					{Name: file.Symbol("y"), Sort: file.SortInt},
				},
				Assertions: []file.Expr{
					file.CmpOpBuilder{
						Operation: file.CmpOpGE,
						Arguments: file.CmpDiff{
							Difference: file.DiffAtom{
								LHS: file.Symbol("x"),
								RHS: file.Symbol("y"),
							},
							Constant: file.NumberAtom{
								Num: file.Number{Value: big.NewInt(10)},
							},
						},
					},
				},
			},
			a2d: map[db.AtomID]*db.DifferenceConstraint{
				3: {X: 1, Y: 0, K: big.NewInt(-10)},
			},
			v2a: map[db.VariablePair][]db.AtomID{
				{Fst: 1, Snd: 0}: {3},
			},
		},
		"lt": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortInt},
					{Name: file.Symbol("y"), Sort: file.SortInt},
				},
				Assertions: []file.Expr{
					file.CmpOpBuilder{
						Operation: file.CmpOpGE,
						Arguments: file.CmpDiff{
							Difference: file.DiffAtom{
								LHS: file.Symbol("x"),
								RHS: file.Symbol("y"),
							},
							Constant: file.NumberAtom{
								Num: file.Number{Value: big.NewInt(10)},
							},
						},
					},
				},
			},
			a2d: map[db.AtomID]*db.DifferenceConstraint{
				3: {X: 1, Y: 0, K: big.NewInt(-10)},
			},
			v2a: map[db.VariablePair][]db.AtomID{
				{Fst: 1, Snd: 0}: {3},
			},
		},
		"equals": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortInt},
					{Name: file.Symbol("y"), Sort: file.SortInt},
				},
				Assertions: []file.Expr{
					file.EquOpBuilder{
						Operation: file.EquOpEQ,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("y")},
						},
					},
				},
			},
			a2d: map[db.AtomID]*db.DifferenceConstraint{
				3: {X: 0, Y: 1, K: big.NewInt(0)},
				4: {X: 1, Y: 0, K: big.NewInt(0)},
			},
			v2a: map[db.VariablePair][]db.AtomID{
				{Fst: 0, Snd: 1}: {3},
				{Fst: 1, Snd: 0}: {4},
			},
		},
		"distinct": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortInt},
					{Name: file.Symbol("y"), Sort: file.SortInt},
				},
				Assertions: []file.Expr{
					file.EquOpBuilder{
						Operation: file.EquOpNE,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("y")},
						},
					},
				},
			},
			a2d: map[db.AtomID]*db.DifferenceConstraint{
				3: {X: 0, Y: 1, K: big.NewInt(0)},
				4: {X: 1, Y: 0, K: big.NewInt(0)},
			},
			v2a: map[db.VariablePair][]db.AtomID{
				{Fst: 0, Snd: 1}: {3},
				{Fst: 1, Snd: 0}: {4},
			},
		},
		"duplicate": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortInt},
					{Name: file.Symbol("y"), Sort: file.SortInt},
				},
				Assertions: []file.Expr{
					file.CmpOpBuilder{
						Operation: file.CmpOpLE,
						Arguments: file.CmpDiff{
							Difference: file.DiffAtom{
								LHS: file.Symbol("x"),
								RHS: file.Symbol("y"),
							},
							Constant: file.NumberAtom{
								Num: file.Number{Value: big.NewInt(10)},
							},
						},
					},
					file.CmpOpBuilder{
						Operation: file.CmpOpLE,
						Arguments: file.CmpDiff{
							Difference: file.DiffAtom{
								LHS: file.Symbol("x"),
								RHS: file.Symbol("y"),
							},
							Constant: file.NumberAtom{
								Num: file.Number{Value: big.NewInt(10)},
							},
						},
					},
				},
			},
			a2d: map[db.AtomID]*db.DifferenceConstraint{
				3: {X: 0, Y: 1, K: big.NewInt(10)},
				4: {X: 0, Y: 1, K: big.NewInt(10)},
			},
			v2a: map[db.VariablePair][]db.AtomID{
				{Fst: 0, Snd: 1}: {3, 4},
			},
		},
	}

	for name, test := range tests {
		test := test
		t.Run(name, func(t *testing.T) {
			t.Parallel()

			ret, err := db.FromFile(test.ast)
			if err != nil {
				t.Errorf("construction error: %s", err.Error())
				t.FailNow()
			}

			if !reflect.DeepEqual(ret.AtomID2Diff, test.a2d) {
				t.Errorf("AtomID2Diff maps did not compare equal")
			}
			if !reflect.DeepEqual(ret.Variables2AtomIDs, test.v2a) {
				t.Errorf("Variables2AtomIDs maps did not compare equal")
			}
		})
	}
}

func TestInequalitySolver(t *testing.T) {
	tests := map[string]struct {
		ast  file.File
		stat file.Status
	}{
		"equality_sat_pos": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortInt},
					{Name: file.Symbol("y"), Sort: file.SortInt},
				},
				Assertions: []file.Expr{
					file.EquOpBuilder{
						Operation: file.EquOpEQ,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("y")},
						},
					},
					file.NotBuilder{
						Argument: file.EquOpBuilder{
							Operation: file.EquOpNE,
							Arguments: []file.Expr{
								file.SymbolAtom{Name: file.Symbol("x")},
								file.SymbolAtom{Name: file.Symbol("y")},
							},
						},
					},
				},
			},
			stat: file.StatusSat,
		},
		"equality_sat_neg": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortInt},
					{Name: file.Symbol("y"), Sort: file.SortInt},
				},
				Assertions: []file.Expr{
					file.NotBuilder{
						Argument: file.EquOpBuilder{
							Operation: file.EquOpEQ,
							Arguments: []file.Expr{
								file.SymbolAtom{Name: file.Symbol("x")},
								file.SymbolAtom{Name: file.Symbol("y")},
							},
						},
					},
					file.EquOpBuilder{
						Operation: file.EquOpNE,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("y")},
						},
					},
				},
			},
			stat: file.StatusSat,
		},
		"equality_unsat_pos": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortInt},
					{Name: file.Symbol("y"), Sort: file.SortInt},
				},
				Assertions: []file.Expr{
					file.EquOpBuilder{
						Operation: file.EquOpEQ,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("y")},
						},
					},
					file.EquOpBuilder{
						Operation: file.EquOpNE,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("y")},
						},
					},
				},
			},
			stat: file.StatusUnsat,
		},
		"equality_unsat_neg": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortInt},
					{Name: file.Symbol("y"), Sort: file.SortInt},
				},
				Assertions: []file.Expr{
					file.NotBuilder{
						Argument: file.EquOpBuilder{
							Operation: file.EquOpEQ,
							Arguments: []file.Expr{
								file.SymbolAtom{Name: file.Symbol("x")},
								file.SymbolAtom{Name: file.Symbol("y")},
							},
						},
					},
					file.NotBuilder{
						Argument: file.EquOpBuilder{
							Operation: file.EquOpNE,
							Arguments: []file.Expr{
								file.SymbolAtom{Name: file.Symbol("x")},
								file.SymbolAtom{Name: file.Symbol("y")},
							},
						},
					},
				},
			},
			stat: file.StatusUnsat,
		},
	}

	for name, test := range tests {
		test := test
		t.Run(name, func(t *testing.T) {
			for solverName, solver := range theory.Solvers {
				solver := solver
				t.Run(solverName, func(t *testing.T) {
					t.Parallel()

					db, err := db.FromFile(test.ast)
					if err != nil {
						t.Errorf("construction error: %s", err.Error())
						t.FailNow()
					}

					if theory.Solve(&db, solver) != test.stat {
						t.Errorf("wrong satisfiability")
					}
				})
			}
		})
	}
}
