package db_test

import (
	"math/big"
	"reflect"
	"testing"

	"github.com/ammrat13/qf-idl-solver/internal/db"
	"github.com/ammrat13/qf-idl-solver/internal/file"
)

func TestInequality(t *testing.T) {
	tests := map[string]struct {
		ast file.File
		a2d map[db.AtomID]*db.DifferenceConstraint
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
				t.Errorf("maps did not compare equal")
			}
		})
	}
}
