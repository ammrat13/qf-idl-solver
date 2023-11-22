package db_test

import (
	"math/big"
	"reflect"
	"testing"

	"github.com/ammrat13/qf-idl-solver/internal/db"
	"github.com/ammrat13/qf-idl-solver/internal/file"
)

func TestMaps(t *testing.T) {
	tests := map[string]struct {
		ast file.File
		a2d map[db.AtomID]*db.DifferenceConstraint
		v2a map[db.VariablePair][]db.AtomID
	}{
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
			},
			v2a: map[db.VariablePair][]db.AtomID{
				{Fst: 0, Snd: 1}: {3},
			},
		},
		"sorting": {
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
								Num: file.Number{Value: big.NewInt(20)},
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
				3: {X: 0, Y: 1, K: big.NewInt(20)},
				4: {X: 0, Y: 1, K: big.NewInt(10)},
			},
			v2a: map[db.VariablePair][]db.AtomID{
				{Fst: 0, Snd: 1}: {4, 3},
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
