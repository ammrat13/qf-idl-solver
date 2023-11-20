package preprocessing_test

import (
	"math/big"
	"testing"

	"github.com/ammrat13/qf-idl-solver/internal/db"
	"github.com/ammrat13/qf-idl-solver/internal/preprocessing"
	"github.com/go-air/gini"
)

func TestTrans(t *testing.T) {
	tests := map[string]struct {
		base    db.DB
		clauses [][]int
		sat     int
	}{
		"basic_sat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 0, Y: 1, K: big.NewInt(20)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3, 4},
				},
			},
			clauses: [][]int{
				{1},
				{-2},
				{3},
				{4},
			},
			sat: 1,
		},
		"lhs_sat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 0, Y: 1, K: big.NewInt(20)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3, 4},
				},
			},
			clauses: [][]int{
				{1},
				{-2},
				{-3},
				{4},
			},
			sat: 1,
		},
		"none_sat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 0, Y: 1, K: big.NewInt(20)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3, 4},
				},
			},
			clauses: [][]int{
				{1},
				{-2},
				{-3},
				{-4},
			},
			sat: 1,
		},
		"unsat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 0, Y: 1, K: big.NewInt(20)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3, 4},
				},
			},
			clauses: [][]int{
				{1},
				{-2},
				{3},
				{-4},
			},
			sat: -1,
		},
	}

	for name, test := range tests {
		test := test
		t.Run(name, func(t *testing.T) {
			t.Parallel()

			ret := test.base
			ret.Clauses = gini.New()
			ret.AddClauses(test.clauses...)

			preprocessing.NewTrans().Preprocess(&ret)

			if ret.Clauses.Solve() != test.sat {
				t.Errorf("wrong satisfiability")
			}
		})
	}
}
