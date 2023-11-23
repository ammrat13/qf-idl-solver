package preprocess_test

import (
	"math/big"
	"testing"

	"github.com/ammrat13/qf-idl-solver/internal/db"
	"github.com/ammrat13/qf-idl-solver/internal/file"
	"github.com/ammrat13/qf-idl-solver/internal/preprocess"
	"github.com/go-air/gini"
)

func TestT(t *testing.T) {
	preprocessors := map[string]preprocess.Preprocessor{
		"t-lin":  preprocess.TLin{},
		"t-quad": preprocess.TQuad{},
	}
	tests := map[string]struct {
		base    db.DB
		clauses [][]db.Lit
		stat    file.Status
	}{
		"both_sat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 0, Y: 1, K: big.NewInt(20)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3, 4},
				},
			},
			clauses: [][]db.Lit{
				{1},
				{-2},
				{3},
				{4},
			},
			stat: file.StatusSat,
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
			clauses: [][]db.Lit{
				{1},
				{-2},
				{-3},
				{4},
			},
			stat: file.StatusSat,
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
			clauses: [][]db.Lit{
				{1},
				{-2},
				{-3},
				{-4},
			},
			stat: file.StatusSat,
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
			clauses: [][]db.Lit{
				{1},
				{-2},
				{3},
				{-4},
			},
			stat: file.StatusUnsat,
		},
	}

	for name, test := range tests {
		test := test
		t.Run(name, func(t *testing.T) {
			for preprocName, preproc := range preprocessors {
				preproc := preproc
				t.Run(preprocName, func(t *testing.T) {
					t.Parallel()

					ret := test.base
					ret.Clauses = gini.New()
					ret.AddClauses(test.clauses...)

					preproc.Preprocess(&ret)
					if ret.SATSolve() != test.stat {
						t.Errorf("wrong satisfiability")
					}
				})
			}
		})
	}
}
