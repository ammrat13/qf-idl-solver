package preprocess_test

import (
	"math/big"
	"testing"

	"github.com/ammrat13/qf-idl-solver/internal/db"
	"github.com/ammrat13/qf-idl-solver/internal/file"
	"github.com/ammrat13/qf-idl-solver/internal/preprocess"
	"github.com/go-air/gini"
)

func TestTIE(t *testing.T) {
	preprocessors := map[string]preprocess.Preprocessor{
		"tie-lin":  preprocess.TIELin{},
		"tie-quad": preprocess.TIEQuad{},
	}
	tests := map[string]struct {
		base    db.DB
		clauses [][]db.Lit
		stat    file.Status
	}{
		"t-both_sat": {
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
		"t-lhs_sat": {
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
		"t-none_sat": {
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
		"t-unsat": {
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
		"i-lhs_sat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 1, Y: 0, K: big.NewInt(-10)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3},
					{Fst: 1, Snd: 0}: {4},
				},
			},
			clauses: [][]db.Lit{
				{1},
				{-2},
				{3},
				{-4},
			},
			stat: file.StatusSat,
		},
		"i-rhs_sat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 1, Y: 0, K: big.NewInt(-10)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3},
					{Fst: 1, Snd: 0}: {4},
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
		"i-both_sat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 1, Y: 0, K: big.NewInt(-10)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3},
					{Fst: 1, Snd: 0}: {4},
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
		"i-unsat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 1, Y: 0, K: big.NewInt(-10)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3},
					{Fst: 1, Snd: 0}: {4},
				},
			},
			clauses: [][]db.Lit{
				{1},
				{-2},
				{-3},
				{-4},
			},
			stat: file.StatusUnsat,
		},
		"e-lhs_sat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 1, Y: 0, K: big.NewInt(-12)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3},
					{Fst: 1, Snd: 0}: {4},
				},
			},
			clauses: [][]db.Lit{
				{1},
				{-2},
				{3},
				{-4},
			},
			stat: file.StatusSat,
		},
		"e-rhs_sat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 1, Y: 0, K: big.NewInt(-12)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3},
					{Fst: 1, Snd: 0}: {4},
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
		"e-none_sat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 1, Y: 0, K: big.NewInt(-12)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3},
					{Fst: 1, Snd: 0}: {4},
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
		"e-unsat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 1, Y: 0, K: big.NewInt(-12)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3},
					{Fst: 1, Snd: 0}: {4},
				},
			},
			clauses: [][]db.Lit{
				{1},
				{-2},
				{3},
				{4},
			},
			stat: file.StatusUnsat,
		},
		"ie-lhs_sat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 1, Y: 0, K: big.NewInt(-11)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3},
					{Fst: 1, Snd: 0}: {4},
				},
			},
			clauses: [][]db.Lit{
				{1},
				{-2},
				{3},
				{-4},
			},
			stat: file.StatusSat,
		},
		"ie-rhs_sat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 1, Y: 0, K: big.NewInt(-11)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3},
					{Fst: 1, Snd: 0}: {4},
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
		"ie-both_unsat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 1, Y: 0, K: big.NewInt(-11)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3},
					{Fst: 1, Snd: 0}: {4},
				},
			},
			clauses: [][]db.Lit{
				{1},
				{-2},
				{3},
				{4},
			},
			stat: file.StatusUnsat,
		},
		"i-none_unsat": {
			base: db.DB{
				AtomID2Diff: map[db.AtomID]*db.DifferenceConstraint{
					3: {X: 0, Y: 1, K: big.NewInt(10)},
					4: {X: 1, Y: 0, K: big.NewInt(-11)},
				},
				Variables2AtomIDs: map[db.VariablePair][]db.AtomID{
					{Fst: 0, Snd: 1}: {3},
					{Fst: 1, Snd: 0}: {4},
				},
			},
			clauses: [][]db.Lit{
				{1},
				{-2},
				{-3},
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
