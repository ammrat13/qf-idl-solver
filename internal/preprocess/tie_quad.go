package preprocess

import (
	"math/big"

	"github.com/ammrat13/qf-idl-solver/internal/db"
)

// The TIEQuad preprocessor applies all the preprocessing rules, effectively
// eagerly adding constraints for each pair of difference constraints. It does
// so by looping over all the possibilities, causing a quadratic increase in the
// number of clauses.
type TIEQuad struct{}

func (TIEQuad) Preprocess(dbase *db.DB) {

	// Auxiliary variables
	ONE := big.NewInt(1)

	// Apply all the transitivity constraints.
	TransLin{}.Preprocess(dbase)

	// For each pair of variables, add inclusion and exclusion constraints.
	for pospair, posatoms := range dbase.Variables2AtomIDs {
		negpair := db.VariablePair{
			Fst: pospair.Snd,
			Snd: pospair.Fst,
		}
		negatoms := dbase.Variables2AtomIDs[negpair]

		// If we have no corresponding negative atoms, we can't do anything
		if len(negatoms) == 0 {
			continue
		}

		// For each atom in the positive pair...
		for i := 0; i < len(posatoms); i++ {
			ai := posatoms[i]
			ki := dbase.AtomID2Diff[ai].K
			if ki == nil {
				panic("Atom not in AtomID2Diff")
			}

			// Compute the threshold to decide which case we're in. If the
			// constant is less than or equal to this, the difference can't be
			// in both (exclusion). If it's greater than or equal to, the
			// difference can't be in neither (inclusion).
			var threshold *big.Int
			threshold = new(big.Int).Neg(ki)
			threshold = threshold.Sub(threshold, ONE)

			// ... analyze the negative pair
			for j := 0; j < len(negatoms); j++ {
				aj := negatoms[j]
				kj := dbase.AtomID2Diff[aj].K
				if kj == nil {
					panic("Atom not in AtomID2Diff")
				}

				// Handle inclusion
				if threshold.Cmp(kj) <= 0 {
					dbase.AddClauses([]db.Lit{ai, aj})
				}
				// Handle exclusion
				if threshold.Cmp(kj) >= 0 {
					dbase.AddClauses([]db.Lit{-ai, -aj})
				}
			}
		}
	}
}
