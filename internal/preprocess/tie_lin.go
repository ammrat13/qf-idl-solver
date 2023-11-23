package preprocess

import (
	"math/big"
	"sort"

	"github.com/ammrat13/qf-idl-solver/internal/db"
)

// The TIELin preprocessor applies all the preprocessing rules, effectively
// eagerly adding constraints for each pair of difference constraints. However,
// it only applies it to ones that imply all the others so that the number of
// extra clauses is linear.
type TIELin struct{}

func (TIELin) Preprocess(dbase *db.DB) {

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

		// For each atom in the positive pair, analyze the negative pair.
		for i := 0; i < len(posatoms)-1; i++ {
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

			// Find the start of the inclusion range.
			inclJ := sort.Search(len(negatoms), func(j int) bool {
				aj := negatoms[j]
				kj := dbase.AtomID2Diff[aj].K
				if kj == nil {
					panic("Atom not in AtomID2Diff")
				}
				return threshold.Cmp(kj) <= 0
			})
			// Handle inclusion
			if inclJ < len(negatoms) {
				aInclJ := negatoms[inclJ]
				dbase.AddClauses([]db.Lit{ai, aInclJ})
			}
			// Handle exclusion
			if inclJ > 0 {
				aExclJ := negatoms[inclJ-1]
				dbase.AddClauses([]db.Lit{-ai, -aExclJ})
			}
		}
	}
}
