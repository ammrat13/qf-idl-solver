package preprocess

import (
	"github.com/ammrat13/qf-idl-solver/internal/db"
)

// The TQuad preprocessor only applies the transitivity rule. To do this, it
// tries to apply it to every pair of atoms for each variable pair. In this way,
// the number of extra clauses is quadratic in the number of atoms.
type TQuad struct{}

func (TQuad) Preprocess(dbase *db.DB) {

	// For each pair of variables, add constraints.
	for _, atoms := range dbase.Variables2AtomIDs {
		// Transitivity only applies between two different constraints. If we
		// don't have that many, bail.
		if len(atoms) < 2 {
			continue
		}

		// Loop over each pair of atoms that imply each other, and add the
		// implication. Remember that the list is in sorted order.
		for i := 0; i < len(atoms)-1; i++ {
			for j := i + 1; j < len(atoms); j++ {
				ai := atoms[i]
				aj := atoms[j]

				// Retrive the constants.
				ki := dbase.AtomID2Diff[ai].K
				kj := dbase.AtomID2Diff[aj].K
				if ki == nil || kj == nil {
					panic("Atom not in AtomID2Diff")
				}
				// The constraints should be in sorted order, and they should be
				// distinct.
				if ki.Cmp(kj) == 1 {
					panic("Atoms not in sorted order")
				}
				if ki.Cmp(kj) == 0 {
					panic("Atoms not distinct")
				}

				// Add the constraints
				dbase.AddClauses([]db.Lit{-ai, aj})
			}
		}
	}
}
