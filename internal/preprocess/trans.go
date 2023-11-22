package preprocess

import (
	"github.com/ammrat13/qf-idl-solver/internal/db"
)

// The Trans preprocessor only applies the transitivity rule. This is the bare
// minimum required to allow the solver to function.
type Trans struct{}

func (Trans) Preprocess(db *db.DB) {

	// For each pair of variables, add constraints.
	for _, atoms := range db.Variables2AtomIDs {
		// Transitivity only applies between two different constraints. If we
		// don't have that many, bail.
		if len(atoms) < 2 {
			continue
		}

		// Have each constraint imply the next, since they are in sorted order
		// by their constants. Remember that the difference constraints have the
		// form x - y <= k. Furthermore, if two subsequent constants are equal,
		// add an if-and-only-if.
		for i := 0; i < len(atoms)-1; i++ {
			j := i + 1

			ai := atoms[i]
			aj := atoms[j]

			// Retrive the constants.
			ki := db.AtomID2Diff[ai].K
			kj := db.AtomID2Diff[aj].K
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
			db.AddClauses([]int{-ai, aj})
		}
	}
}
