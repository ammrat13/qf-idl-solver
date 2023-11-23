package preprocess

import (
	"github.com/ammrat13/qf-idl-solver/internal/db"
)

// The TransLin preprocessor only applies the transitivity rule. To do this, it
// scans across each variable pair's atoms array and says that one implies the
// next. In this way, the number of extra clauses is linear in the number of
// atoms associated with a pair of variables.
type TransLin struct{}

func (TransLin) Preprocess(dbase *db.DB) {

	// For each pair of variables, add constraints.
	for _, atoms := range dbase.Variables2AtomIDs {
		// Transitivity only applies between two different constraints. If we
		// don't have that many, bail.
		if len(atoms) < 2 {
			continue
		}

		// Have each constraint imply the next, since they are in sorted order
		// by their constants. Remember that the difference constraints have the
		// form x - y <= k.
		for i := 0; i < len(atoms)-1; i++ {
			j := i + 1

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
