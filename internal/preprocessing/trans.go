package preprocessing

import (
	"github.com/ammrat13/qf-idl-solver/internal/db"
)

// The Trans preprocessor only applies the transitivity rule. This is the bare
// minimum required to allow the solver to function.
type Trans struct{}

// The NewTrans function creates a new [Trans] instance.
func NewTrans() Trans { return Trans{} }

func (t Trans) Preprocess(db *db.DB) {

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
			di, ok := db.AtomID2Diff[ai]
			ki := di.K
			if !ok || ki == nil {
				panic("Atom not in AtomID2Diff")
			}
			dj, ok := db.AtomID2Diff[aj]
			kj := dj.K
			if !ok || kj == nil {
				panic("Atom not in AtomID2Diff")
			}
			// The constraints should be in sorted order
			if ki.Cmp(kj) == 1 {
				panic("Atoms not in sorted order")
			}

			// Add the constraints
			db.AddClauses([]int{-ai, aj})
			if ki.Cmp(kj) == 0 {
				db.AddClauses([]int{-aj, ai})
			}
		}
	}
}
