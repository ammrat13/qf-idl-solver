// The theory package has all of the theory solvers. These accept a weighted
// directed graph as input, and output a negative cycle if one exists.
package theory

import (
	"math/big"

	"github.com/ammrat13/qf-idl-solver/internal/db"
	"github.com/ammrat13/qf-idl-solver/internal/file"
)

// A Node in the constraint graph is just a variable.
type Node = db.VariableID

// An Edge consists of the metadata associated with an edge. That's its weight
// along with the underlying atom.
type Edge struct {
	Weight *big.Int
	Atom   db.AtomID
}

// An AdjacencyList represents the adjacency list of the constraint graph. The
// first variable is the source [Node], followed by the destination [Node],
// followed by the weight (and underlying atom).
//
// If the first variable is not present, then it has no outgoing edges. If the
// second variable is not present, there is no edge to that vertex.
type AdjacencyList = map[Node]map[Node]Edge

// A Cycle is a list of [Nodes] such that all adjacent ones are adjacent, and
// the last one is adjacent to the first.
type Cycle = []db.VariableID

// A Solver takes in an [AdjacencyList] representing the conflict graph, as well
// as the number of nodes in the graph. If a negative-weight cycle exists in the
// conflict graph, it returns it. Otherwise, it returns an error.
type Solver interface {
	Solve(AdjacencyList, uint64) (Cycle, error)
}

// The Solvers variable stores a map from strings to the [Solver] they are
// associated with. We use this map when processing command-line arguments.
var Solvers = map[string]Solver{
	"bf": BF{},
}

// The Solve function implements the high-level solving algorithm described in
// class. In other words, it implements offline DPLL(T). It is complete - it
// will never return unknown. It may panic though.
func Solve(db *db.DB, thr Solver) file.Status {
	for {
		// SAT Solve.
		satres := db.SATSolve()
		if satres == file.StatusUnknown {
			panic("SAT solver returned unknown")
		}
		// If unsat, return unsat
		if satres == file.StatusUnsat {
			return file.StatusUnsat
		}

		// Otherwise, construct the adjacency list.
		adjList := make(AdjacencyList)
		for varpair, atoms := range db.Variables2AtomIDs {
			// Look for the first atom that is true. Remember that it's sorted
			// by ascending order of constants.
			for _, atom := range atoms {
				var ok bool
				if !db.Value(atom) {
					continue
				}

				// Make sure the first variable is populated.
				_, ok = adjList[varpair.Fst]
				if !ok {
					adjList[varpair.Fst] = make(map[Node]Edge)
				}
				// Get the constant value for the atom.
				k := db.AtomID2Diff[atom].K
				if k == nil {
					panic("Bad constant")
				}
				// Add it to the adjacency list.
				adjList[varpair.Fst][varpair.Snd] = Edge{Weight: k, Atom: atom}
			}
		}

		// Send the adjacency list to the theory solver.
		cycle, err := thr.Solve(adjList, db.NextVariable)
		// If sat, we're done
		if err != nil {
			return file.StatusSat
		}

		// Otherwise, walk the returned cycle and add the newly learned
		// constraints.
		toAdd := make([]int, len(cycle))
		for i := 0; i < len(cycle); i++ {
			j := (i + 1) % len(cycle)

			// Check that the values are in the maps.
			var ok bool
			_, ok = adjList[cycle[i]]
			if !ok {
				panic("Value not in map")
			}
			_, ok = adjList[cycle[i]][cycle[j]]
			if !ok {
				panic("Value not in map")
			}

			// Add the new constraint.
			toAdd[i] = -adjList[cycle[i]][cycle[j]].Atom
		}
		db.AddClauses(toAdd)
	}
}
