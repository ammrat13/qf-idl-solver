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
// along with the underlying literal.
type Edge struct {
	Weight *big.Int
	Lit    db.Lit
}

// An AdjacencyList represents the adjacency list of the constraint graph. The
// first variable is the source [Node], followed by the destination [Node],
// followed by the weight (and underlying literal).
//
// If the first variable is not present, then it has no outgoing edges. If the
// second variable is not present, there is no edge to that vertex.
type AdjacencyList = map[Node]map[Node]Edge

// A Cycle is a list of [Node] such that all consecutive ones are adjacent, and
// the last one is adjacent to the first.
type Cycle = []db.VariableID

// A Solver takes in an [AdjacencyList] representing the conflict graph, as well
// as the number of nodes in the graph. If a negative-weight cycle exists in the
// conflict graph, it returns it. Otherwise, it returns an error.
type Solver interface {
	Solve(AdjacencyList) (Cycle, error)

	// The SetNumVar method tells the solver how many variables exist in the
	// problem. This is called once before solving beings.
	SetNumVar(uint)
}

// The Solvers variable stores a map from strings to the [Solver] they are
// associated with. We use this map when processing command-line arguments.
var Solvers = map[string]Solver{
	"bf": &BF{},
}

// The Solve function implements the high-level solving algorithm described in
// class. In other words, it implements offline DPLL(T). It is complete - it
// will never return unknown. It may panic though.
func Solve(dbase *db.DB, thr Solver) file.Status {

	// Do theory setup.
	thr.SetNumVar(dbase.NextVariable)

	for {
		// SAT Solve. If unsat, return unsat.
		satres := dbase.SATSolve()
		if satres == file.StatusUnsat {
			return file.StatusUnsat
		}

		// Otherwise, construct the adjacency list. We do this in two passes. In
		// the first, we look for positive atoms, which we can inject into the
		// adjacency list directly. In the second, we look for negative atoms,
		// for which we have to add constraints to make sure we don't
		// accidentally satisfy them.
		adjList := make(AdjacencyList)
		for pospair, atoms := range dbase.Variables2AtomIDs {
			one := big.NewInt(1)
			negpair := db.VariablePair{
				Fst: pospair.Snd,
				Snd: pospair.Fst,
			}

			// Positive pass
			for i := 0; i < len(atoms); i++ {
				atom := atoms[i]
				if !dbase.Value(atom) {
					continue
				}
				// Assert x <= y + k
				addEdge(adjList, pospair, Edge{
					Weight: dbase.AtomID2Diff[atom].K,
					Lit:    atom,
				})
				break
			}

			// Negative pass
			for i := len(atoms) - 1; i >= 0; i-- {
				atom := atoms[i]
				if dbase.Value(atom) {
					continue
				}
				// Assert x > y + k, which is equivalent to y <= x - k - 1
				var newK *big.Int
				newK = new(big.Int).Neg(dbase.AtomID2Diff[atom].K)
				newK = newK.Sub(newK, one)
				addEdge(adjList, negpair, Edge{
					Weight: newK,
					Lit:    -atom,
				})
				break
			}
		}

		// Send the adjacency list to the theory solver.
		cycle, err := thr.Solve(adjList)
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
			toAdd[i] = -adjList[cycle[i]][cycle[j]].Lit
		}
		dbase.AddClauses(toAdd)
	}
}

func addEdge(adjList AdjacencyList, varpair db.VariablePair, edge Edge) {
	// Make sure the source (second) variable is populated.
	_, ok := adjList[varpair.Snd]
	if !ok {
		adjList[varpair.Snd] = make(map[Node]Edge)
	}
	// If it doesn't exist, just add it. If it does, first check that the edge
	// is less than.
	oldEdge, ok := adjList[varpair.Snd][varpair.Fst]
	if !ok || oldEdge.Weight.Cmp(edge.Weight) == 1 {
		adjList[varpair.Snd][varpair.Fst] = edge
	}
}
