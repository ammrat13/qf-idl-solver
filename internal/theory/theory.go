// The theory package has all of the theory solvers. These accept a weighted
// directed graph as input, and output a negative cycle if one exists.
package theory

import (
	"math/big"
	"time"

	"github.com/ammrat13/qf-idl-solver/internal/db"
	"github.com/ammrat13/qf-idl-solver/internal/file"
	"github.com/ammrat13/qf-idl-solver/internal/stats"
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

// A nodeState describes the different states a vertex can be in in the
// unlabeled / labeled / scanned paradigm.
type nodeState int

const (
	nodeStateUnlabeled nodeState = iota
	nodeStateLabeled
	nodeStateScanned
)

// A Solver takes in an [AdjacencyList] representing the conflict graph, as well
// as the number of nodes in the graph. If a negative-weight cycle exists in the
// conflict graph, it returns it. Otherwise, it returns an error.
type Solver interface {
	Solve(AdjacencyList, *stats.Stats) (Cycle, error)

	// The SetNumVar method tells the solver how many variables exist in the
	// problem. This is called once before solving beings.
	SetNumVar(uint)

	// The Copy method creates a deep copy of this solver instance. This is
	// needed since solver instances are pointers.
	Copy() Solver
}

// The Solvers variable stores a map from strings to the [Solver] they are
// associated with. We use this map when processing command-line arguments.
var Solvers = map[string]Solver{
	"bf-basic":   &BF{BasicMode: true},
	"bf-full":    &BF{BasicMode: false},
	"spfa-basic": &SPFA{BasicMode: true},
	"spfa-full":  &SPFA{BasicMode: false},
}

// The Solve function implements the high-level solving algorithm described in
// class. In other words, it implements offline DPLL(T). It is complete - it
// will never return unknown. It may panic though.
func Solve(dbase *db.DB, thr Solver, stats *stats.Stats) file.Status {

	// Do theory setup.
	thr.SetNumVar(dbase.NextVariable)

	// Auxiliary variables
	ONE := big.NewInt(1)

	for {
		stats.SolverCalls++

		// SAT Solve.
		t_sat_start := time.Now()
		satres := dbase.SATSolve()
		t_sat_end := time.Now()
		stats.SATSolverDuration += t_sat_end.Sub(t_sat_start)
		// If unsat, return unsat.
		if satres == file.StatusUnsat {
			return file.StatusUnsat
		}

		// Otherwise, construct the adjacency list.
		//
		// Logically, we do this in two passes. In the first, we look for
		// positive atoms, which we can inject into the adjacency list directly.
		// In the second, we look for negative atoms, for which we have to add
		// constraints to make sure we don't accidentally satisfy them.
		//
		// Practically, we first scan through the adjacency list looking for the
		// first positive and the last negative atoms.
		t_graph_start := time.Now()
		adjList := make(AdjacencyList)
		for pospair, atoms := range dbase.Variables2AtomIDs {
			negpair := db.VariablePair{
				Fst: pospair.Snd,
				Snd: pospair.Fst,
			}

			// Iterate through the array looking for positive and negative
			// atoms.
			posFound := false
			negFound := false
			posI := 0
			negI := 0
			for i := 0; i < len(atoms); i++ {
				atom := atoms[i]
				// Only record the first positive instance. Remember everything
				// is sorted.
				if !posFound && dbase.Value(atom) {
					posFound = true
					posI = i
				}
				// Remember the last negative instance.
				if !dbase.Value(atom) {
					negFound = true
					negI = i
				}
			}

			// Positive pass
			if posFound {
				atom := atoms[posI]
				// Assert x <= y + k
				addEdge(adjList, pospair, Edge{
					Weight: dbase.AtomID2Diff[atom].K,
					Lit:    atom,
				})
			}

			// Negative pass
			if negFound {
				atom := atoms[negI]
				// Assert x > y + k, which is equivalent to y <= x - k - 1
				var newK *big.Int
				newK = new(big.Int).Neg(dbase.AtomID2Diff[atom].K)
				newK = newK.Sub(newK, ONE)
				addEdge(adjList, negpair, Edge{
					Weight: newK,
					Lit:    -atom,
				})
			}
		}
		t_graph_end := time.Now()
		stats.GraphOverheadDuration += t_graph_end.Sub(t_graph_start)

		// Send the adjacency list to the theory solver.
		t_thr_start := time.Now()
		cycle, err := thr.Solve(adjList, stats)
		t_thr_end := time.Now()
		stats.TheorySolverDuration += t_thr_end.Sub(t_thr_start)
		// If sat, we're done
		if err != nil {
			return file.StatusSat
		}

		// Otherwise, walk the returned cycle and add the newly learned
		// constraints.
		t_lrn_start := time.Now()
		toAdd := make([]db.Lit, len(cycle))
		for i := 0; i < len(cycle); i++ {
			j := (i + 1) % len(cycle)
			toAdd[i] = -adjList[cycle[i]][cycle[j]].Lit
		}
		dbase.AddClauses(toAdd)
		t_lrn_end := time.Now()
		stats.LearnOverheadDuration += t_lrn_end.Sub(t_lrn_start)
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
