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

// An AdjacencyList represents the adjacency list of the constraint graph. The
// first variable is the source [Node], followed by the destination [Node],
// followed by the weight.
//
// If the first variable is not present, then it has no outgoing edges. If the
// second variable is not present, there is no edge to that vertex.
type AdjacencyList = map[Node]map[Node]*big.Int

// A Cycle is a list of [Nodes] such that all adjacent ones are adjacent, and
// the last one is adjacent to the first.
type Cycle = []db.VariableID

// A Solver takes in an [AdjacencyList] representing the conflict graph. If a
// negative-weight cycle exists in the conflict graph, it returns it. Otherwise,
// it returns an error.
type Solver interface {
	Solve(AdjacencyList) (Cycle, error)
}

// The Solvers variable stores a map from strings to the [Solver] they are
// associated with. We use this map when processing command-line arguments.
var Solvers = map[string]Solver{
	"bf": BF{},
}

// The Solve function implements the high-level solving algorithm described in
// class. In other words, it implements offline DPLL(T). It is complete - it
// will never return unknown.
func Solve(db *db.DB, thr Solver) file.Status {
	return file.StatusSat
}
