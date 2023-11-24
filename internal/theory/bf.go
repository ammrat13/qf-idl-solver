package theory

import (
	"errors"
	"math/big"

	"github.com/ammrat13/qf-idl-solver/internal/stats"
)

// The BF struct implements the Bellman-Ford algorithm. It doesn't do any
// optimization, except for possibly early termination.
type BF struct {
	// The BasicMode field reports whether to disable early termination.
	BasicMode bool

	// The number of variables in this problem instance.
	numVar uint

	// The graph field is the input graph we're checking for negative cycles
	// for. It always has numVar nodes numbered 0 to numVar-1.
	graph AdjacencyList

	// The nodes field consists of all the metadata we keep on a per-node basis.
	// The index corresponds to the node number.
	nodes []bfNodeData
}

func (thr *BF) SetNumVar(numVar uint) { thr.numVar = numVar }
func (thr BF) Copy() Solver           { return &BF{BasicMode: thr.BasicMode, numVar: thr.numVar} }

// A nodeData struct holds all the bookkeeping infomation we keep on a
// per-vertex basis.
type bfNodeData struct {

	// The Distance field is the current label of the node. It is always an
	// upper-bound on the true distance to the node.
	Distance *big.Int

	// The Predecessor field indicates the node before this one in the shortest
	// path. A nil predecessor means this is a root in the forest.
	Predecessor *Node
}

func (thr *BF) Solve(graph AdjacencyList, stats *stats.Stats) (ret Cycle, err error) {

	// Create the auxiliary structures.
	thr.graph = graph
	thr.nodes = make([]bfNodeData, thr.numVar)
	ZERO := big.NewInt(0)

	// Initialize all nodes at distance zero.
	for i := range thr.nodes {
		thr.nodes[i] = bfNodeData{
			Distance:    ZERO,
			Predecessor: nil,
		}
	}

	// Main relaxation loop. We repeat this N-1 times. We really have one more
	// vertex than the problem instance, but we've already done one relaxation
	// loop.
	for it := uint(0); it < thr.numVar-1; it++ {
		changed := false

		// Iterate over every edge and relax it. Remember to capture the loop
		// variable. We take its adress, but we don't want the aliased data to
		// change out from under us on subsequent loops.
		for uIdx, vIdxs := range thr.graph {
			uIdx := uIdx
			uDat := &thr.nodes[uIdx]
			for vIdx, edge := range vIdxs {
				vDat := &thr.nodes[vIdx]
				stats.TheorySolverLoops++

				vDist := new(big.Int).Add(uDat.Distance, edge.Weight)
				if vDist.Cmp(vDat.Distance) == -1 {
					changed = true
					vDat.Distance = vDist
					vDat.Predecessor = &uIdx
				}
			}
		}

		// If we made no change this loop, we can bail.
		if !thr.BasicMode && !changed {
			return Cycle{}, errors.New("no negative cycle")
		}
	}

	// Relax one last time to check for negative cycles.
	for uIdx, vIdxs := range thr.graph {
		uIdx := uIdx
		uDat := &thr.nodes[uIdx]
		for vIdx, edge := range vIdxs {
			vDat := &thr.nodes[vIdx]
			stats.TheorySolverLoops++

			vDist := new(big.Int).Add(uDat.Distance, edge.Weight)
			if vDist.Cmp(vDat.Distance) == -1 {
				vDat.Distance = vDist
				vDat.Predecessor = &uIdx
				return thr.findCycleFrom(vIdx, stats), nil
			}
		}
	}

	// Couldn't find anything
	return Cycle{}, errors.New("no negative cycle")
}

// The findCycleFrom function follows the path backwards from the node idx
// looking for a cycle. If the node is not contained in a cycle, this panics.
func (thr BF) findCycleFrom(idx Node, stats *stats.Stats) (ret Cycle) {
	// Implement tortise and hare
	slow := idx
	fast := idx
	for {
		stats.TheorySolverLoops++
		slow = *thr.nodes[slow].Predecessor
		fast = *thr.nodes[*thr.nodes[fast].Predecessor].Predecessor
		if slow == fast {
			return thr.findCycleAt(slow, stats)
		}
	}
}

// The findCycleAt function finds a cycle containing the node idx. If that node
// is not contained in a cycle, this infinite loops.
func (thr BF) findCycleAt(idx Node, stats *stats.Stats) (ret Cycle) {
	// Create the backing array for the cycle.
	ret = make([]Node, 0, thr.numVar)
	// Follow the predecessors until we find a repeat.
	cur := idx
	for {
		stats.TheorySolverLoops++
		ret = append(ret, cur)
		cur = *thr.nodes[cur].Predecessor
		if cur == idx {
			break
		}
	}
	// Remember to reverse the list. We expect edges in the forward direction,
	// but we traverse reverse edges in this method.
	for i, j := 0, len(ret)-1; i < j; i, j = i+1, j-1 {
		ret[i], ret[j] = ret[j], ret[i]
	}
	return
}
