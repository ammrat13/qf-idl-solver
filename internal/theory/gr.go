package theory

import (
	"errors"
	"math/big"

	"github.com/ammrat13/qf-idl-solver/internal/stats"
)

// The GR struct implements the Goldberg-Radzik algorithm. It uses topological
// sorting to heuristically improve Bellman-Ford, and it uses admissible graph
// search for negative cycle detection.
type GR struct {

	// The number of variables in this problem instance.
	numVar uint

	// The graph field is the input graph we're checking for negative cycles
	// for. It always has numVar nodes numbered 0 to numVar-1.
	graph AdjacencyList

	// The nodes field consists of all the metadata we keep on a per-node basis.
	// The index corresponds to the node number.
	nodes []grNodeData

	// The a field is the list of nodes we will scan on this pass, computed from
	// b and the admissible graph.
	a []Node
	// The b field is the map-set of all the vertices to process on the next
	// pass.
	b map[Node]bool
}

func (thr *GR) SetNumVar(numVar uint) { thr.numVar = numVar }
func (thr GR) Copy() Solver           { return &GR{numVar: thr.numVar} }

// A grNodeData struct holds all the bookkeeping infomation we keep on a
// per-vertex basis.
type grNodeData struct {

	// The State of a node reflects whether or not it is in a set. If it is, the
	// state is [nodeStateLabeled], otherwise it is [nodeStateScanned].
	State nodeState

	// The Distance field is the current label of the node. It is always an
	// upper-bound on the true distance to the node.
	Distance *big.Int
}

func (thr *GR) Solve(graph AdjacencyList, stats *stats.Stats) (ret Cycle, err error) {

	// Create the auxiliary structures.
	thr.graph = graph
	thr.nodes = make([]grNodeData, thr.numVar)
	thr.b = make(map[Node]bool)
	ZERO := big.NewInt(0)

	// Initialize all nodes.
	for i := range thr.nodes {
		thr.nodes[i] = grNodeData{
			State:    nodeStateLabeled,
			Distance: ZERO,
		}
	}

	// Set up the queue.
	for i := Node(0); i < thr.numVar; i++ {
		thr.b[i] = true
	}

	// Main loop. Run passes until the b set is empty.
	for len(thr.b) != 0 {

		// Initialize a. This might lead us to finding a cycle, so report that
		// if needed.
		ret, err = thr.computeAFromB(stats)
		if err == nil {
			return
		}
		// Reset b since it should be emptied at the start of each pass.
		thr.b = make(map[Node]bool)

		// Scan every vertex in a.
		for _, uIdx := range thr.a {
			uDat := &thr.nodes[uIdx]

			// Remember to update the state of u since it's no longer in the
			// queue.
			uDat.State = nodeStateScanned

			// Loop over all the outgoing edges.
			for vIdx, edge := range thr.graph[uIdx] {
				vDat := &thr.nodes[vIdx]
				stats.TheorySolverLoops++

				// Try to relax each edge.
				vDist := new(big.Int).Add(uDat.Distance, edge.Weight)
				if vDist.Cmp(vDat.Distance) == -1 {
					// Only add this vertex to b if it isn't already labeled.
					// This way, we maintain the invariant that each labeled
					// node is in exactly one of a or b.
					if vDat.State != nodeStateLabeled {
						thr.b[vIdx] = true
					}
					// Update the distance and set it as labeled.
					vDat.Distance = vDist
					vDat.State = nodeStateLabeled
				}
			}
		}
	}

	// Couldn't find anything
	return Cycle{}, errors.New("no negative cycle")
}

// The computeAFromB is to be called at the start of each pass. It expects the b
// field of the theory solver to be populated. From that it computes the set of
// nodes reachable from (a culled version of) b into aSet, and from there it
// computes a via topological sort on the admissible graph.
func (thr *GR) computeAFromB(stats *stats.Stats) (_ Cycle, err error) {

	// Step 1: cull all the vertices that cannot possibly seed relaxations.
	for uIdx := range thr.b {
		uDat := &thr.nodes[uIdx]

		// Check if every outgoing edge has d(u) + w(u,v) >= d(v)
		found := false
		for vIdx, edge := range thr.graph[uIdx] {
			vDat := &thr.nodes[vIdx]
			stats.TheorySolverLoops++

			// Do the check.
			vDist := new(big.Int).Add(uDat.Distance, edge.Weight)
			if vDist.Cmp(vDat.Distance) == -1 {
				found = true
				break
			}
		}

		// If that's not the case, cull.
		if !found {
			delete(thr.b, uIdx)
		}
	}

	// Steps 2 and 3: find all the vertices reachable from b in topological sort
	// order. The a list is initially stored in reverse order, but we reverse it
	// at the end.
	//
	// See: https://en.wikipedia.org/wiki/Topological_sorting#Depth-first_search
	thr.a = make([]Node, 0, thr.numVar)

	// Node colors keep track of what state a node is in. White, gray, and black
	// correspond to unmarked, temporarily marked, and permanently marked
	// respectively.
	type nodeColor int
	const (
		nodeColorWhite nodeColor = iota
		nodeColorGray
		nodeColorBlack
	)

	// Create an array to store the colors of each node. Initially, all are
	// white. Also, create an array to store the predecessor of each node in DFS
	// order, initially all nil.
	nodeColorArray := make([]nodeColor, thr.numVar)
	nodePredArray := make([]*Node, thr.numVar)

	// DFS helper function. It takes in the current node for DFS. If there is a
	// cycle, it returns a node that's part of the cycle. Otherwise, it returns
	// an error.
	var helper func(Node) (Node, error)
	helper = func(uIdx Node) (ret Node, err error) {
		uDat := &thr.nodes[uIdx]

		switch nodeColorArray[uIdx] {
		case nodeColorBlack:
			return 0, errors.New("no cycle")
		case nodeColorGray:
			return uIdx, nil

		case nodeColorWhite:
			// Mark ourselves with a temporary mark.
			nodeColorArray[uIdx] = nodeColorGray

			// Iterate over all the outgoing edges.
			for vIdx, edge := range thr.graph[uIdx] {
				vDat := &thr.nodes[vIdx]
				stats.TheorySolverLoops++

				// Filter to edges that are in the admissible graph.
				vDist := new(big.Int).Add(uDat.Distance, edge.Weight)
				if vDist.Cmp(vDat.Distance) == 1 {
					continue
				}

				// Recurse. Make sure to mark the predecessor. If we find a
				// cycle, return it.
				nodePredArray[vIdx] = &uIdx
				ret, err = helper(vIdx)
				if err == nil {
					return
				}
			}

			// Make the mark permanent, add ourselves to the topological sort,
			// and return.
			nodeColorArray[uIdx] = nodeColorBlack
			thr.a = append(thr.a, uIdx)
			return 0, errors.New("no cycle")
		}

		panic("Unhandled case")
	}

	// Run the helper function on all the nodes in b. If we find a cycle, return
	// it.
	for bIdx := range thr.b {
		var cycNode Node
		cycNode, err = helper(bIdx)
		if err == nil {
			return thr.findCycleFrom(nodePredArray, cycNode, stats), nil
		}
	}

	// Remember to reverse the list. We appended during the topological sort,
	// when we should've prepended
	for i, j := 0, len(thr.a)-1; i < j; i, j = i+1, j-1 {
		thr.a[i], thr.a[j] = thr.a[j], thr.a[i]
	}
	return Cycle{}, errors.New("no negative cycle")
}

// The findCycleFrom function follows the path backwards from the node idx
// looking for a cycle in the nodePredArray. If the node is not contained in a
// cycle, this panics.
func (thr GR) findCycleFrom(nodePredArray []*Node, idx Node, stats *stats.Stats) Cycle {
	// Implement tortise and hare
	slow := idx
	fast := idx
	for {
		stats.TheorySolverLoops++
		slow = *nodePredArray[slow]
		fast = *nodePredArray[*nodePredArray[fast]]
		if slow == fast {
			return thr.findCycleAt(nodePredArray, slow, stats)
		}
	}
}

// The findCycleAt function finds a cycle containing the node idx in the
// nodePredArray. If that node is not contained in a cycle, this infinite loops.
func (thr GR) findCycleAt(nodePredArray []*Node, idx Node, stats *stats.Stats) (ret Cycle) {
	// Create the backing array for the cycle.
	ret = make([]Node, 0, thr.numVar)
	// Follow the predecessors until we find a repeat.
	cur := idx
	for {
		stats.TheorySolverLoops++
		ret = append(ret, cur)
		cur = *nodePredArray[cur]
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
