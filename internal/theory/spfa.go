package theory

import (
	"errors"
	"math/big"

	"github.com/ammrat13/qf-idl-solver/internal/stats"
	"github.com/gammazero/deque"
)

// SPFA is an implementation of the Bellman-Ford theory solver. It uses SPFA
// under the hood, with amortized parent graph search for negative cycle
// detection.
type SPFA struct {
	// The BasicMode field disables amortized parent graph search.
	BasicMode bool

	// The number of variables in this problem instance.
	numVar uint

	// The graph field is the input graph we're checking for negative cycles
	// for. It always has numVar nodes numbered 0 to numVar-1.
	graph AdjacencyList

	// The nodes field consists of all the metadata we keep on a per-node basis.
	// The index corresponds to the node number.
	nodes []spfaNodeData
	// The queue field represents the queue we use for SPFA.
	queue *deque.Deque[Node]
}

func (thr *SPFA) SetNumVar(numVar uint) { thr.numVar = numVar }
func (thr SPFA) Copy() Solver           { return &SPFA{BasicMode: thr.BasicMode, numVar: thr.numVar} }

// An spfaNodeData struct holds all the bookkeeping infomation we keep on a
// per-vertex basis.
type spfaNodeData struct {

	// The State of a node reflects whether or not it is in the queue. If it is,
	// the state is [nodeStateLabeled], otherwise it is [nodeStateScanned].
	State nodeState

	// The Distance field is the current label of the node. It is always an
	// upper-bound on the true distance to the node.
	Distance *big.Int

	// The Predecessor field indicates the node before this one in the shortest
	// path. A nil predecessor means this is a root in the forest.
	Predecessor *Node

	// The Relaxations field indicates how many times this node has been popped
	// from the queue. A node can only be popped so many times before
	// participating in a cycle.
	Relaxations uint
}

func (thr *SPFA) Solve(graph AdjacencyList, stats *stats.Stats) (ret Cycle, err error) {

	// Create the auxiliary structures.
	thr.graph = graph
	thr.nodes = make([]spfaNodeData, thr.numVar)
	thr.queue = deque.New[Node](int(thr.numVar))
	ZERO := big.NewInt(0)

	// Initialize the nodes at distance zeor with no relaxations.
	for i := range thr.nodes {
		thr.nodes[i] = spfaNodeData{
			State:       nodeStateLabeled,
			Distance:    ZERO,
			Predecessor: nil,
			Relaxations: 0,
		}
	}
	// Add all the nodes to the queue.
	for i := range thr.nodes {
		thr.queue.PushBack(Node(i))
	}

	var iteration uint = 0
	for thr.queue.Len() != 0 {
		// Consider edges from the node at the front of the queue
		uIdx := thr.queue.PopFront()
		uDat := &thr.nodes[uIdx]

		// Mark this vertex as scanned since it's no longer in the queue.
		uDat.State = nodeStateScanned

		// With Bellman-Ford, relaxations can only occur n-1 times before we
		// know a cycle exists. Therefore, break if we've relaxed a node more
		// than that. Note that the number of times a node has been dequeued is
		// a lower bound on the number of "passes" we've done.
		if uDat.Relaxations >= thr.numVar {
			return thr.findCycleFrom(uIdx, stats), nil
		}
		uDat.Relaxations++

		// Look at all the outgoing edges.
		for vIdx, edge := range thr.graph[uIdx] {
			vDat := &thr.nodes[vIdx]
			stats.TheorySolverLoops++

			// Compute the new distance to the node. Check if it's less than the
			// current label.
			vDist := new(big.Int).Add(uDat.Distance, edge.Weight)
			if vDist.Cmp(vDat.Distance) == -1 {

				// Enqueue depending on the state.
				if vDat.State != nodeStateLabeled {
					thr.queue.PushBack(vIdx)
				}
				// Set the new state.
				vDat.State = nodeStateLabeled
				vDat.Distance = vDist
				vDat.Predecessor = &uIdx
			}

			// Amortized parent graph search. Do this in the inner loop since
			// inner loops are O(1).
			if !thr.BasicMode {
				if iteration >= thr.numVar {
					nd, err := thr.parentGraphSearch(stats)
					if err == nil {
						return thr.findCycleAt(nd, stats), nil
					}
					iteration = 0
				} else {
					iteration++
				}
			}
		}
	}

	// Couldn't find anything
	return Cycle{}, errors.New("no negative cycle")
}

// The findCycleFrom function follows the path backwards from the node idx
// looking for a cycle. If the node is not contained in a cycle, this panics.
func (thr SPFA) findCycleFrom(idx Node, stats *stats.Stats) Cycle {
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
func (thr SPFA) findCycleAt(idx Node, stats *stats.Stats) (ret Cycle) {
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

// The parentGraphSearch function tries to find a cycle by following the
// predecessors of each node. If it can find one, it returns a node in the
// cycle. Otherwise, it returns an error.
func (thr SPFA) parentGraphSearch(stats *stats.Stats) (ret Node, err error) {

	// Node colors keep track of what state a node is in. Initially, all nodes
	// are white for unexplored. When we enter, we set it to gray to mark that
	// we're currently exploring. When we exit, we set it to black to mark that
	// we're done.
	type nodeColor int
	const (
		nodeColorWhite nodeColor = iota
		nodeColorGray
		nodeColorBlack
	)

	// Create an array to store the colors of each node. Initially, all are
	// white.
	nodeColorArray := make([]nodeColor, thr.numVar)

	// This helper function goes up toward the root starting at a node, marking
	// the intermediate steps as grey. If there is a cycle starting at that
	// node, this will return a node that's part of the cycl4e.
	search := func(cur Node) (Node, error) {
		for {
			stats.TheorySolverLoops++
			// Break into cases on the current node's color
			switch nodeColorArray[cur] {
			case nodeColorBlack:
				return 0, errors.New("no cycle")
			case nodeColorGray:
				return cur, nil
			case nodeColorWhite:
				nodeColorArray[cur] = nodeColorGray
				if pred := thr.nodes[cur].Predecessor; pred != nil {
					cur = *pred
				} else {
					return 0, errors.New("no cycle")
				}
			}
		}
	}
	// This helper function marks everything along a path as having no cycles.
	finalize := func(cur Node) {
		for {
			stats.TheorySolverLoops++
			// Early termination
			if nodeColorArray[cur] == nodeColorBlack {
				return
			}
			// Normal path
			nodeColorArray[cur] = nodeColorBlack
			if pred := thr.nodes[cur].Predecessor; pred != nil {
				cur = *pred
			} else {
				return
			}
		}
	}

	// Search every vertex to check for a cycle.
	for i := Node(0); i < thr.numVar; i++ {
		ret, err = search(i)
		if err == nil {
			return
		} else {
			finalize(i)
		}
	}
	return 0, errors.New("no cycle")
}
