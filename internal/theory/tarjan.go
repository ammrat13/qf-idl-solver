package theory

import (
	"errors"
	"math/big"

	"github.com/ammrat13/qf-idl-solver/internal/stats"
	"github.com/gammazero/deque"
)

type Tarjan struct {
	// The number of variables in this problem instance.
	numVar uint

	// The graph field is the input graph we're checking for negative cycles
	// for. It always has numVar nodes numbered 0 to numVar-1.
	graph AdjacencyList

	// The nodes field consists of all the metadata we keep on a per-node basis.
	// The index corresponds to the node number.
	nodes []tarjanNodeData
	// The queue field represents the queue we use for Tarjan's algorithm. All
	// the nodes in here are either labeled or unlabeled, and all the other
	// nodes are either scanned or unlabeled.
	queue *deque.Deque[Node]
	// The parentGraph field is an adjacency list for the parent graph during
	// the run. We need this because we need to search over all of a node's
	// children.
	parentGraph map[Node]map[Node]bool
}

func (thr *Tarjan) SetNumVar(numVar uint) { thr.numVar = numVar }
func (thr Tarjan) Copy() Solver           { return &Tarjan{numVar: thr.numVar} }

// An tarjanNodeData struct holds all the bookkeeping infomation we keep on a
// per-vertex basis.
type tarjanNodeData struct {

	// The State of a node is correlated with whether or not it is in the queue.
	// All vertices that are [nodeStateLabeled] are in the queue, while all
	// [nodeStateScanned] vertices are not. Nodes that are [nodeStateUnlabeled]
	// may or may not be in the queue. If an unlabeled node is dequeued, it is
	// skipped.
	State nodeState
	// The InQueue field reports whether a node is in the queue. We need this
	// because the State field doesn't correlate perfectly for unlabeled nodes,
	// and since we don't want to add a vertex to the queue if it's already in
	// there.
	InQueue bool

	// The Distance field is the current label of the node. It is always an
	// upper-bound on the true distance to the node. For nodes that are
	// [nodeStateLabeled], the shortest path can be found by following the
	// predecessors. For nodes that are [nodeStateUnlabeled], that's not the
	// case, but there still exists a path with this distance or less.
	Distance *big.Int

	// The Predecessor field indicates the node before this one in the shortest
	// path. A nil predecessor means this is a root in the forest, or that the
	// node is [nodeStateUnlabeled].
	Predecessor *Node
}

func (thr *Tarjan) Solve(graph AdjacencyList, stats *stats.Stats) (ret Cycle, err error) {

	// Create the auxiliary structures.
	thr.graph = graph
	thr.nodes = make([]tarjanNodeData, thr.numVar)
	thr.queue = deque.New[Node](int(thr.numVar))
	thr.parentGraph = make(map[Node]map[Node]bool)
	ZERO := big.NewInt(0)

	// Initially, all the nodes are labeled, in the queue, and with distance
	// zero.
	for i := range thr.nodes {
		thr.nodes[i] = tarjanNodeData{
			State:    nodeStateLabeled,
			InQueue:  true,
			Distance: ZERO,
		}
	}

	// Add all the vertices to the queue initially.
	for i := range thr.nodes {
		thr.queue.PushBack(Node(i))
	}

	// Loop until we don't have anything else in the queue, in which case there
	// is no negative cycle.
	for thr.queue.Len() != 0 {
		// Consider the node at the front of the queue.
		uIdx := thr.queue.PopFront()
		uDat := &thr.nodes[uIdx]

		// Mark the vertex as no longer in the queue. If it's unlabeled, skip
		// it. Otherwise, scan it.
		uDat.InQueue = false
		if uDat.State == nodeStateUnlabeled {
			continue
		} else {
			uDat.State = nodeStateScanned
		}

		// Try to relax all outgoing edges of the scanned vertex.
		for vIdx, edge := range thr.graph[uIdx] {
			vDat := &thr.nodes[vIdx]
			stats.TheorySolverLoops++

			// Compute the new distance to the node. Check if it's less than the
			// current label.
			vDist := new(big.Int).Add(uDat.Distance, edge.Weight)
			if vDist.Cmp(vDat.Distance) == -1 {

				// Disassemble the subtree starting at v. This may result in us
				// discovering a cycle, so handle that.
				ret, err = thr.disassemble(vIdx, vIdx, uIdx, stats)
				if err == nil {
					return
				}

				// Update v's distance.
				vDat.Distance = vDist

				// Reparent v to us and mark it as labeled.
				if vDat.Predecessor != nil {
					delete(thr.parentGraph[*vDat.Predecessor], vIdx)
				}
				if thr.parentGraph[uIdx] == nil {
					thr.parentGraph[uIdx] = make(map[Node]bool)
				}
				thr.parentGraph[uIdx][vIdx] = true
				vDat.Predecessor = &uIdx
				vDat.State = nodeStateLabeled
				// Add v to the queue if it isn't already
				if !vDat.InQueue {
					thr.queue.PushBack(vIdx)
					vDat.InQueue = true
				}
			}
		}
	}

	// Couldn't find anything
	return Cycle{}, errors.New("no negative cycle")
}

// The disassemble method removes uIdx and all its children from the parent
// graph. If toIdx is found during this process, a cycle is returned that starts
// at fromIdx and goes to toIdx - for this we require fromIdx be adjacent to
// toIdx.
func (thr Tarjan) disassemble(uIdx Node, fromIdx Node, toIdx Node, stats *stats.Stats) (ret Cycle, err error) {

	// If our target node is the node we're looking for, return the cycle.
	if uIdx == toIdx {
		ret = make([]Node, 0)
		// Follow the parents from to until we get to from.
		cur := toIdx
		for cur != fromIdx {
			stats.TheorySolverLoops++
			ret = append(ret, cur)
			cur = *thr.nodes[fromIdx].Predecessor
		}
		ret = append(ret, fromIdx)
		// Remember to reverse.
		for i, j := 0, len(ret)-1; i < j; i, j = i+1, j-1 {
			ret[i], ret[j] = ret[j], ret[i]
		}
		return
	}

	// Otherwise, disassemble all our children.
	for vIdx := range thr.parentGraph[uIdx] {
		stats.TheorySolverLoops++
		thr.disassemble(vIdx, fromIdx, toIdx, stats)
	}
	// Get rid of all our children and mark us as unlabeled.
	thr.parentGraph[uIdx] = nil
	thr.nodes[uIdx].State = nodeStateUnlabeled
	return Cycle{}, errors.New("no negative cycle")
}
