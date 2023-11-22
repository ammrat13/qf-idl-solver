package theory

import (
	"errors"
	"math/big"

	"github.com/gammazero/deque"
)

// BF is an implementation of the Bellman-Ford theory solver. It uses SPFA under
// the hood, with amortized parent graph search for negative cycle detection.
type BF struct {
	// The number of variables in this problem instance.
	numVar uint

	// The nodes field consists of all the metadata we keep on a per-node basis.
	// The index corresponds to the node number.
	nodes []nodeData
	// The queue field represents the queue we use for SPFA.
	queue *deque.Deque[Node]
}

func (thr *BF) SetNumVar(numVar uint) { thr.numVar = numVar }

// A nodeState describes the different states a vertex can be in in the
// unlabeled / labeled / scanned paradigm. The Bellman-Ford algorithm only uses
// the labeled and scanned states.
type nodeState int

const (
	nodeStateLabeled nodeState = iota
	nodeStateScanned
)

// A nodeData struct holds all the bookkeeping infomation we keep on a
// per-vertex basis.
type nodeData struct {

	// The State of a node reflects whether or not it is in the queue. If it is,
	// the state is [nodeStateLabeled], otherwise it is [nodeStateScanned].
	State nodeState

	// The Distance field is the current label of the node. It is always an
	// upper-bound on the true distance to the node.
	Distance *big.Int

	// The Predecessor field indicates the node before this one in the shortest
	// path. A nil predecessor means this is a root in the forest.
	Predecessor *Node

	// The Depth field indicates how many nodes were before this one in the
	// shortest path. This is equivalent to the number of edges.
	Depth uint
}

func (thr *BF) Solve(graph AdjacencyList) (ret Cycle, err error) {

	// Create the auxiliary structures.
	thr.nodes = make([]nodeData, thr.numVar)
	thr.queue = deque.New[Node]()

	// Initialize the nodes at depth zero.
	for i := range thr.nodes {
		zero := big.NewInt(0)
		thr.nodes[i] = nodeData{
			State:       nodeStateLabeled,
			Distance:    zero,
			Predecessor: nil,
			Depth:       0,
		}
	}
	// Add all the nodes to the queue.
	for i := range thr.nodes {
		thr.queue.PushBack(uint(i))
	}

	for thr.queue.Len() != 0 {

		// Consider edges from the node at the front of the queue
		uIdx := thr.queue.PopFront()
		uDat := &thr.nodes[uIdx]
		// Look at all the outgoing edges.
		for vIdx, edge := range graph[uIdx] {
			vDat := &thr.nodes[vIdx]

			// Mark this vertex as scanned since it's no longer in the queue.
			uDat.State = nodeStateScanned

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
				vDat.Depth = uDat.Depth + 1

				// If the new depth is too much, die
				if vDat.Depth >= thr.numVar {
					return thr.findCycleFrom(vIdx), nil
				}
			}
		}
	}

	// Couldn't find anything
	return Cycle{}, errors.New("no negative cycle")
}

// The findCycleFrom function follows the path backwards from the node idx
// looking for a cycle. If the node is not contained in a cycle, this panics.
func (thr BF) findCycleFrom(idx Node) (ret Cycle) {
	// Implement tortise and hare
	slow := idx
	fast := idx
	for {
		slow = *thr.nodes[slow].Predecessor
		fast = *thr.nodes[*thr.nodes[fast].Predecessor].Predecessor
		if slow == fast {
			return thr.findCycleAt(slow)
		}
	}
}

// The findCycleAt function finds a cycle containing the node idx. If that node
// is not contained in a cycle, this infinite loops.
func (thr BF) findCycleAt(idx Node) (ret Cycle) {
	// Create the backing array for the cycle.
	ret = make([]Node, 0, thr.numVar)
	// Follow the predecessors until we find a repeat.
	cur := idx
	for {
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
