package theory

// BF is an implementation of the Bellman-Ford theory solver. It uses SPFA under
// the hood, with amortized parent graph search for negative cycle detection.
type BF struct{}

func (BF) Solve(graph AdjacencyList, numVar uint64) (ret Cycle, err error) {
	panic("TODO")
}
