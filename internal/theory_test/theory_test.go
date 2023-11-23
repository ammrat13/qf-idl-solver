package theory_test

import (
	"math"
	"math/big"
	"testing"

	"github.com/ammrat13/qf-idl-solver/internal/stats"
	"github.com/ammrat13/qf-idl-solver/internal/theory"
)

// The fuzzTheory function takes in a theory solver and checks that it behaves
// consistently. Specifically, it checks that it doesn't return a negative cycle
// when all the weights are positive, and it checks that all the negative cycles
// returned are in fact negative. Note that this is not a complete correctness
// specification.
func fuzzTheory(f *testing.F, thr theory.Solver) {

	f.Add([]byte("\x00\x00\x00\x00"), false)
	f.Add([]byte("\x80\x80\x80\x80"), false)
	f.Add([]byte("\x00\x00\x00\x00"), true)
	f.Add([]byte("\xff\xff\xff\x00"), true)

	f.Fuzz(func(t *testing.T, graphData []byte, shift bool) {

		// We have N**2 edges, each represented by a byte. Thus, we must compute
		// how many vertices we have.
		N := uint(math.Floor(math.Sqrt(float64(len(graphData)))))
		if N <= 0 {
			return
		}

		// Construct the graph by iterating over every possible pair of
		// vertices.
		adjList := make(theory.AdjacencyList)
		for i := uint(0); i < N; i++ {
			adjList[i] = make(map[theory.Node]theory.Edge)
			for j := uint(0); j < N; j++ {
				// Compute the weight depending on the shift.
				weight := int64(graphData[i*N+j])
				if shift {
					weight -= 128
				}
				// Add the edge.
				adjList[i][j] = theory.Edge{
					Weight: big.NewInt(weight),
				}
			}
		}

		// Run the theory solver
		t.Log(adjList)
		thr.SetNumVar(N)
		cyc, err := thr.Solve(adjList, &stats.Stats{})

		// If we have no negative edges, we can't possibly have a negative
		// cycle.
		if !shift && err == nil {
			t.Error("found negative cycle when none exists")
		}

		// If we didn't find a negative cycle, we're done.
		if err != nil {
			return
		}

		// Check that the cycle we found is negative.
		total := big.NewInt(0)
		for i := 0; i < len(cyc); i++ {
			j := (i + 1) % len(cyc)
			ni := cyc[i]
			nj := cyc[j]
			total = total.Add(total, adjList[ni][nj].Weight)
		}
		if total.Sign() >= 0 {
			t.Error("returned cycle not negative")
		}
	})
}

func FuzzSPFABasic(f *testing.F) { fuzzTheory(f, &theory.SPFA{BasicMode: true}) }
func FuzzSPFAFull(f *testing.F)  { fuzzTheory(f, &theory.SPFA{BasicMode: false}) }
