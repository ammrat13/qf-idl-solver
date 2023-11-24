package theory_test

import (
	"math"
	"math/big"
	"testing"

	"github.com/ammrat13/qf-idl-solver/internal/stats"
	"github.com/ammrat13/qf-idl-solver/internal/theory"
)

// The fuzzConsistency function takes in a theory solver and checks that it
// behaves consistently. Specifically, it checks that it doesn't return a
// negative cycle when all the weights are positive, and it checks that all the
// negative cycles returned are in fact negative. Note that this is not a
// complete correctness specification.
func fuzzConsistency(f *testing.F, th theory.Solver) {
	f.Add([]byte("\x00\x00\x00\x00"), false)
	f.Add([]byte("\x80\x80\x80\x80"), false)
	f.Add([]byte("\x00\x00\x00\x00"), true)
	f.Add([]byte("\xff\xff\xff\x00"), true)

	f.Fuzz(func(t *testing.T, adjListData []byte, shift bool) {

		// Construct the graph. If we were instructed to shift, do that.
		var bias int64
		if shift {
			bias = -128
		} else {
			bias = 0
		}
		n, adjList := parseAdjList(adjListData, bias)
		if n == 0 {
			return
		}

		// Run the theory solver
		thr := th.Copy()
		thr.SetNumVar(n)
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

// The fuzzGold function checs that the given theory solver behaves the same as
// the gold model, which is raw Bellman-Ford. It doesn't need to report the same
// negative cycle, but it needs to agree about whether there is a negative cycle.
func fuzzGold(f *testing.F, th theory.Solver) {
	f.Add([]byte("\x00\x00\x00\x00"))
	f.Add([]byte("\x80\x80\x80\x80"))
	f.Add([]byte("\xff\xff\xff\x00"))

	f.Fuzz(func(t *testing.T, adjListData []byte) {

		// Construct the graph.
		n, adjList := parseAdjList(adjListData, -128)
		if n == 0 {
			return
		}

		// Run the theory solver
		thr := th.Copy()
		thr.SetNumVar(n)
		cycThr, errThr := thr.Solve(adjList, &stats.Stats{})

		// Run the gold model.
		gold := theory.BF{BasicMode: true}
		gold.SetNumVar(n)
		_, errGold := gold.Solve(adjList, &stats.Stats{})

		// Check that they agree
		if (errThr == nil) != (errGold == nil) {
			t.Error("theory and gold disagree")
		}

		// If we found a negative cycle...
		if errThr != nil {
			return
		}
		// ... check that it is negative.
		total := big.NewInt(0)
		for i := 0; i < len(cycThr); i++ {
			j := (i + 1) % len(cycThr)
			ni := cycThr[i]
			nj := cycThr[j]
			total = total.Add(total, adjList[ni][nj].Weight)
		}
		if total.Sign() >= 0 {
			t.Error("returned cycle not negative")
		}
	})
}

// The parseAdjList function takes in a sequence of bytes and returns a graph
// constructed from them. It creates as many nodes as it can, then applies the
// weights given in the bytestream, shifted by the bias.
func parseAdjList(adjListData []byte, bias int64) (n uint, adjList theory.AdjacencyList) {

	// We have n**2 edges, each represented by a byte. Thus, we must compute how
	// many vertices we have.
	n = uint(math.Floor(math.Sqrt(float64(len(adjListData)))))

	// Construct the graph by iterating over every possible pair of
	// vertices.
	adjList = make(theory.AdjacencyList)
	for i := theory.Node(0); i < n; i++ {
		adjList[i] = make(map[theory.Node]theory.Edge)
		for j := theory.Node(0); j < n; j++ {
			// Compute the weight depending on the bias.
			weight := int64(adjListData[i*n+j]) + bias
			// Add the edge.
			adjList[i][j] = theory.Edge{
				Weight: big.NewInt(weight),
			}
		}
	}
	return
}

func FuzzBFBasic(f *testing.F) { fuzzConsistency(f, &theory.BF{BasicMode: true}) }

func FuzzBFFull(f *testing.F)    { fuzzGold(f, &theory.BF{BasicMode: false}) }
func FuzzSPFABasic(f *testing.F) { fuzzGold(f, &theory.SPFA{BasicMode: true}) }
func FuzzSPFAFull(f *testing.F)  { fuzzGold(f, &theory.SPFA{BasicMode: false}) }
func FuzzGR(f *testing.F)        { fuzzGold(f, &theory.GR{}) }
