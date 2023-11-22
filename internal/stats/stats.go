// The stats package exposes a structure to keep track of statistics for a
// solver run.
package stats

import (
	"fmt"
	"time"
)

// The Stats struct stores statistics for one run.
type Stats struct {
	// The csv member reports whether the statistics should be printed in CSV
	// format. If this is unset, they are printed in human-readable format.
	csv bool

	// The IngestDuration member records how long it took to parse the file and
	// convert it to CNF.
	IngestDuration time.Duration
	// The PreprocessDuration member records how long preprocessing takes if
	// enabled.
	PreprocessDuration time.Duration
	// The SATSolverDuration member records the amount of time spent in the SAT
	// solver.
	SATSolverDuration time.Duration
	// The TheorySolverDuration member recrods the amount of time spent in the
	// theory solver.
	TheorySolverDuration time.Duration

	// The GraphOverheadDuration member records the amount of time taken to
	// construct the constraint graph.
	GraphOverheadDuration time.Duration
	// The LearnOverheadDuration member records how long it tooks to learn new
	// clauses from cycles.
	LearnOverheadDuration time.Duration

	// The SolverCalls member records how many times the SAT solver was
	// invoked. The number of times the theory solver was invoked is the same.
	SolverCalls uint64
	// The TheorySolverLoops member records how many O(1) loops took place
	// inside the theory solver. The precise meaning of this field will differ
	// depending on the solver.
	TheorySolverLoops uint64
}

// The New function creates a new [Stats] instance, with the specified method of
// printing.
func New(csv bool) Stats { return Stats{csv: csv} }

// The String implementation for [Stats] dumps the statistics. The result is
// either in human-readable format, or in CSV if the csv member is set.
func (stats Stats) String() string {
	if stats.csv {
		return fmt.Sprintf(
			"%d,%d,%d,%d,%d,%d,%d,%d",
			stats.IngestDuration.Nanoseconds(),
			stats.PreprocessDuration.Nanoseconds(),
			stats.SATSolverDuration.Nanoseconds(),
			stats.TheorySolverDuration.Nanoseconds(),
			stats.GraphOverheadDuration.Nanoseconds(),
			stats.LearnOverheadDuration.Nanoseconds(),
			stats.SolverCalls,
			stats.TheorySolverLoops,
		)
	} else {
		return fmt.Sprintf(
			"Statistics:\n"+
				"  Ingest = %v\n"+
				"  Preprocess = %v\n"+
				"  SAT = %v\n"+
				"  Theory = %v\n"+
				"  Graph Overhead = %v\n"+
				"  Learn Overhead = %v\n"+
				"  Calls = %d\n"+
				"  Loops = %d",
			stats.IngestDuration,
			stats.PreprocessDuration,
			stats.SATSolverDuration,
			stats.TheorySolverDuration,
			stats.GraphOverheadDuration,
			stats.LearnOverheadDuration,
			stats.SolverCalls,
			stats.TheorySolverLoops,
		)
	}
}
