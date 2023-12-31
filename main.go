package main

import (
	"fmt"
	"os"
	"sync"
	"time"

	"github.com/alecthomas/participle/v2"
	"github.com/ammrat13/qf-idl-solver/internal/config"
	"github.com/ammrat13/qf-idl-solver/internal/db"
	"github.com/ammrat13/qf-idl-solver/internal/file"
	"github.com/ammrat13/qf-idl-solver/internal/stats"
	"github.com/ammrat13/qf-idl-solver/internal/theory"
)

// The ParseErrorExit value is the exit code when this program fails to parse an
// input file.
const ParseErrorExit = 3

// The DatabaseConstructionErrorExit is the exit code when this program fails to
// construct the clause database from an input file that was parsed correctly.
const DatabaseConstructionErrorExit = 4

// The HardTimeoutExit is the exit code for when solving times out and we kill
// ourselves.
const HardTimeoutExit = 5

func main() {

	// Parse command-line arguments. Do the associated setup, then log what we
	// got for debugging.
	cfg := config.GetConfiguration()

	// Keep track of statistics for this solver run. Also create a mutex so we
	// don't print the statistics twice.
	stats := stats.New(cfg.CSVStats)
	printMutex := sync.Mutex{}
	printResult := func(res string) {
		printMutex.Lock()
		defer printMutex.Unlock()
		if cfg.PrintStats {
			fmt.Println(stats)
		} else {
			fmt.Println(res)
		}
	}

	// Parse the input file.
	t_ingest_start := time.Now()
	ast, err := file.Parse(cfg.Input)
	if err != nil {
		if erp, ok := err.(participle.Error); ok {
			// Check if the error was from participle.
			fmt.Fprintf(
				os.Stderr,
				"failed to parse at :%d:%d: %s\n",
				erp.Position().Line,
				erp.Position().Column,
				erp.Message(),
			)
		} else {
			// Otherwise, treat it like a normal error.
			fmt.Fprintf(os.Stderr, "failed to parse: %s\n", err.Error())
		}
		// In either case, exit with error.
		os.Exit(ParseErrorExit)
	}

	// Convert it to CNF.
	db, err := db.FromFile(*ast)
	if err != nil {
		fmt.Fprintf(os.Stderr, "failed to construct database: %s\n", err.Error())
		os.Exit(DatabaseConstructionErrorExit)
	}
	t_ingest_end := time.Now()
	stats.IngestDuration = t_ingest_end.Sub(t_ingest_start)

	// Run preprocessing.
	t_preproc_start := time.Now()
	cfg.Preprocessor.Preprocess(&db)
	t_preproc_end := time.Now()
	stats.PreprocessDuration = t_preproc_end.Sub(t_preproc_start)

	// Run a goroutine to kill us on hard timeout. Only do this if we were in
	// fact supplied a timeout.
	if cfg.HardTimeout > 0 {
		go func() {
			// Wait for the hard timeout
			time.Sleep(cfg.HardTimeout)
			// Print results and die
			printResult("unknown")
			os.Exit(HardTimeoutExit)
		}()
	}

	// Solve. Make sure we get the right status. Ignore unknowns.
	status := theory.Solve(&db, cfg.Solver, cfg.SoftTimeout, &stats)
	if status != file.StatusUnknown {
		if expected := ast.GetStatus(); expected != file.StatusUnknown {
			if expected != status {
				panic("Solver returned wrong answer")
			}
		}
	}

	// Print the result. Make sure we only print once.
	printResult(status.String())
}
