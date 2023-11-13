package main

import (
	"fmt"
	"log"
	"os"

	"github.com/alecthomas/participle/v2"
	"github.com/ammrat13/qf-idl-solver/internal/config"
	"github.com/ammrat13/qf-idl-solver/internal/db"
	"github.com/ammrat13/qf-idl-solver/internal/file"
)

// The ParseErrorExit value is the exit code when this program fails to parse an
// input file.
const ParseErrorExit = 3

// The DatabaseConstructionErrorExit is the exit code when this program fails to
// construct the clause database from an input file that was parsed correctly.
const DatabaseConstructionErrorExit = 4

func main() {

	// Parse command-line arguments. Do the associated setup, then log what we
	// got for debugging.
	cfg := config.GetConfiguration()
	cfg.SetupLogging()
	log.Printf("Got configuration: %v\n", cfg)

	// Parse the input file.
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
			fmt.Fprintln(os.Stderr, err.Error())
		}
		// In either case, exit with error.
		os.Exit(ParseErrorExit)
	}
	log.Printf("Got AST: %v\n", ast)

	// Convert it to CNF.
	db, err := db.FromFile(*ast)
	if err != nil {
		fmt.Fprintf(
			os.Stderr,
			"failed to construct database from '%s': %s\n",
			cfg.InputName,
			err.Error(),
		)
		os.Exit(DatabaseConstructionErrorExit)
	}
	log.Printf("Got DB: %v\n", db)
}
