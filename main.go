package main

import (
	"log"

	"github.com/ammrat13/qf-idl-solver/internal/config"
	"github.com/ammrat13/qf-idl-solver/internal/qfidllib"
)

func main() {

	// Parse command-line arguments. Do the associated setup, then log what we
	// got for debugging.
	cfg := config.GetConfiguration()
	cfg.SetupLogging()
	log.Printf("Got configuration: %v\n", cfg)

	// Parse the input file
	ast := qfidllib.Parse(cfg.Input)
	log.Printf("Got AST: %v\n", ast)
}
