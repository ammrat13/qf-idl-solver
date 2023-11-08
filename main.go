package main

import (
	"log"

	"github.com/ammrat13/qf-idl-solver/internal/config"
	"github.com/ammrat13/qf-idl-solver/internal/qfidllib"
)

func main() {

	// Parse command-line arguments
	cfg := config.GetConfiguration()
	log.Printf("Got configuration: %v\n", cfg)

	// Parse the input file
	_ = qfidllib.Parse(&cfg)
}
