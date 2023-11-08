package main

import (
	"log"

	"github.com/ammrat13/qf-idl-solver/internal/config"
)

func main() {
	cfg := config.GetConfiguration()
	log.Printf("Got configuration: %v\n", cfg)
}
