// This script dumps the lexer in lexing.go. It outputs the JSON to standard
// output.

//go:build ignore

package main

import (
	"encoding/json"
	"fmt"

	"github.com/ammrat13/qf-idl-solver/internal/file"
)

func main() {
	ret, err := json.Marshal(file.Lexer)
	if err != nil {
		panic("Couldn't serialize lexer")
	}

	fmt.Printf("%s", ret)
}
