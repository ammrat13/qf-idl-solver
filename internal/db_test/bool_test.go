package db_test

import (
	"bytes"
	"reflect"
	"slices"
	"strings"
	"testing"

	"github.com/ammrat13/qf-idl-solver/internal/db"
	"github.com/ammrat13/qf-idl-solver/internal/file"
)

func TestBool(t *testing.T) {
	tests := map[string]struct {
		ast     file.File
		clauses []string
	}{
		"empty": {
			ast: file.File{},
			clauses: []string{
				"1 0",
				"-2 0",
			},
		},
		"pos": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortBool},
				},
				Assertions: []file.Expr{
					file.SymbolAtom{Name: file.Symbol("x")},
				},
			},
			clauses: []string{
				"1 0",
				"-2 0",
				"3 0",
			},
		},
		"not": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortBool},
				},
				Assertions: []file.Expr{
					file.NotBuilder{
						Argument: file.SymbolAtom{Name: file.Symbol("x")},
					},
				},
			},
			clauses: []string{
				"1 0",
				"-2 0",
				"-3 0",
			},
		},
		"ite": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortBool},
					{Name: file.Symbol("y"), Sort: file.SortBool},
					{Name: file.Symbol("z"), Sort: file.SortBool},
				},
				Assertions: []file.Expr{
					file.ITEBuilder{
						If:   file.SymbolAtom{Name: file.Symbol("x")},
						Then: file.SymbolAtom{Name: file.Symbol("y")},
						Else: file.SymbolAtom{Name: file.Symbol("z")},
					},
				},
			},
			clauses: []string{
				"1 0",
				"-2 0",
				"6 0",
				"-3 -4 6 0",
				"-3 4 -6 0",
				"3 -5 6 0",
				"3 5 -6 0",
			},
		},
		"implies": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortBool},
					{Name: file.Symbol("y"), Sort: file.SortBool},
				},
				Assertions: []file.Expr{
					file.BoolOpBuilder{
						Operation: file.BoolOpIMP,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("y")},
						},
					},
				},
			},
			clauses: []string{
				"1 0",
				"-2 0",
				"5 0",
				"-3 4 -5 0",
				"3 5 0",
				"-4 5 0",
			},
		},
		"and": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortBool},
					{Name: file.Symbol("y"), Sort: file.SortBool},
				},
				Assertions: []file.Expr{
					file.BoolOpBuilder{
						Operation: file.BoolOpAND,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("y")},
						},
					},
				},
			},
			clauses: []string{
				"1 0",
				"-2 0",
				"5 0",
				"-3 -4 5 0",
				"3 -5 0",
				"4 -5 0",
			},
		},
		"or": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortBool},
					{Name: file.Symbol("y"), Sort: file.SortBool},
				},
				Assertions: []file.Expr{
					file.BoolOpBuilder{
						Operation: file.BoolOpOR,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("y")},
						},
					},
				},
			},
			clauses: []string{
				"1 0",
				"-2 0",
				"5 0",
				"3 4 -5 0",
				"-3 5 0",
				"-4 5 0",
			},
		},
		"xor": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortBool},
					{Name: file.Symbol("y"), Sort: file.SortBool},
				},
				Assertions: []file.Expr{
					file.BoolOpBuilder{
						Operation: file.BoolOpXOR,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("y")},
						},
					},
				},
			},
			clauses: []string{
				"1 0",
				"-2 0",
				"5 0",
				"3 4 -5 0",
				"3 -4 5 0",
				"-3 4 5 0",
				"-3 -4 -5 0",
			},
		},
		"equals": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortBool},
					{Name: file.Symbol("y"), Sort: file.SortBool},
				},
				Assertions: []file.Expr{
					file.EquOpBuilder{
						Operation: file.EquOpEQ,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("y")},
						},
					},
				},
			},
			clauses: []string{
				"1 0",
				"-2 0",
				"5 0",
				"3 4 5 0",
				"3 -4 -5 0",
				"-3 4 -5 0",
				"-3 -4 5 0",
			},
		},
		"distinct": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortBool},
					{Name: file.Symbol("y"), Sort: file.SortBool},
				},
				Assertions: []file.Expr{
					file.EquOpBuilder{
						Operation: file.EquOpNE,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("y")},
						},
					},
				},
			},
			clauses: []string{
				"1 0",
				"-2 0",
				"5 0",
				"3 4 -5 0",
				"3 -4 5 0",
				"-3 4 5 0",
				"-3 -4 -5 0",
			},
		},
	}

	for name, test := range tests {
		test := test
		t.Run(name, func(t *testing.T) {
			t.Parallel()

			ret, err := db.FromFile(test.ast)
			if err != nil {
				t.Errorf("construction error: %s", err.Error())
				t.FailNow()
			}

			var dimacs bytes.Buffer
			err = ret.Clauses.Write(&dimacs)
			if err != nil {
				t.Errorf("failed to write DIMACS")
				t.FailNow()
			}

			act := strings.Split(dimacs.String(), "\n")[1:]
			act = act[:len(act)-1]
			slices.Sort(act)

			exp := test.clauses
			slices.Sort(exp)

			if !reflect.DeepEqual(act, exp) {
				t.Errorf("DIMACS did not match, got %v", dimacs.String())
			}
		})
	}
}

func TestSat(t *testing.T) {
	tests := map[string]struct {
		ast file.File
		sat int
	}{
		"empty": {
			ast: file.File{},
			sat: 1,
		},
		"contr": {
			ast: file.File{
				Assertions: []file.Expr{
					file.SymbolAtom{Name: file.Symbol("false")},
				},
			},
			sat: -1,
		},
		"not": {
			ast: file.File{
				Assertions: []file.Expr{
					file.NotBuilder{
						Argument: file.SymbolAtom{Name: file.Symbol("false")},
					},
				},
			},
			sat: 1,
		},
		"not_not": {
			ast: file.File{
				Assertions: []file.Expr{
					file.NotBuilder{
						Argument: file.NotBuilder{
							Argument: file.SymbolAtom{Name: file.Symbol("false")},
						},
					},
				},
			},
			sat: -1,
		},
		"ite_true": {
			ast: file.File{
				Assertions: []file.Expr{
					file.ITEBuilder{
						If:   file.SymbolAtom{Name: file.Symbol("true")},
						Then: file.SymbolAtom{Name: file.Symbol("true")},
						Else: file.SymbolAtom{Name: file.Symbol("false")},
					},
				},
			},
			sat: 1,
		},
		"ite_false": {
			ast: file.File{
				Assertions: []file.Expr{
					file.ITEBuilder{
						If:   file.SymbolAtom{Name: file.Symbol("false")},
						Then: file.SymbolAtom{Name: file.Symbol("true")},
						Else: file.SymbolAtom{Name: file.Symbol("false")},
					},
				},
			},
			sat: -1,
		},
		"implies_true": {
			ast: file.File{
				Assertions: []file.Expr{
					file.BoolOpBuilder{
						Operation: file.BoolOpIMP,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("false")},
						},
					},
				},
			},
			sat: -1,
		},
		"implies_false": {
			ast: file.File{
				Assertions: []file.Expr{
					file.BoolOpBuilder{
						Operation: file.BoolOpIMP,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("false")},
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("false")},
						},
					},
				},
			},
			sat: 1,
		},
		"and_true": {
			ast: file.File{
				Assertions: []file.Expr{
					file.BoolOpBuilder{
						Operation: file.BoolOpAND,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("true")},
						},
					},
				},
			},
			sat: 1,
		},
		"and_false": {
			ast: file.File{
				Assertions: []file.Expr{
					file.BoolOpBuilder{
						Operation: file.BoolOpAND,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("false")},
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("true")},
						},
					},
				},
			},
			sat: -1,
		},
		"or_true": {
			ast: file.File{
				Assertions: []file.Expr{
					file.BoolOpBuilder{
						Operation: file.BoolOpOR,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("false")},
							file.SymbolAtom{Name: file.Symbol("false")},
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("false")},
							file.SymbolAtom{Name: file.Symbol("false")},
						},
					},
				},
			},
			sat: 1,
		},
		"or_false": {
			ast: file.File{
				Assertions: []file.Expr{
					file.BoolOpBuilder{
						Operation: file.BoolOpAND,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("false")},
							file.SymbolAtom{Name: file.Symbol("false")},
							file.SymbolAtom{Name: file.Symbol("false")},
							file.SymbolAtom{Name: file.Symbol("false")},
							file.SymbolAtom{Name: file.Symbol("false")},
						},
					},
				},
			},
			sat: -1,
		},
		"xor_true": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortBool},
					{Name: file.Symbol("y"), Sort: file.SortBool},
				},
				Assertions: []file.Expr{
					file.BoolOpBuilder{
						Operation: file.BoolOpXOR,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("y")},
							file.SymbolAtom{Name: file.Symbol("y")},
							file.SymbolAtom{Name: file.Symbol("y")},
						},
					},
				},
			},
			sat: 1,
		},
		"xor_false": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortBool},
					{Name: file.Symbol("y"), Sort: file.SortBool},
				},
				Assertions: []file.Expr{
					file.BoolOpBuilder{
						Operation: file.BoolOpXOR,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("y")},
							file.SymbolAtom{Name: file.Symbol("y")},
							file.SymbolAtom{Name: file.Symbol("y")},
							file.SymbolAtom{Name: file.Symbol("y")},
						},
					},
				},
			},
			sat: -1,
		},
		"equals_true_true": {
			ast: file.File{
				Assertions: []file.Expr{
					file.EquOpBuilder{
						Operation: file.EquOpEQ,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("true")},
						},
					},
				},
			},
			sat: 1,
		},
		"equals_true_false": {
			ast: file.File{
				Assertions: []file.Expr{
					file.EquOpBuilder{
						Operation: file.EquOpEQ,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("false")},
							file.SymbolAtom{Name: file.Symbol("false")},
							file.SymbolAtom{Name: file.Symbol("false")},
							file.SymbolAtom{Name: file.Symbol("false")},
						},
					},
				},
			},
			sat: 1,
		},
		"equals_false": {
			ast: file.File{
				Assertions: []file.Expr{
					file.EquOpBuilder{
						Operation: file.EquOpEQ,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("false")},
							file.SymbolAtom{Name: file.Symbol("true")},
							file.SymbolAtom{Name: file.Symbol("false")},
							file.SymbolAtom{Name: file.Symbol("false")},
						},
					},
				},
			},
			sat: -1,
		},
		"distinct_true": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortBool},
					{Name: file.Symbol("y"), Sort: file.SortBool},
				},
				Assertions: []file.Expr{
					file.EquOpBuilder{
						Operation: file.EquOpNE,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("y")},
						},
					},
				},
			},
			sat: 1,
		},
		"distinct_false": {
			ast: file.File{
				Declarations: []file.Declaration{
					{Name: file.Symbol("x"), Sort: file.SortBool},
					{Name: file.Symbol("y"), Sort: file.SortBool},
					{Name: file.Symbol("z"), Sort: file.SortBool},
				},
				Assertions: []file.Expr{
					file.EquOpBuilder{
						Operation: file.EquOpNE,
						Arguments: []file.Expr{
							file.SymbolAtom{Name: file.Symbol("x")},
							file.SymbolAtom{Name: file.Symbol("y")},
							file.SymbolAtom{Name: file.Symbol("z")},
						},
					},
				},
			},
			sat: -1,
		},
	}

	for name, test := range tests {
		test := test
		t.Run(name, func(t *testing.T) {
			t.Parallel()

			ret, err := db.FromFile(test.ast)
			if err != nil {
				t.Errorf("construction error: %s", err.Error())
				t.FailNow()
			}

			if ret.Clauses.Solve() != test.sat {
				t.Errorf("wrong satisfiability")
			}
		})
	}
}
