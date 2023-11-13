package file_test

import (
	"testing"

	"github.com/ammrat13/qf-idl-solver/internal/file"
)

func TestBasicParsing(t *testing.T) {
	tests := map[string][]byte{
		"smoke": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(check-sat)
			(exit)
		`),
		"logic": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic |QF_IDL|)
			(check-sat)
			(exit)
		`),
		"symbol_attributes": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :source ammrat13)
			(set-info :source |ammrat13|)
			(set-info :source ./$)
			(set-info :source |a b.c <= "def" "|)
			(set-info :notes ammrat13)
			(check-sat)
			(exit)
		`),
		"string_attributes": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :license "abc")
			(set-info :license "")
			(set-info :license """")
			(set-info :license "abc""def")
			(set-info :category "abc")
			(check-sat)
			(exit)
		`),
		"status_attribute": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status sat)
			(set-info :status |sat|)
			(set-info :status unsat)
			(set-info :status |unsat|)
			(check-sat)
			(exit)
		`),
		"declarations": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(declare-fun x () Bool)
			(declare-fun x () Int)
			(declare-fun |x| () Bool)
			(declare-fun x () |Int|)
			(check-sat)
			(exit)
		`),
		"atoms": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(assert x)
			(assert |x|)
			(assert 5)
			(assert (- 5))
			(assert (- x y))
			(check-sat)
			(exit)
		`),
		"not": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(assert (not x))
			(assert (not (not x)))
			(assert (not (distinct x y)))
			(assert (not (>= x 5)))
			(assert (not (>= x (- 5))))
			(assert (not (>= (- x y) (- 5))))
			(check-sat)
			(exit)
		`),
		"ite": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(assert (ite x y z))
			(assert (ite (not x) y (distinct x y z)))
			(check-sat)
			(exit)
		`),
		"equality": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(assert (= x y))
			(assert (= x y z w))
			(assert (distinct x y z))
			(assert (= x (>= (- y z) 5)))
			(assert (= x (>= (- y z) (- 5))))
			(check-sat)
			(exit)
		`),
		"comparison": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(assert (> x y))
			(assert (<= x 5))
			(assert (<= x (- 5)))
			(assert (>= (- x y) 5))
			(assert (>= (- x y) (- 5)))
			(check-sat)
			(exit)
		`),
		"boolean": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(assert (and x y))
			(assert (and x y z))
			(assert (or x y z))
			(assert (xor x y z))
			(assert (=> x y z))
			(assert (and x (distinct y z w) (>= (- a b) 5)))
			(check-sat)
			(exit)
		`),
		"let": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(assert (let ((x y) (z w)) k))
			(assert (let ((x y) (z w)) (>= (- a b) 5)))
			(check-sat)
			(exit)
		`),
	}

	for name, test := range tests {
		test := test
		t.Run(name, func(t *testing.T) {
			t.Parallel()

			// Try to parse. We don't use the wrapped parse method since it
			// exits on failure.
			ret, err := file.Parser.ParseBytes("TEST", test)
			// Check that the parse actually succeeded
			if err != nil {
				t.Error("parser returned error")
			}
			// Check that we got the correct logic. This is common to all the
			// tests, so we can check for it
			if ret.Logic != "QF_IDL" {
				t.Error("bad logic")
			}
		})
	}
}
