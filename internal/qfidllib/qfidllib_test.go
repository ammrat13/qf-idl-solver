package qfidllib

import (
	"io/fs"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// The BenchmarkPath is the relative path to the benchmarks from the directory
// the tests are run. This should be bench/.
const BenchmarkPath = "../../bench/"

func TestBenchmarkParsing(t *testing.T) {

	// Find all of the benchmark files
	filepath.Walk(BenchmarkPath, func(path string, info fs.FileInfo, err error) error {

		// It's fine if we couldn't walk into a directory. Just continue looking
		// at the other directories.
		if err != nil {
			return nil
		}
		// We don't care about directories, only files. We also only care about
		// SMT-LIB files.
		if info.IsDir() || !strings.HasSuffix(info.Name(), ".smt2") {
			return nil
		}

		t.Run(path, func(t *testing.T) {
			t.Parallel()

			// Try to open the file.
			bench, err := os.Open(path)
			if err != nil {
				t.SkipNow()
			}

			// Try to parse.
			ret, err := theParser.Parse(path, bench)

			// Check for errors.
			if err != nil {
				t.Errorf("parse error: %v", err)
			}
			if ret.Logic != "QF_IDL" {
				t.Error("bad logic")
			}
			if !ret.Footer {
				t.Error("no footer")
			}
		})
		return nil
	})
}

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
			(assert true)
			(assert false)
			(assert x)
			(assert |x|)
			(assert (> (- x y) 0))
			(assert (>= (- x y) (- 0)))
			(assert (= x y))
			(assert (distinct x y))
			(check-sat)
			(exit)
		`),
		"not": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(assert (not x))
			(assert (not (not x)))
			(assert (not (distinct x y)))
			(assert (not (>= (- x y) (- 5))))
			(check-sat)
			(exit)
		`),
		"ite": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(assert (ite x y z))
			(assert (ite (not x) y (distinct x y)))
			(check-sat)
			(exit)
		`),
		"equality": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(assert (= x y z))
			(assert (distinct x y z))
			(assert (= x (>= (- y z) 5)))
			(check-sat)
			(exit)
		`),
		"operations": []byte(`
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
			ret, err := theParser.ParseBytes("TEST", test)
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

func TestStatusParsing(t *testing.T) {
	tests := map[string]struct {
		data   []byte
		status Status
	}{
		"sat_simple": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status sat)
			(check-sat)
			(exit)
		`), status: StatusSat},
		"sat_complex": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status |sat|)
			(check-sat)
			(exit)
		`), status: StatusSat},
		"unsat_simple": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status unsat)
			(check-sat)
			(exit)
		`), status: StatusUnsat},
		"unsat_complex": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status |unsat|)
			(check-sat)
			(exit)
		`), status: StatusUnsat},
	}

	for name, test := range tests {
		test := test
		t.Run(name, func(t *testing.T) {
			t.Parallel()

			// Try to parse. We don't use the wrapped parse method since it
			// exits on failure.
			ret, err := theParser.ParseBytes("TEST", test.data)
			// Check that the parse actually succeeded
			if err != nil {
				t.Error("parser returned error")
			}
			// Check that the status was parsed correctly. This means it has the
			// correct type and that its value is correct.
			if len(ret.Metadata) == 0 {
				t.Error("did not get any metadata")
			}
			status, ok := ret.Metadata[0].(MetadataStatus)
			if !ok {
				t.Error("got bad metadata type")
			}
			if status.Status != test.status {
				t.Error("incorrect parse")
			}
		})
	}
}

func TestSymbolParsing(t *testing.T) {
	tests := map[string]struct {
		data  []byte
		value string
	}{
		"simple": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :source ammrat13)
			(check-sat)
			(exit)
		`), value: `ammrat13`},
		"complex_basic": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :source |ammrat13|)
			(check-sat)
			(exit)
		`), value: `ammrat13`},
		"complex": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :source |a b c < "def""|)
			(check-sat)
			(exit)
		`), value: `a b c < "def""`},
	}

	for name, test := range tests {
		test := test
		t.Run(name, func(t *testing.T) {
			t.Parallel()

			// Try to parse. We don't use the wrapped parse method since it
			// exits on failure.
			ret, err := theParser.ParseBytes("TEST", test.data)
			// Check that the parse actually succeeded
			if err != nil {
				t.Error("parser returned error")
			}
			// Check that the source was parsed correctly. This means it has the
			// correct type and that its value is correct.
			if len(ret.Metadata) == 0 {
				t.Error("did not get any metadata")
			}
			source, ok := ret.Metadata[0].(MetadataSource)
			if !ok {
				t.Error("got bad metadata type")
			}
			if source.Source != Symbol(test.value) {
				t.Error("incorrect parse")
			}
		})
	}
}

func TestStringParsing(t *testing.T) {
	tests := map[string]struct {
		data  []byte
		value string
	}{
		"simple": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :license "abc")
			(check-sat)
			(exit)
		`), value: `abc`},
		"empty": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :license "")
			(check-sat)
			(exit)
		`), value: ``},
		"escape": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :license "abc""def""")
			(check-sat)
			(exit)
		`), value: `abc"def"`},
	}

	for name, test := range tests {
		test := test
		t.Run(name, func(t *testing.T) {
			t.Parallel()

			// Try to parse. We don't use the wrapped parse method since it
			// exits on failure.
			ret, err := theParser.ParseBytes("TEST", test.data)
			// Check that the parse actually succeeded
			if err != nil {
				t.Error("parser returned error")
			}
			// Check that the source was parsed correctly. This means it has the
			// correct type and that its value is correct.
			if len(ret.Metadata) == 0 {
				t.Error("did not get any metadata")
			}
			license, ok := ret.Metadata[0].(MetadataLicense)
			if !ok {
				t.Error("got bad metadata type")
			}
			if license.License != StringLit(test.value) {
				t.Error("incorrect parse")
			}
		})
	}
}

func TestEqualityParsing(t *testing.T) {
	atoms := map[string][]byte{
		"equality": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(assert (= x y))
			(check-sat)
			(exit)
		`),
		"inequality": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(assert (distinct x y))
			(check-sat)
			(exit)
		`),
	}
	builders := map[string][]byte{
		"equality": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(assert (= x y z))
			(check-sat)
			(exit)
		`),
		"inequality": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(assert (distinct x y z))
			(check-sat)
			(exit)
		`),
		"complex_equality": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(assert (= x (= y z)))
			(check-sat)
			(exit)
		`),
		"complex_inequality": []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(assert (distinct x (>= (- y z) (- 5))))
			(check-sat)
			(exit)
		`),
	}

	// Check that simple equality expressions are parsed as atoms.
	for name, test := range atoms {
		test := test
		t.Run(name, func(t *testing.T) {
			t.Parallel()

			// Try to parse. We don't use the wrapped parse method since it
			// exits on failure.
			ret, err := theParser.ParseBytes("TEST", test)
			// Check that the parse actually succeeded
			if err != nil {
				t.Error("parser returned error")
			}
			// Check that the equality was parsed as an atom.
			if len(ret.Assertions) == 0 {
				t.Error("did not get any assertions")
			}
			_, ok := ret.Assertions[0].(EqualityAtom)
			if !ok {
				t.Error("got bad equality type")
			}
		})
	}

	// Check that complex equality expressions are parsed as builders.
	for name, test := range builders {
		test := test
		t.Run(name, func(t *testing.T) {
			t.Parallel()

			// Try to parse. We don't use the wrapped parse method since it
			// exits on failure.
			ret, err := theParser.ParseBytes("TEST", test)
			// Check that the parse actually succeeded
			if err != nil {
				t.Error("parser returned error")
			}
			// Check that the equality was parsed as a builder.
			if len(ret.Assertions) == 0 {
				t.Error("did not get any assertions")
			}
			_, ok := ret.Assertions[0].(EqualityBuilder)
			if !ok {
				t.Error("got bad equality type")
			}
		})
	}
}
