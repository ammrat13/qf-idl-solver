package file_test

import (
	"testing"

	"github.com/ammrat13/qf-idl-solver/internal/file"
)

func TestStatusParsing(t *testing.T) {
	tests := map[string]struct {
		data   []byte
		status file.Status
	}{
		"sat_simple": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status sat)
			(check-sat)
			(exit)
		`), status: file.StatusSat},
		"sat_complex": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status |sat|)
			(check-sat)
			(exit)
		`), status: file.StatusSat},
		"unsat_simple": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status unsat)
			(check-sat)
			(exit)
		`), status: file.StatusUnsat},
		"unsat_complex": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status |unsat|)
			(check-sat)
			(exit)
		`), status: file.StatusUnsat},
	}

	for name, test := range tests {
		test := test
		t.Run(name, func(t *testing.T) {
			t.Parallel()

			// Try to parse. We don't use the wrapped parse method since it
			// exits on failure.
			ret, err := file.Parser.ParseBytes("TEST", test.data)
			// Check that the parse actually succeeded
			if err != nil {
				t.Error("parser returned error")
			}
			// Check that the status was parsed correctly. This means it has the
			// correct type and that its value is correct.
			if len(ret.Metadata) == 0 {
				t.Error("did not get any metadata")
			}
			status, ok := ret.Metadata[0].(file.MetadataStatus)
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
		value file.Symbol
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
			ret, err := file.Parser.ParseBytes("TEST", test.data)
			// Check that the parse actually succeeded
			if err != nil {
				t.Error("parser returned error")
			}
			// Check that the source was parsed correctly. This means it has the
			// correct type and that its value is correct.
			if len(ret.Metadata) == 0 {
				t.Error("did not get any metadata")
			}
			source, ok := ret.Metadata[0].(file.MetadataSource)
			if !ok {
				t.Error("got bad metadata type")
			}
			if source.Source != test.value {
				t.Error("incorrect parse")
			}
		})
	}
}

func TestStringParsing(t *testing.T) {
	tests := map[string]struct {
		data  []byte
		value file.StringLit
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
			ret, err := file.Parser.ParseBytes("TEST", test.data)
			// Check that the parse actually succeeded
			if err != nil {
				t.Error("parser returned error")
			}
			// Check that the source was parsed correctly. This means it has the
			// correct type and that its value is correct.
			if len(ret.Metadata) == 0 {
				t.Error("did not get any metadata")
			}
			license, ok := ret.Metadata[0].(file.MetadataLicense)
			if !ok {
				t.Error("got bad metadata type")
			}
			if license.License != test.value {
				t.Error("incorrect parse")
			}
		})
	}
}

func TestCmpArgument(t *testing.T) {

	t.Run("diff", func(t *testing.T) {
		t.Parallel()

		tests := map[string][]byte{
			"sym+": []byte(`
				(set-info :smt-lib-version 2.6)
				(set-logic QF_IDL)
				(assert (>= x 5))
				(check-sat)
				(exit)
			`),
			"sym-": []byte(`
				(set-info :smt-lib-version 2.6)
				(set-logic QF_IDL)
				(assert (>= x (- 5)))
				(check-sat)
				(exit)
			`),
			"diff+": []byte(`
				(set-info :smt-lib-version 2.6)
				(set-logic QF_IDL)
				(assert (>= (- x y) 5))
				(check-sat)
				(exit)
			`),
			"diff-": []byte(`
				(set-info :smt-lib-version 2.6)
				(set-logic QF_IDL)
				(assert (>= (- x y) (- 5)))
				(check-sat)
				(exit)
			`),
		}

		for name, test := range tests {
			test := test
			t.Run(name, func(t *testing.T) {
				t.Parallel()
				var ok bool

				// Try to parse. We don't use the wrapped parse method since it
				// exits on failure.
				ret, err := file.Parser.ParseBytes("TEST", test)
				// Check that the parse actually succeeded
				if err != nil {
					t.Error("parser returned error")
				}
				// Check that the assertion was parsed correctly. This means its
				// comparison argument has the correct type.
				if len(ret.Assertions) == 0 {
					t.Error("did not get any metadata")
				}
				cmp, ok := ret.Assertions[0].(file.CmpOpBuilder)
				if !ok {
					t.Error("got bad assertion type")
				}
				_, ok = cmp.Arguments.(file.CmpDiff)
				if !ok {
					t.Error("incorrect comparison argument type")
				}
			})
		}
	})

	t.Run("sym", func(t *testing.T) {
		t.Parallel()

		tests := map[string][]byte{
			"simple": []byte(`
				(set-info :smt-lib-version 2.6)
				(set-logic QF_IDL)
				(assert (>= x y))
				(check-sat)
				(exit)
			`),
		}

		for name, test := range tests {
			test := test
			t.Run(name, func(t *testing.T) {
				t.Parallel()
				var ok bool

				// Try to parse. We don't use the wrapped parse method since it
				// exits on failure.
				ret, err := file.Parser.ParseBytes("TEST", test)
				// Check that the parse actually succeeded
				if err != nil {
					t.Error("parser returned error")
				}
				// Check that the assertion was parsed correctly. This means its
				// comparison argument has the correct type.
				if len(ret.Assertions) == 0 {
					t.Error("did not get any metadata")
				}
				cmp, ok := ret.Assertions[0].(file.CmpOpBuilder)
				if !ok {
					t.Error("got bad assertion type")
				}
				_, ok = cmp.Arguments.(file.CmpSym)
				if !ok {
					t.Error("incorrect comparison argument type")
				}
			})
		}
	})
}
