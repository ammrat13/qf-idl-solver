package file_test

import (
	"io"
	"strings"
	"testing"

	"github.com/ammrat13/qf-idl-solver/internal/file"
)

func TestStatusParsing(t *testing.T) {
	tests := map[string]struct {
		data   io.Reader
		status file.Status
	}{
		"sat_simple": {data: strings.NewReader(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status sat)
			(check-sat)
			(exit)
		`), status: file.StatusSat},
		"sat_complex": {data: strings.NewReader(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status |sat|)
			(check-sat)
			(exit)
		`), status: file.StatusSat},
		"unsat_simple": {data: strings.NewReader(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status unsat)
			(check-sat)
			(exit)
		`), status: file.StatusUnsat},
		"unsat_complex": {data: strings.NewReader(`
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

			ret, err := file.Parse(test.data)
			if err != nil {
				t.Errorf("parse error: %s", err.Error())
				t.FailNow()
			}

			// Check that the status was parsed correctly. This means it has the
			// correct type and that its value is correct.
			if len(ret.Metadata) == 0 {
				t.Error("did not get any metadata")
			}
			status, ok := ret.Metadata[0].(file.MetadataStatus)
			if !ok {
				t.Error("bad type")
			}
			if status.Status != test.status {
				t.Error("incorrect parse")
			}
		})
	}
}

func TestGetStatus(t *testing.T) {
	tests := map[string]struct {
		data   io.Reader
		status file.Status
	}{
		"sat": {data: strings.NewReader(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status sat)
			(check-sat)
			(exit)
		`), status: file.StatusSat},
		"unsat": {data: strings.NewReader(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status unsat)
			(check-sat)
			(exit)
		`), status: file.StatusUnsat},
		"unknown": {data: strings.NewReader(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status unknown)
			(check-sat)
			(exit)
		`), status: file.StatusUnknown},
		"both": {data: strings.NewReader(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status sat)
			(set-info :status unsat)
			(check-sat)
			(exit)
		`), status: file.StatusSat},
		"neither": {data: strings.NewReader(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(check-sat)
			(exit)
		`), status: file.StatusUnknown},
	}

	for name, test := range tests {
		test := test
		t.Run(name, func(t *testing.T) {
			t.Parallel()

			ret, err := file.Parse(test.data)
			if err != nil {
				t.Errorf("parse error: %s", err.Error())
				t.FailNow()
			}

			// Check that we can get the status of the file correctly.
			if ret.GetStatus() != test.status {
				t.Error("wrong status")
			}
		})
	}
}

func TestSymbolParsing(t *testing.T) {
	tests := map[string]struct {
		data  io.Reader
		value file.Symbol
	}{
		"simple": {data: strings.NewReader(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :source ammrat13)
			(check-sat)
			(exit)
		`), value: `ammrat13`},
		"complex_basic": {data: strings.NewReader(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :source |ammrat13|)
			(check-sat)
			(exit)
		`), value: `ammrat13`},
		"complex": {data: strings.NewReader(`
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

			ret, err := file.Parse(test.data)
			if err != nil {
				t.Errorf("parse error: %s", err.Error())
				t.FailNow()
			}

			// Check that the source was parsed correctly. This means it has the
			// correct type and that its value is correct.
			if len(ret.Metadata) == 0 {
				t.Error("did not get any metadata")
			}
			source, ok := ret.Metadata[0].(file.MetadataSource)
			if !ok {
				t.Error("bad type")
			}
			if source.Source != test.value {
				t.Error("incorrect parse")
			}
		})
	}
}

func TestStringParsing(t *testing.T) {
	tests := map[string]struct {
		data  io.Reader
		value file.StringLit
	}{
		"simple": {data: strings.NewReader(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :license "abc")
			(check-sat)
			(exit)
		`), value: `abc`},
		"empty": {data: strings.NewReader(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :license "")
			(check-sat)
			(exit)
		`), value: ``},
		"escape": {data: strings.NewReader(`
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

			ret, err := file.Parse(test.data)
			if err != nil {
				t.Errorf("parse error: %s", err.Error())
				t.FailNow()
			}

			// Check that the license was parsed correctly. This means it has
			// the correct type and that its value is correct.
			if len(ret.Metadata) == 0 {
				t.Error("did not get any metadata")
			}
			license, ok := ret.Metadata[0].(file.MetadataLicense)
			if !ok {
				t.Error("bad type")
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

		tests := map[string]io.Reader{
			"sym+": strings.NewReader(`
				(set-info :smt-lib-version 2.6)
				(set-logic QF_IDL)
				(assert (>= x 5))
				(check-sat)
				(exit)
			`),
			"sym-": strings.NewReader(`
				(set-info :smt-lib-version 2.6)
				(set-logic QF_IDL)
				(assert (>= x (- 5)))
				(check-sat)
				(exit)
			`),
			"diff+": strings.NewReader(`
				(set-info :smt-lib-version 2.6)
				(set-logic QF_IDL)
				(assert (>= (- x y) 5))
				(check-sat)
				(exit)
			`),
			"diff-": strings.NewReader(`
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

				ret, err := file.Parse(test)
				if err != nil {
					t.Errorf("parser error: %s", err.Error())
					t.FailNow()
				}

				// Check that the assertion was parsed correctly. This means its
				// comparison's argument has the correct type.
				if len(ret.Assertions) == 0 {
					t.Error("did not get any assertions")
				}
				cmp, ok := ret.Assertions[0].(file.CmpOpBuilder)
				if !ok {
					t.Error("bad type")
				}
				_, ok = cmp.Arguments.(file.CmpDiff)
				if !ok {
					t.Error("incorrect type")
				}
			})
		}
	})

	t.Run("sym", func(t *testing.T) {
		t.Parallel()

		tests := map[string]io.Reader{
			"simple": strings.NewReader(`
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

				ret, err := file.Parse(test)
				if err != nil {
					t.Errorf("parser error: %s", err.Error())
					t.FailNow()
				}

				// Check that the assertion was parsed correctly. This means its
				// comparison's argument has the correct type.
				if len(ret.Assertions) == 0 {
					t.Error("did not get any assertions")
				}
				cmp, ok := ret.Assertions[0].(file.CmpOpBuilder)
				if !ok {
					t.Error("bad type")
				}
				_, ok = cmp.Arguments.(file.CmpSym)
				if !ok {
					t.Error("incorrect type")
				}
			})
		}
	})
}
