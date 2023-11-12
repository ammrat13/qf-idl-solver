package qfidllib_test

import (
	"testing"

	"github.com/ammrat13/qf-idl-solver/internal/qfidllib"
)

func TestStatusParsing(t *testing.T) {
	tests := map[string]struct {
		data   []byte
		status qfidllib.Status
	}{
		"sat_simple": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status sat)
			(check-sat)
			(exit)
		`), status: qfidllib.StatusSat},
		"sat_complex": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status |sat|)
			(check-sat)
			(exit)
		`), status: qfidllib.StatusSat},
		"unsat_simple": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status unsat)
			(check-sat)
			(exit)
		`), status: qfidllib.StatusUnsat},
		"unsat_complex": {data: []byte(`
			(set-info :smt-lib-version 2.6)
			(set-logic QF_IDL)
			(set-info :status |unsat|)
			(check-sat)
			(exit)
		`), status: qfidllib.StatusUnsat},
	}

	for name, test := range tests {
		test := test
		t.Run(name, func(t *testing.T) {
			t.Parallel()

			// Try to parse. We don't use the wrapped parse method since it
			// exits on failure.
			ret, err := qfidllib.Parser.ParseBytes("TEST", test.data)
			// Check that the parse actually succeeded
			if err != nil {
				t.Error("parser returned error")
			}
			// Check that the status was parsed correctly. This means it has the
			// correct type and that its value is correct.
			if len(ret.Metadata) == 0 {
				t.Error("did not get any metadata")
			}
			status, ok := ret.Metadata[0].(qfidllib.MetadataStatus)
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
		value qfidllib.Symbol
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
			ret, err := qfidllib.Parser.ParseBytes("TEST", test.data)
			// Check that the parse actually succeeded
			if err != nil {
				t.Error("parser returned error")
			}
			// Check that the source was parsed correctly. This means it has the
			// correct type and that its value is correct.
			if len(ret.Metadata) == 0 {
				t.Error("did not get any metadata")
			}
			source, ok := ret.Metadata[0].(qfidllib.MetadataSource)
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
		value qfidllib.StringLit
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
			ret, err := qfidllib.Parser.ParseBytes("TEST", test.data)
			// Check that the parse actually succeeded
			if err != nil {
				t.Error("parser returned error")
			}
			// Check that the source was parsed correctly. This means it has the
			// correct type and that its value is correct.
			if len(ret.Metadata) == 0 {
				t.Error("did not get any metadata")
			}
			license, ok := ret.Metadata[0].(qfidllib.MetadataLicense)
			if !ok {
				t.Error("got bad metadata type")
			}
			if license.License != test.value {
				t.Error("incorrect parse")
			}
		})
	}
}
