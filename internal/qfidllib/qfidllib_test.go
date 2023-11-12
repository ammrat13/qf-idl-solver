package qfidllib

import (
	"testing"
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
