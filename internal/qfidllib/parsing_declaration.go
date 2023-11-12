package qfidllib

import "errors"

// Sort is an enumeration of all the sorts we support, specifically Bool and
// Int.
type Sort int

const (
	SortBool = iota
	SortInt
)

func (sort Sort) String() string {
	switch sort {
	case SortBool:
		return "Bool"
	case SortInt:
		return "Int"
	default:
		panic("Invalid sort")
	}
}

func (sort *Sort) Capture(values []string) error {
	// We should always get exactly one value, so panic if this doesn't happen
	if len(values) != 1 {
		panic("Should have gotten exactly one value")
	}
	// Switch on the value we got, and notify the user if they put something
	// invalid.
	switch value := values[0]; value {
	case "Bool":
		fallthrough
	case "|Bool|":
		*sort = SortBool
		return nil
	case "Int":
		fallthrough
	case "|Int|":
		*sort = SortInt
		return nil
	default:
		return errors.New("sort should be either Bool or Int")
	}
}

// The Declaration struct represents a variable declaration in a QFIDL-LIB file.
// It can be declares with declare-const or declare-fun, and it can have sort
// either Bool or Int.
type Declaration struct {
	Name Symbol `parser:"'(':ParenOpen ( 'declare-fun':Symbol @Symbol '(':ParenOpen ')':ParenClose | 'declare-const':Symbol @Symbol )"`
	Sort Sort   `parser:"@Symbol ')':ParenClose"`
}
