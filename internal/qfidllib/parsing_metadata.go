package qfidllib

import (
	"errors"
)

// Status is a wrapper to express whether a particular instance is satisfiable
// or not. This is the general way Golang does enums, it seems.
type Status int

const (
	StatusUnsat   = Status(0)
	StatusSat     = Status(1)
	StatusUnknown = Status(-1)
)

func (stat Status) String() string {
	switch stat {
	case StatusUnsat:
		return "unsat"
	case StatusSat:
		return "sat"
	default:
		return "unknown"
	}
}

func (stat *Status) Capture(values []string) error {
	// We should always get exactly one value, so panic if this doesn't happen
	if len(values) != 1 {
		panic("Should have gotten exactly one value")
	}
	// Switch on the value we got, and notify the user if they put something
	// invalid.
	switch value := values[0]; value {
	case "unsat":
		fallthrough
	case "|unsat|":
		*stat = StatusUnsat
		return nil
	case "sat":
		fallthrough
	case "|sat|":
		*stat = StatusSat
		return nil
	default:
		return errors.New(":status should be either sat or unsat")
	}
}

// The Metadata interface models the possible annotations on QFIDL-LIB files.
// These correspond to a limited set of the annotations on SMT-LIB files,
// meaning:
//   - :source with [MetadataSource]
//   - :license with [MetadataLicense]
//   - :category with [MetadataCategory]
//   - :status with [MetadataStatus]
//   - :notes with [MetadataNotes]
type Metadata interface {
	metadata()
}

//go-sumtype:decl Metadata

type MetadataSource struct {
	Source Symbol `parser:"'(':ParenOpen 'set-info':Symbol ':source':Attribute @Symbol ')':ParenClose"`
}
type MetadataLicense struct {
	License StringLit `parser:"'(':ParenOpen 'set-info':Symbol ':license':Attribute @StringLit ')':ParenClose"`
}
type MetadataCategory struct {
	Category StringLit `parser:"'(':ParenOpen 'set-info':Symbol ':category':Attribute @StringLit ')':ParenClose"`
}
type MetadataStatus struct {
	Status Status `parser:"'(':ParenOpen 'set-info':Symbol ':status':Attribute @Symbol ')':ParenClose"`
}
type MetadataNotes struct {
	Notes Symbol `parser:"'(':ParenOpen 'set-info':Symbol ':notes':Attribute @Symbol ')':ParenClose"`
}

func (m MetadataSource) metadata()   {}
func (m MetadataLicense) metadata()  {}
func (m MetadataCategory) metadata() {}
func (m MetadataStatus) metadata()   {}
func (m MetadataNotes) metadata()    {}
