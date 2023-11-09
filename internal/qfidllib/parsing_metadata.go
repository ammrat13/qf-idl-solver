package qfidllib

import (
	"errors"
)

// Wrapper to express whether a particular instance is satisfiable or not. This
// is the general way Golang does enums, it seems.
type Status int

const (
	UNSAT   = 0
	SAT     = 1
	UNKNOWN = -1
)

func (stat *Status) Capture(values []string) error {
	// We should always get exactly one value, so panic if this doesn't happen
	if len(values) != 1 {
		panic("Should have gotten exactly one value")
	}
	// Switch on the value we got, and notify the user if they put something
	// invalid.
	switch value := values[0]; value {
	case "sat":
		fallthrough
	case "|sat|":
		*stat = SAT
		return nil
	case "unsat":
		fallthrough
	case "|unsat|":
		*stat = UNSAT
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
	Source Symbol `'(' "set-info":Symbol ":source":Attribute @Symbol ')'`
}

type MetadataLicense struct {
	License StringLit `'(' "set-info":Symbol ":license":Attribute @StringLit ')'`
}

type MetadataCategory struct {
	Category StringLit `'(' "set-info":Symbol ":category":Attribute @StringLit ')'`
}

type MetadataStatus struct {
	Status Status `'(' "set-info":Symbol ":status":Attribute @Symbol ')'`
}

type MetadataNotes struct {
	Notes Symbol `'(' "set-info":Symbol ":notes":Attribute @Symbol ')'`
}

func (m MetadataSource) metadata()   {}
func (m MetadataLicense) metadata()  {}
func (m MetadataCategory) metadata() {}
func (m MetadataStatus) metadata()   {}
func (m MetadataNotes) metadata()    {}
