package file

import (
	"errors"
	"strconv"
	"strings"
)

// The Version struct documents what library version the input file was written
// with. It has the format N.M, and it implements the Capture interface to parse
// that string to integers.
type Version struct {
	Major uint64
	Minor uint64
}

func (v *Version) Capture(values []string) error {

	// We should've gotten exactly one value, so panic if that isn't the case
	if len(values) != 1 {
		panic("Should have gotten exactly one value")
	}
	// The value should be of the form N.M, so split on periods and check we got
	// the right number of components.
	value := values[0]
	components := strings.Split(value, ".")
	if len(components) != 2 {
		panic("Version number should have exactly two components")
	}

	// Parse each component individually, and die if we can't. First the major
	// component.
	var errMaj error
	v.Major, errMaj = strconv.ParseUint(components[0], 10, 64)
	if errMaj != nil {
		// Check if we're actually out of range. If we are, that's a user error
		// and not a panic
		if errMaj.(*strconv.NumError).Err == strconv.ErrRange {
			return errors.New("major version " + components[0] + " is out-of-range")
		}
		// Otherwise, it's on us
		panic("Could not parse integer")
	}
	// Then the minor in the same way.
	var errMin error
	v.Minor, errMin = strconv.ParseUint(components[1], 10, 64)
	if errMin != nil {
		if errMin.(*strconv.NumError).Err == strconv.ErrRange {
			return errors.New("minor version " + components[1] + " is out-of-range")
		}
		panic("Could not parse integer")
	}

	return nil
}
