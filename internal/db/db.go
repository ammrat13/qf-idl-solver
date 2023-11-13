// Package db is the internal representation of a QF_IDL formula in CNF. It
// takes in the AST and converts it using Tseiten's transformation. Once built,
// it provides facilities to query the database, as well as augment it with
// newly discovered blocking clauses.
package db

import (
	"math/big"
)

// A DB is a database consisting of all the asserted clauses in CNF. Each
// boolean variable in the CNF is an atom, which is either a difference
// constraint or a boolean variable.
//
// We only store IDs for all the atoms, even though we store difference
// constraints in full. This is because we have to generate boolean constraints
// on the fly.
type DB struct {

	// The Clauses variable stores the CNF form of what we want to satisfy.
	Clauses [][]AtomLit

	// The id2diff map goes from atom identifiers to [DifferenceAtom] in the
	// problem. If an ID doesn't show up in the domain, it has no
	// [DifferenceAtom] associated with it, and it's just a boolean.
	id2diff map[AtomID]DifferenceAtom
	// The diff2id map goes in the opposite direction from [id2diff]. If a
	// [DifferenceAtom] doesn't show up in the domain, it has no associated ID.
	diff2id map[DifferenceAtom]AtomID

	// The next boolean variable we will create. This is incremented every time
	// we request one, and is always positive.
	nextAtomID AtomID
}

func (db *DB) getNewAtom() AtomID {
	// Do bounds checking
	if db.nextAtomID < 1 {
		panic("Next atom is out of range; maybe overflow")
	}
	// Return and increment
	ret := db.nextAtomID
	db.nextAtomID = db.nextAtomID + 1
	return ret
}

// A DifferenceAtom is an atom that is a difference constraint. It has the form
// x <= y + k, where x and y are variables from the instance, and k is a
// constant. The other type of atom is a boolean atom, which is either true or
// false.
type DifferenceAtom struct {
	X string
	Y string
	K *big.Int
}

// The AtomID type represents an identifier for an atom, whether that be a
// boolean variable or a difference constraint. It must be strictly positive.
type AtomID int

// An AtomLit is either an AtomID or its negation. We alias it to int since that
// is what we will feed into the SAT solver.
type AtomLit = int

// The Positive function returns an [AtomLit] corresponding to the positive
// version of the input [AtomID]
func (i AtomID) Positive() AtomLit {
	// Return ourselves
	ret := int(i)
	// We shouldn't ever get a non-positive number on the input.
	if ret <= 0 {
		panic("Got non-positive ID")
	}
	// Otherwise return
	return ret
}

// The Negative method is just like Positive, except that it returns the
// negation of this variable.
func (i AtomID) Negative() AtomLit {
	// Return the negation of ourselves
	ret := -int(i)
	// We shouldn't ever get a non-positive number on the input.
	if ret >= 0 {
		panic("Got non-positive ID")
	}
	// Otherwise return
	return ret
}

func ToAtomID(l AtomLit) AtomID {
	// The return value is the positive of the literal
	if l < 0 {
		l = -l
	}
	// Check that we didn't get zero
	if l == 0 {
		panic("Got zero literal")
	}
	// Otherwise return
	return AtomID(l)
}
