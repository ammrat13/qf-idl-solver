// Package db is the internal representation of a QF_IDL formula in CNF. It
// takes in the AST and converts it using Tseiten's transformation, adding the
// clauses to the database. It also provides facilities to query atoms and to
// add new clauses.
package db

import (
	"math/big"

	"github.com/go-air/gini"
	"github.com/go-air/gini/z"
)

// A DB is a database consisting of all the asserted clauses in CNF, along with
// all of the atoms. An atom is either a boolean variable, represented by an
// integer identifier or a difference constraint, represented by a
// [DifferenceConstraint].
//
// The DB doesn't store any information about the names of the variables. It
// instead uses numeric identifiers, which are assigned in order. This way, we
// know for example how many verticies to have in the constraint graph.
type DB struct {

	// The Clauses variable stores the CNF form of what we want to satisfy. It's
	// represented by an instance of the SAT solver we will use. Call
	// [GetSolution] to get a solution to the clauses, which may not be theory
	// consistent.
	Clauses *gini.Gini

	// The NextAtom field reads one more than how many atoms have been created.
	// It is also the value of the next atom to be created.
	NextAtom int
	// The NextVariable field reads how many variables have been created. It is
	// also the value of the next variable to be created.
	NextVariable uint64

	// The AtomIDToDiff map goes from atom identifiers to [DifferenceConstraint]
	// in the problem. If an ID doesn't show up in the domain, it has no
	// [DifferenceConstraint] associated with it, and it's just a boolean.
	//
	// Note that there is no way to go the other way. This is because difference
	// constraints use big integers, which are not comparable.
	AtomID2Diff map[AtomID]*DifferenceConstraint
}

// The AddClauses method adds a set of clauses to the solver. We wrap this
// method because there's some plumbing.
func (db *DB) AddClauses(clauses ...[]Lit) {
	for _, clause := range clauses {
		for _, lit := range clause {
			db.Clauses.Add(z.Dimacs2Lit(lit))
		}
		db.Clauses.Add(0)
	}
}

// The AtomID type represents an identifier for an atom, whether that be a
// boolean variable or a difference constraint. It must be strictly positive.
type AtomID = int

// An Lit is either an AtomID or its negation. Positive numbers represent
// positive literals, while negative numbers represent negative literals, just
// like in DIMACS format. Zero is not allowed.
type Lit = int

// The ToAtomID function takes in a [Lit] and converts it to its corresponding
// [AtomID], checking for zero just in case.
func ToAtomID(l Lit) AtomID {
	// Check that we didn't get zero
	if l == 0 {
		panic("Got zero literal")
	}
	// Otherwise, return the absolute value
	if l < 0 {
		return -l
	} else {
		return l
	}
}

// The NewAtom method creates a new [AtomID] for use in clauses.
func (db *DB) newAtom() (ret AtomID) {
	// Do bounds checking.
	if db.NextAtom < 1 {
		panic("Too many atoms")
	}
	// Return and increment. It's fine if this overflows since we'll catch it on
	// the next one.
	ret = db.NextAtom
	db.NextAtom = db.NextAtom + 1
	return
}

// VariableIDs are assigned to each symbol of sort Int. These are used by
// [DifferenceConstraint] to keep track of which variables take part in the
// constraint.
type VariableID = uint64

// A VariablePair is an ordered pair of two variables. These are used by the
// [DB] to store difference constraints by the variables they reference.
type VariablePair struct {
	Fst VariableID
	Snd VariableID
}

// The NewVariable method creates a new [VariableID] for use in
// [DifferenceConstraint].
func (db *DB) newVariable() (ret VariableID) {
	// Compute the return value and increment. This may overflow
	ret = db.NextVariable
	db.NextVariable = db.NextVariable + 1
	// Panic if it overflowed, otherwise return
	if db.NextVariable == 0 {
		panic("Too many variables")
	}
	return
}

// A DifferenceConstraint is an atom of this type. It has the form x <= y + k,
// where x and y are variables from the instance, and k is a constant. The other
// type of atom is a boolean atom, which is either true or false.
type DifferenceConstraint struct {
	X VariableID
	Y VariableID
	K *big.Int
}

// The makeAtomForDiff function takes in a [DifferenceConstraint] and creates an
// [AtomID] corresponding to it. It also does all of the bookkeeping required
// when adding difference constraints.
//
// Note that we create a new value for each constraint. This is because we have
// no good way to look up constraints in a map.
func (db *DB) makeAtomForDiff(c DifferenceConstraint) (ret AtomID) {
	// Create a new atom.
	ret = db.newAtom()
	// Associate it with the given difference constraint.
	db.AtomID2Diff[ret] = &c
	// Done
	return
}
