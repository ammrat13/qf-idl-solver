// The preprocess package consists of all the preprocessing operations we can
// do. In the proposal, preprocessing was optional, but that is not the case
// now. We should at least apply the transitivity rule so that we can use binary
// search on the clauses if we want to in the future.
package preprocess

import (
	"github.com/ammrat13/qf-idl-solver/internal/db"
)

// The Preprocessor interface has a single method that applies preprocessing to
// a [db.DB] of clauses. It's allowed to add extra clauses, but it should leave
// all the other variables untouched.
type Preprocessor interface {
	Preprocess(*db.DB)
}

// The Preprocessors variable stores a map from strings to the [Preprocessor]
// they are associated with. We use this map when processing command-line
// arguments.
var Preprocessors = map[string]Preprocessor{
	"nil":   Nil{},
	"trans": Trans{},
}
