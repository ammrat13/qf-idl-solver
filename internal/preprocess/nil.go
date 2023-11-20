package preprocess

import (
	"github.com/ammrat13/qf-idl-solver/internal/db"
)

// The Nil preprocessor does nothing.
type Nil struct{}

func (Nil) Preprocess(db *db.DB) {}
