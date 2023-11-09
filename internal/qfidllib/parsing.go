package qfidllib

import (
	"github.com/alecthomas/participle/v2"
)

// This variable defines the parser we will use on QFIDL-LIB input streams. Note
// the unions. These have to be declared here and below.
var theParser = participle.MustBuild[File](
	participle.UseLookahead(2),
	participle.Lexer(theLexer),
	participle.Union[Metadata](
		MetadataSource{},
		MetadataLicense{},
		MetadataCategory{},
		MetadataStatus{},
		MetadataNotes{},
	),
)

// The File struct represents the root of the AST. It contains file metadata,
// along with all the declarations and assertions.
type File struct {

	// The Version field describes the version number declared in the file. This
	// is ignored, but it may be useful in the future.
	Version Version `parser:"'(' CmdSetInfo AttrVersion @VersionNum ')'"`
	// The Logic field gives the logic the file was written with. We only
	// support QF_IDL, and we reject anything that doesn't declare that type at
	// parse-time.
	Logic Symbol `parser:"'(' CmdSetLogic @Symbol ')'"`

	// This holds all the metadata entries given in the file. These correspond
	// to all the attributes we declared in the lexer, minus the version.
	Metadata []Metadata `parser:"@@*"`

	// This array holds all of the assertions for the solver, as they are given
	// in the AST. Its grammar also captures the check-sat and exit commands.
	Assertions []Assertion `parser:"@@* '(' CmdCheckSat ')' '(' CmdExit ')'"`
}
