package qfidllib

import (
	"github.com/alecthomas/participle/v2"
)

// This variable defines the parser we will use on QFIDL-LIB input streams. Note
// the unions. These have to be declared here and below.
var Parser = participle.MustBuild[File](
	participle.UseLookahead(5),
	participle.Lexer(Lexer),
	participle.Union[Metadata](
		MetadataSource{},
		MetadataLicense{},
		MetadataCategory{},
		MetadataStatus{},
		MetadataNotes{},
	),

	// The order here is important. We always want to parse atoms before formula
	// building operators so that valid integer expressions aren't flagged as
	// errors. We also want to parse expressions with specified symbols before
	// those that leave the symbols unspecified. This is because we have
	// operations as just regular symbols, and we don't always check in the
	// grammar rules whether the symbols work.
	participle.Union[Formula](
		LitAtom{},
		VarAtom{},
		EqualityAtom{},
		DiffAtom{},
		NotBuilder{},
		ITEBuilder{},
		LetBuilder{},
		EqualityBuilder{},
		OperationBuilder{},
	),
)

// The File struct represents the root of the AST. It contains file metadata,
// along with all the declarations and assertions.
type File struct {

	// The Version field describes the version number declared in the file. This
	// is ignored, but it may be useful in the future.
	Version Version `parser:"'(':ParenOpen 'set-info':Symbol ':smt-lib-version':Attribute @VersionNum ')':ParenClose"`
	// The Logic field gives the logic the file was written with. We only
	// support QF_IDL, and we will reject anything that doesn't declare that
	// type, even if it is otherwise valid.
	Logic Symbol `parser:"'(':ParenOpen 'set-logic':Symbol @Symbol ')':ParenClose"`

	// This holds all the metadata entries given in the file. These correspond
	// to all the attributes we declared in the lexer, minus the version.
	Metadata []Metadata `parser:"@@*"`

	// This array holds all of the variable delclarations
	Declarations []Declaration `parser:"@@*"`

	// This array holds all of the assertions for the solver, as they are given
	// in the AST.
	Assertions []Formula `parser:"( '(':ParenOpen 'assert':Symbol @@ ')':ParenClose )*"`

	// This flag reports whether a footer was present. The footer is a check-sat
	// command followed by an exit command. The grammar requires that the footer
	// be present, so this will always be true.
	Footer bool `parser:"@('(':ParenOpen 'check-sat':Symbol ')':ParenClose '(':ParenOpen 'exit':Symbol ')':ParenClose)"`
}
