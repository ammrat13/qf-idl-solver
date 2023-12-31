package file_test

import (
	"io/fs"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/ammrat13/qf-idl-solver/internal/file"
)

// The BenchmarkPath is the relative path to the benchmarks from the directory
// the tests are run. This should be bench/.
const BenchmarkPath = "../../bench/"

func TestBenchmarkParsing(t *testing.T) {

	// This test takes a long time to run
	if testing.Short() {
		t.SkipNow()
	}

	// Find all of the benchmark files
	filepath.Walk(BenchmarkPath, func(path string, info fs.FileInfo, err error) error {

		// It's fine if we couldn't walk into a directory. Just continue looking
		// at the other directories.
		if err != nil {
			return nil
		}
		// We don't care about directories, only files. We also only care about
		// SMT-LIB files.
		if info.IsDir() || !strings.HasSuffix(info.Name(), ".smt2") {
			return nil
		}

		t.Run(path, func(t *testing.T) {
			t.Parallel()

			bench, err := os.Open(path)
			if err != nil {
				t.SkipNow()
			}

			_, err = file.Parse(bench)
			if err != nil {
				t.Errorf("parse error: %s", err.Error())
			}
		})
		return nil
	})
}
