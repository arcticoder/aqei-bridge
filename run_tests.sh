#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT_DIR"

# Explicit quick checks (mirrors docs/TODO.md guidance).
(cd "$ROOT_DIR/lean" && lake build)

if command -v wolframscript >/dev/null 2>&1; then
	wolframscript -file "$ROOT_DIR/mathematica/search.wl" --test-mode
elif command -v wolfram >/dev/null 2>&1; then
	wolfram -script "$ROOT_DIR/mathematica/search.wl" --test-mode
else
	echo "ERROR: neither wolframscript nor wolfram found on PATH" >&2
	exit 1
fi

python -m unittest discover -q tests/

bash tests/python_tests.sh
bash tests/mathematica_tests.sh
bash tests/lean_tests.sh

echo "All tests: OK"
