#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

# GeneratedPosetConjectures.lean is checked in as a static data fixture.
# No dynamic generation is needed; the python/ scripts that previously
# produced it have been deprecated (see deprecated/python/).

echo "Lean tests: OK"
