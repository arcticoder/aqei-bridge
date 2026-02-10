#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT_DIR"

bash tests/python_tests.sh
bash tests/mathematica_tests.sh
bash tests/lean_tests.sh

echo "All tests: OK"
