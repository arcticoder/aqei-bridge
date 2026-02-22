#!/usr/bin/env bash
set -euo pipefail
# aqei-bridge test suite: Lean build and typecheck only.
# Numerical/Mathematica tests moved to: https://github.com/arcticoder/aqei-numerical-validation

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT_DIR"

echo "=== aqei-bridge Lean tests ==="

echo "--- Lean build ---"
(cd "$ROOT_DIR/lean" && lake build)

if [[ -f "$ROOT_DIR/tests/lean_tests.sh" ]]; then
    echo "--- Lean typecheck ---"
    bash tests/lean_tests.sh
fi

echo "=== All Lean tests: OK ==="
