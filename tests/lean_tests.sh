#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

# Ensure the generated file exists (it is overwritten by python/analyze_candidates.py).
python - <<'PY'
from pathlib import Path
out = Path('lean/src/AqeiBridge/GeneratedCandidates.lean')
out.parent.mkdir(parents=True, exist_ok=True)
if not out.exists():
    out.write_text("/-- Placeholder; overwritten by python/analyze_candidates.py. -/\nimport Std\n\nstructure Candidate where\n  score : Float\n  a : Array Float\n  activeConstraints : Array Nat\n  rayIndex : Nat\nderiving Repr\n\ndef topCandidates : List Candidate := []\n")
PY

"$ROOT_DIR/tests/build_lean.sh"

echo "Lean tests: OK"
