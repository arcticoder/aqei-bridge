#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

python -m py_compile \
  "$ROOT_DIR/python/orchestrator.py" \
  "$ROOT_DIR/python/analyze_candidates.py"

# Smoke-test: generate Lean candidates from a tiny synthetic JSON.
TMP_DIR="$ROOT_DIR/.tmp_test"
rm -rf "$TMP_DIR"
mkdir -p "$TMP_DIR"

cat >"$TMP_DIR/summary.json" <<'JSON'
{"N": 2, "M": 3}
JSON

cat >"$TMP_DIR/top_candidates.json" <<'JSON'
[
  {"rayIndex": 1, "rayName": "t=x", "score": 0.01, "a": [0.1, -0.2], "activeConstraints": [1,2]}
]
JSON

python - <<'PY'
from pathlib import Path
from python.analyze_candidates import generate_lean_candidates

out = Path('.tmp_test') / 'GeneratedCandidates.lean'
generate_lean_candidates(Path('.tmp_test'), out, top_k=5)
text = out.read_text()
assert 'structure Candidate' in text
assert 'def topCandidates' in text
assert 'aRat' in text
PY

rm -rf "$TMP_DIR"

echo "Python tests: OK"
