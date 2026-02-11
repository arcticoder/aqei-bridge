#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

python -m py_compile \
  "$ROOT_DIR/python/orchestrator.py" \
  "$ROOT_DIR/python/analyze_candidates.py"

python -m unittest -q tests.test_pipeline

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

# Smoke-test: sweep planner (dry-run only).
python "$ROOT_DIR/python/sweep_parameters.py" \
  --dry-run \
  --nbasis 2 \
  --sigmas 0.7 \
  --grid 16 \
  --out "$ROOT_DIR/.tmp_test/sweep_plan.json"

python - <<'PY'
import json
from pathlib import Path

p = Path('.tmp_test') / 'sweep_plan.json'
data = json.loads(p.read_text())
assert data['count'] == 1
pt = data['points'][0]
assert pt['AQEI_NUM_BASIS'] == 2
assert abs(pt['AQEI_SIGMA'] - 0.7) < 1e-12
assert pt['AQEI_GRID'] == 16
PY

rm -rf "$TMP_DIR"

echo "Python tests: OK"
