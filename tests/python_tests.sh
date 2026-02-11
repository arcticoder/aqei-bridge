#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

python -m py_compile \
  "$ROOT_DIR/python/orchestrator.py" \
  "$ROOT_DIR/python/analyze_candidates.py" \
  "$ROOT_DIR/python/multi_ray_analysis.py" \
  "$ROOT_DIR/python/sweep_analysis.py"

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
assert 'maxScoreUpperRat' in text
PY

# Smoke-test: analyze_candidates CLI supports custom results-dir and out.
python "$ROOT_DIR/python/analyze_candidates.py" \
  --results-dir "$ROOT_DIR/.tmp_test" \
  --out "$ROOT_DIR/.tmp_test/GeneratedCandidatesCli.lean"

python - <<'PY'
from pathlib import Path

p = Path('.tmp_test') / 'GeneratedCandidatesCli.lean'
text = p.read_text()
assert 'structure Candidate' in text
assert 'def topCandidates' in text
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

# Smoke-test: multi-ray analysis.
cat >"$TMP_DIR/top_candidates.json" <<'JSON'
[
  {"rayIndex": 1, "rayName": "r1", "score": 0.1, "a": [0.1], "activeConstraints": [1,2,3]},
  {"rayIndex": 2, "rayName": "r2", "score": 0.2, "a": [0.2], "activeConstraints": [3,4]},
  {"rayIndex": 1, "rayName": "r1", "score": 0.05, "a": [0.3], "activeConstraints": [5]}
]
JSON

python "$ROOT_DIR/python/multi_ray_analysis.py" \
  --candidates "$TMP_DIR/top_candidates.json" \
  --out "$TMP_DIR/multi_ray.json" \
  --threshold 0.2 \
  --theta 0.2 \
  --thresholds 0.0,0.2,0.5 \
  --dot-out "$TMP_DIR/multi_ray.dot"

python - <<'PY'
import json
from pathlib import Path

data = json.loads(Path('.tmp_test/multi_ray.json').read_text())
assert data['rays'][0]['rayIndex'] == 1
assert data['rays'][1]['rayIndex'] == 2
assert len(data['jaccardPairs']) == 1
pair = data['jaccardPairs'][0]
assert pair['intersection'] == 1
assert pair['union'] == 5
assert len(data['thresholdSweep']) == 3
conn = data['connectedness']
assert abs(conn['theta'] - 0.2) < 1e-12
assert conn['pairCount'] == 1
assert 0.0 <= conn['meanJaccard'] <= 1.0
assert conn['fractionPairsAboveTheta'] in (0.0, 1.0)

dot = Path('.tmp_test/multi_ray.dot').read_text()
assert 'graph Overlap' in dot
assert '--' in dot
PY

# Smoke-test: sweep analysis (reads index + run record + candidates).
RUN_TS="20260101T000000Z"
mkdir -p "$ROOT_DIR/runs/$RUN_TS/artifacts"
cat >"$ROOT_DIR/runs/$RUN_TS/artifacts/top_candidates.json" <<'JSON'
[
  {"rayIndex": 1, "rayName": "r1", "score": 0.3, "a": [0.1], "activeConstraints": [1]},
  {"rayIndex": 2, "rayName": "r2", "score": 0.9, "a": [0.2], "activeConstraints": [2]}
]
JSON

cat >"$ROOT_DIR/runs/$RUN_TS/run.json" <<JSON
{
  "timestampUtc": "$RUN_TS",
  "archivedTopCandidatesJson": "$ROOT_DIR/runs/$RUN_TS/artifacts/top_candidates.json"
}
JSON

cat >"$TMP_DIR/sweep_index.json" <<JSON
{
  "generatedAtUtc": "20260101T000000Z",
  "planPath": "(test)",
  "count": 1,
  "runs": [
    {
      "point": {"AQEI_NUM_BASIS": 2, "AQEI_SIGMA": 0.7, "AQEI_GRID": 16},
      "runTimestampUtc": "$RUN_TS",
      "runRecordPath": "$ROOT_DIR/runs/$RUN_TS/run.json"
    }
  ]
}
JSON

python "$ROOT_DIR/python/sweep_analysis.py" \
  --index "$TMP_DIR/sweep_index.json" \
  --out "$TMP_DIR/sweep_summary.json"

python - <<'PY'
import json
from pathlib import Path

data = json.loads(Path('.tmp_test/sweep_summary.json').read_text())
assert data['count'] == 1
pt0 = data['points'][0]
assert abs(pt0['maxScore'] - 0.9) < 1e-12
assert pt0['maxScoreRay'] == 'r2'
PY

rm -rf "$TMP_DIR"

echo "Python tests: OK"
