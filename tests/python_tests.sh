#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

python -m py_compile \
  "$ROOT_DIR/python/orchestrator.py" \
  "$ROOT_DIR/python/analyze_candidates.py" \
  "$ROOT_DIR/python/multi_ray_analysis.py" \
  "$ROOT_DIR/python/sweep_analysis.py" \
  "$ROOT_DIR/python/poset_homology_proxy.py" \
  "$ROOT_DIR/python/causal_graph_tools.py" \
  "$ROOT_DIR/python/minkowski_poset.py" \
  "$ROOT_DIR/python/ctc_scan.py" \
  "$ROOT_DIR/python/poset_interval_tools.py"

python -m unittest -q tests.test_pipeline

# Smoke-test: generate Lean candidates from a tiny synthetic JSON.
TMP_DIR="$ROOT_DIR/.tmp_test"
rm -rf "$TMP_DIR"

# Smoke-test: poset homology proxy (Z1 dimension) + Lean emission.
TMP_DIR="$ROOT_DIR/.tmp_test"
rm -rf "$TMP_DIR"
mkdir -p "$TMP_DIR"

cat >"$TMP_DIR/diamond.json" <<'JSON'
{
  "edges": [
    ["a","b"],
    ["a","c"],
    ["b","d"],
    ["c","d"]
  ]
}
JSON

python - <<'PY'
import json
import subprocess
import sys
from pathlib import Path

root = Path('.').resolve()
tool = root / 'python' / 'poset_homology_proxy.py'

out = subprocess.check_output([sys.executable, str(tool), 'z1', str(root / '.tmp_test/diamond.json'), '--json'])
obj = json.loads(out.decode('utf-8'))
assert obj['hasDirectedCycle'] is False
assert obj['nodeCount'] == 4
assert obj['edgeCount'] == 4
assert obj['weakComponentCount'] == 1
assert obj['z1Dim'] == 1
PY

python - <<'PY'
import json
import subprocess
import sys
from pathlib import Path

root = Path('.').resolve()
tool = root / 'python' / 'poset_homology_proxy.py'

out = subprocess.check_output(
  [
    sys.executable,
    str(tool),
    'perturb-fft',
    str(root / '.tmp_test/diamond.json'),
    '--trials', '3',
    '--epsilon', '0.01',
    '--threshold', '0.5',
    '--window', '5',
    '--seed', '0',
    '--json',
  ]
)
obj = json.loads(out.decode('utf-8'))
assert obj['baseline']['z1Dim'] == 1
assert obj['params']['trials'] == 3

summ = obj['summary']
assert abs(summ['meanAbsDeltaZ1'] - 0.0) < 1e-12
assert summ['maxAbsDeltaZ1'] == 0
assert abs(summ['fractionUnchanged'] - 1.0) < 1e-12
PY

python - <<'PY'
import json
import subprocess
import sys
from pathlib import Path

root = Path('.').resolve()
tool = root / 'python' / 'poset_homology_proxy.py'

# With epsilon=0 and positive cutoff, the local cone never widens, so the
# perturbed graphs equal baseline.
out = subprocess.check_output(
  [
    sys.executable,
    str(tool),
    'sweep-minkowski-perturb',
    '--tmax', '2',
    '--xmax', '2',
    '--trials', '3',
    '--epsilon', '0.0',
    '--cutoff', '0.1',
    '--window', '5',
    '--seed', '0',
    '--json',
  ]
)
obj = json.loads(out.decode('utf-8'))
assert obj['grid']['tmax'] == 2
assert obj['grid']['xmax'] == 2
assert obj['baseline']['nodeCount'] == 9
assert obj['params']['trials'] == 3

summ = obj['summary']
assert abs(summ['meanAbsDeltaZ1'] - 0.0) < 1e-12
assert summ['maxAbsDeltaZ1'] == 0
assert abs(summ['fractionUnchanged'] - 1.0) < 1e-12
PY

python "$ROOT_DIR/python/poset_homology_proxy.py" \
  sweep-minkowski \
  --tmaxs 1,2 \
  --xmaxs 1 \
  --out-dir "$TMP_DIR/poset_sweep" \
  --lean-out "$ROOT_DIR/lean/src/AqeiBridge/GeneratedPosetConjectures.lean"

python - <<'PY'
from pathlib import Path

p = Path('lean/src/AqeiBridge/GeneratedPosetConjectures.lean')
text = p.read_text()
assert 'structure PosetZ1Result' in text
assert 'def posetZ1Results' in text
assert 'def posetZ1DimMax' in text
PY

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
  --analyze \
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

# Smoke-test: causal graph tools (cycle detection + DOT export).
TMP_DIR="$ROOT_DIR/.tmp_test"
rm -rf "$TMP_DIR"
mkdir -p "$TMP_DIR"

cat >"$TMP_DIR/graph_acyclic.json" <<'JSON'
{"edges": [["a","b"], ["b","c"]]}
JSON

cat >"$TMP_DIR/graph_cycle.json" <<'JSON'
{"edges": [["a","b"], ["b","a"]]}
JSON

python - <<'PY'
import json
import subprocess
import sys
from pathlib import Path

root = Path('.').resolve()
tool = root / 'python' / 'causal_graph_tools.py'

acy = subprocess.check_output([sys.executable, str(tool), 'ctc', str(root / '.tmp_test/graph_acyclic.json'), '--json'])
cyc = subprocess.check_output([sys.executable, str(tool), 'ctc', str(root / '.tmp_test/graph_cycle.json'), '--json'])

acy_obj = json.loads(acy.decode('utf-8'))
cyc_obj = json.loads(cyc.decode('utf-8'))
assert acy_obj['hasCycle'] is False
assert cyc_obj['hasCycle'] is True

dot_out = root / '.tmp_test' / 'graph.dot'
subprocess.check_call([sys.executable, str(tool), 'dot', str(root / '.tmp_test/graph_acyclic.json'), '--out', str(dot_out)])
dot = dot_out.read_text()
assert 'digraph' in dot
assert '->' in dot
PY

rm -rf "$TMP_DIR"

# Smoke-test: causal graph tools accept futures-map JSON.
TMP_DIR="$ROOT_DIR/.tmp_test"
rm -rf "$TMP_DIR"
mkdir -p "$TMP_DIR"

cat >"$TMP_DIR/futures_cycle.json" <<'JSON'
{"futures": {"a": ["b"], "b": ["a"]}}
JSON

python - <<'PY'
import json
import subprocess
import sys
from pathlib import Path

root = Path('.').resolve()
tool = root / 'python' / 'causal_graph_tools.py'

out = subprocess.check_output([sys.executable, str(tool), 'ctc', str(root / '.tmp_test/futures_cycle.json'), '--json'])
obj = json.loads(out.decode('utf-8'))
assert obj['hasCycle'] is True
PY

# Smoke-test: Minkowski poset generator writes JSON and DOT.
python "$ROOT_DIR/python/minkowski_poset.py" \
  --tmax 2 \
  --xmax 2 \
  --out "$ROOT_DIR/.tmp_test/poset.json" \
  --dot-out "$ROOT_DIR/.tmp_test/poset.dot"

python - <<'PY'
import json
from pathlib import Path

data = json.loads(Path('.tmp_test/poset.json').read_text())
assert 'edges' in data
assert len(data['edges']) > 0

dot = Path('.tmp_test/poset.dot').read_text()
assert 'digraph' in dot
assert '->' in dot
PY

rm -rf "$TMP_DIR"

# Smoke-test: ctc_scan wrapper can generate Minkowski poset and reports acyclic.
TMP_DIR="$ROOT_DIR/.tmp_test"
rm -rf "$TMP_DIR"
mkdir -p "$TMP_DIR"

python - <<'PY'
import json
import subprocess
import sys
from pathlib import Path

root = Path('.').resolve()
scan = root / 'python' / 'ctc_scan.py'
out_graph = root / '.tmp_test' / 'poset_scan.json'

out = subprocess.check_output(
  [sys.executable, str(scan), '--minkowski', '--tmax', '3', '--xmax', '3', '--out', str(out_graph), '--json']
)
obj = json.loads(out.decode('utf-8'))
assert obj['hasCycle'] is False
assert obj['nodeCount'] > 0
assert out_graph.exists()
PY

rm -rf "$TMP_DIR"

# Smoke-test: Alexandrov interval helper computes I(p,q) and can write DOT.
TMP_DIR="$ROOT_DIR/.tmp_test"
rm -rf "$TMP_DIR"
mkdir -p "$TMP_DIR"

cat >"$TMP_DIR/chain.json" <<'JSON'
{"edges": [["a","b"], ["b","c"]]}
JSON

python - <<'PY'
import json
import subprocess
import sys
from pathlib import Path

root = Path('.').resolve()
tool = root / 'python' / 'poset_interval_tools.py'
graph = root / '.tmp_test' / 'chain.json'

out = subprocess.check_output(
  [sys.executable, str(tool), 'interval', str(graph), '--p', 'a', '--q', 'c', '--json']
)
obj = json.loads(out.decode('utf-8'))
assert obj['p'] == 'a'
assert obj['q'] == 'c'
assert set(obj['intervalNodes']) == {'a', 'b', 'c'}

dot_out = root / '.tmp_test' / 'interval.dot'
subprocess.check_call(
  [sys.executable, str(tool), 'interval', str(graph), '--p', 'a', '--q', 'c', '--dot-out', str(dot_out)]
)
dot = dot_out.read_text()
assert 'digraph' in dot
assert '->' in dot
PY

rm -rf "$TMP_DIR"

echo "Python tests: OK"
