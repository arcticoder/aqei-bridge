#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

# Keep this fast.
export AQEI_NUM_BASIS="2"
export AQEI_NUM_CONSTRAINTS="6"
export AQEI_GRID="32"
export AQEI_DOMAIN="2.0"
export AQEI_SIGMA="0.8"
export AQEI_SEED="42"

if command -v wolframscript >/dev/null 2>&1; then
  wolframscript -file "$ROOT_DIR/mathematica/search.wl"
elif command -v wolfram >/dev/null 2>&1; then
  wolfram -script "$ROOT_DIR/mathematica/search.wl"
else
  echo "ERROR: neither wolframscript nor wolfram found on PATH" >&2
  exit 1
fi

python - <<'PY'
import json
from pathlib import Path

results = Path('mathematica/results')
summary = results / 'summary.json'
top = results / 'top_candidates.json'
assert summary.exists(), 'summary.json missing'
assert top.exists(), 'top_candidates.json missing'

s = json.loads(summary.read_text())
assert s['N'] == 2
assert s['M'] == 6
assert s['grid'] == 32

cands = json.loads(top.read_text())
assert isinstance(cands, list)
assert len(cands) >= 1
assert 'a' in cands[0] and len(cands[0]['a']) == 2
print('Mathematica tests: OK')
PY
