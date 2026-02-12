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

# Ensure the generated poset conjectures file exists (it may be overwritten by python/poset_homology_proxy.py).
python - <<'PY'
from pathlib import Path
out = Path('lean/src/AqeiBridge/GeneratedPosetConjectures.lean')
out.parent.mkdir(parents=True, exist_ok=True)
if not out.exists():
    out.write_text("/- Placeholder; overwritten by python/poset_homology_proxy.py. -/\nimport Std\n\nnamespace AqeiBridge\n\nstructure PosetZ1Result where\n  name : String\n  nodeCount : Nat\n  edgeCount : Nat\n  weakComponentCount : Nat\n  z1Dim : Nat\n  hasDirectedCycle : Bool\nderiving Repr\n\ndef posetZ1Results : List PosetZ1Result := []\n\ndef posetZ1DimMax : Nat := 0\n\ntheorem posetZ1Results_exported : True := by\n  trivial\n\ntheorem conjecture_posetZ1DimMax_bound : True := by\n  trivial\n\nend AqeiBridge\n")
PY

"$ROOT_DIR/tests/build_lean.sh"

echo "Lean tests: OK"
