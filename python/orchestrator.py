"""orchestrator.py

Single 4-stage pipeline orchestrator for aqei-bridge.

Pipeline stages (repeatable):

I.   Lean formal language step
     - `lean/src/*.lean` defines toy types, cones, and conjecture statements.

II.  Heuristic ansatz step (design choices are explicit and revisable)
     - encoded in `mathematica/search.wl` as a finite-dimensional toy model.

III. Computational stress-testing (Mathematica)
     - run `wolframscript -file mathematica/search.wl`
     - writes JSON results under `mathematica/results/`

IV.  Formal synthesis (Lean skeleton emission)
     - `python/analyze_candidates.py` converts top candidates to rationals
       and writes `lean/src/GeneratedCandidates.lean`.
     - then `lake build` is invoked for a quick typecheck.

IMPORTANT:
- Stages II–III are heuristic/experimental.
- Nothing in this pipeline is a proof of physical causal behavior.

Usage:
  python python/orchestrator.py

Optional environment variables are passed through to Mathematica (see search.wl).
"""

from __future__ import annotations

import os
import subprocess
from pathlib import Path


def run_mathematica(repo_root: Path) -> None:
    script = repo_root / "mathematica" / "search.wl"
    if not script.exists():
        raise FileNotFoundError(script)

    # Prefer wolframscript (more stable for file execution), fall back to wolfram.
    if shutil_which("wolframscript"):
        cmd = ["wolframscript", "-file", str(script)]
    elif shutil_which("wolfram"):
        cmd = ["wolfram", "-script", str(script)]
    else:
        raise RuntimeError("Neither 'wolframscript' nor 'wolfram' found on PATH")

    subprocess.run(cmd, cwd=str(repo_root), check=True)


def run_analysis(repo_root: Path) -> None:
    analyze = repo_root / "python" / "analyze_candidates.py"
    subprocess.run(["python", str(analyze)], cwd=str(repo_root), check=True)


def run_lean_build(repo_root: Path) -> None:
    lean_dir = repo_root / "lean"
    # If elan is installed, we can source env in the shell; here we rely on PATH.
    subprocess.run(["lake", "build"], cwd=str(lean_dir), check=True)


def shutil_which(cmd: str) -> str | None:
    # Tiny `which` replacement to avoid importing shutil in some constrained setups.
    for p in os.environ.get("PATH", "").split(os.pathsep):
        candidate = Path(p) / cmd
        if candidate.exists() and os.access(candidate, os.X_OK):
            return str(candidate)
    return None


def main() -> int:
    repo_root = Path(__file__).resolve().parents[1]

    print("[aqei-bridge] Stage III: running Mathematica search")
    run_mathematica(repo_root)

    print("[aqei-bridge] Stage IV: generating Lean candidates")
    run_analysis(repo_root)

    print("[aqei-bridge] Stage I: Lean build (typecheck)")
    run_lean_build(repo_root)

    print("[aqei-bridge] OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
