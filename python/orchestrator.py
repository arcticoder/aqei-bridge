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

import json
import os
import subprocess
from datetime import datetime, timezone
from pathlib import Path


def run_mathematica(repo_root: Path, env: dict[str, str] | None = None) -> None:
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

    subprocess.run(cmd, cwd=str(repo_root), check=True, env=env)


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


def _utc_timestamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def run_pipeline(repo_root: Path, env: dict[str, str] | None = None) -> dict[str, str]:
    """Run the full 4-stage loop and persist a small run record.

    Returns a dict with paths for the produced artifacts.
    """

    env_final = os.environ.copy()
    if env:
        env_final.update(env)

    print("[aqei-bridge] Stage III: running Mathematica search")
    run_mathematica(repo_root, env=env_final)

    print("[aqei-bridge] Stage IV: generating Lean candidates")
    run_analysis(repo_root)

    print("[aqei-bridge] Stage I: Lean build (typecheck)")
    run_lean_build(repo_root)

    # Persist run metadata.
    ts = _utc_timestamp()
    runs_dir = repo_root / "runs" / ts
    runs_dir.mkdir(parents=True, exist_ok=True)

    results_dir = repo_root / "mathematica" / "results"
    summary_path = results_dir / "summary.json"
    candidates_path = results_dir / "top_candidates.json"
    generated_path = repo_root / "lean" / "src" / "AqeiBridge" / "GeneratedCandidates.lean"

    run_record = {
        "timestampUtc": ts,
        "resultsDir": str(results_dir),
        "summaryJson": str(summary_path),
        "topCandidatesJson": str(candidates_path),
        "generatedLean": str(generated_path),
        "env": {k: env_final[k] for k in sorted(env_final) if k.startswith("AQEI_")},
    }
    (runs_dir / "run.json").write_text(json.dumps(run_record, indent=2, sort_keys=True) + "\n")

    print("[aqei-bridge] OK")
    return run_record


def main() -> int:
    repo_root = Path(__file__).resolve().parents[1]

    run_pipeline(repo_root=repo_root)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
