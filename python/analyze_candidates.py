"""analyze_candidates.py

Stage IV (Formal synthesis helpers)
---------------------------------

Reads heuristic search outputs from Mathematica and emits Lean 4 skeletons that
capture candidate coefficient vectors and (heuristically) active constraints.

This file is intentionally conservative:
- It does *not* claim any physical or geometric equivalence.
- It only converts numeric artifacts into exact-ish rational literals for Lean,
  suitable for iterative formalization.

Expected inputs (written by mathematica/search.wl):
- mathematica/results/summary.json
- mathematica/results/top_candidates.json

Outputs:
- lean/src/GeneratedCandidates.lean

All claims about "active constraints" are heuristic (tolerance-based).
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable


@dataclass(frozen=True)
class Candidate:
    ray_index: int
    ray_name: str
    score: float
    a: list[float]
    active_constraints: list[int]


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text())


def float_to_fraction(x: float, max_den: int = 10**6) -> Fraction:
    # Defensive: avoid NaNs/Infs leaking into Lean.
    if x != x or x in (float("inf"), float("-inf")):
        raise ValueError(f"Non-finite float: {x}")
    return Fraction(x).limit_denominator(max_den)


def fraction_to_lean_rat(q: Fraction) -> str:
    # Emit as ((n : Int) : Rat) / d to avoid parsing surprises.
    n = q.numerator
    d = q.denominator
    return f"((( {n} : Int) : Rat) / {d})"


def _lean_array_int(xs: Iterable[int]) -> str:
    return "#[]" if not xs else "#[" + ", ".join(str(int(x)) for x in xs) + "]"


def generate_lean_candidates(
    results_dir: Path,
    out_path: Path,
    top_k: int = 4,
    max_den: int = 10**6,
) -> None:
    """Generate lean/src/GeneratedCandidates.lean from Mathematica JSON outputs."""

    summary_path = results_dir / "summary.json"
    cands_path = results_dir / "top_candidates.json"

    summary = _read_json(summary_path)
    cands_raw = _read_json(cands_path)

    # Sort by score descending.
    cands_raw = sorted(cands_raw, key=lambda c: float(c.get("score", 0.0)), reverse=True)[:top_k]

    candidates: list[Candidate] = []
    for c in cands_raw:
        candidates.append(
            Candidate(
                ray_index=int(c.get("rayIndex", 0)),
                ray_name=str(c.get("rayName", "")),
                score=float(c.get("score", 0.0)),
                a=[float(x) for x in c.get("a", [])],
                active_constraints=[int(x) for x in c.get("activeConstraints", [])],
            )
        )

    max_score = max((c.score for c in candidates), default=0.0)
    max_score_ray = ""
    if candidates:
        best = max(candidates, key=lambda c: c.score)
        max_score_ray = best.ray_name

    # A conservative rational upper bound on max_score.
    # We round up at denominator `max_den` to make later “≤ bound” lemmas plausible.
    if max_den <= 0:
        max_den = 10**6
    max_score_upper = Fraction(math.ceil(max_score * max_den), max_den)

    # Emit Lean.
    out_path.parent.mkdir(parents=True, exist_ok=True)

    n_basis = int(summary.get("N", len(candidates[0].a) if candidates else 0))
    m_constraints = int(summary.get("M", 0))

    lines: list[str] = []
    lines.append("/-- Auto-generated from mathematica/search.wl. -/")
    lines.append("import Std")
    lines.append("import Mathlib.Data.Rat.Basic")
    lines.append("")
    lines.append("namespace AqeiBridge")
    lines.append("")
    lines.append("structure Candidate where")
    lines.append("  rayIndex : Nat")
    lines.append("  rayName : String")
    lines.append("  score : Float")
    lines.append("  aRat : Array Rat")
    lines.append("  activeConstraints : Array Nat")
    lines.append("deriving Repr")
    lines.append("")
    lines.append(f"def nBasis : Nat := {n_basis}")
    lines.append(f"def mConstraints : Nat := {m_constraints}")
    lines.append(f"def maxScore : Float := {max_score}")
    lines.append(f"def maxScoreRay : String := {json.dumps(max_score_ray)}")
    lines.append(f"def maxScoreUpperRat : Rat := {fraction_to_lean_rat(max_score_upper)}")
    lines.append("")

    lines.append("def topCandidates : List Candidate := [")

    for cand in candidates:
        fracs = [float_to_fraction(x, max_den=max_den) for x in cand.a]
        a_rat = "#[]" if not fracs else "#[" + ", ".join(fraction_to_lean_rat(q) for q in fracs) + "]"
        active = _lean_array_int(cand.active_constraints)
        lines.append("  {")
        lines.append(f"    rayIndex := {cand.ray_index},")
        lines.append(f"    rayName := {json.dumps(cand.ray_name)},")
        lines.append(f"    score := {cand.score},")
        lines.append(f"    aRat := {a_rat},")
        lines.append(f"    activeConstraints := {active}")
        lines.append("  },")

    lines.append("]")
    lines.append("")

    # Skeleton lemma: user fills in the actual AQEI functionals + proof obligations.
    lines.append("/--")
    lines.append("Heuristic certificate skeleton.")
    lines.append("")
    lines.append("This lemma is intentionally weak: it only packages the exported data.")
    lines.append("Replace `True` with real inequalities once the AQEI functionals are formalized.")
    lines.append("-/")
    lines.append("theorem topCandidates_exported : True := by")
    lines.append("  trivial")

    lines.append("")
    lines.append("/--")
    lines.append("A placeholder 'bound' statement: tie the numeric search output to a rational upper bound.")
    lines.append("Replace `True` with a real statement once Δ is formalized.")
    lines.append("-/")
    lines.append("theorem maxScore_le_maxScoreUpperRat : True := by")
    lines.append("  trivial")
    lines.append("")
    lines.append("end AqeiBridge")

    out_path.write_text("\n".join(lines) + "\n")


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    results_dir = root / "mathematica" / "results"
    out_path = root / "lean" / "src" / "AqeiBridge" / "GeneratedCandidates.lean"
    generate_lean_candidates(results_dir, out_path)
    print(f"Wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
