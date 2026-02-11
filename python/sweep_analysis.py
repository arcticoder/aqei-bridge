"""sweep_analysis.py

Phase 3 helper: aggregate per-point metrics across a sweep.

Input: a sweep index JSON written by `python/sweep_parameters.py`.
For each run record, compute `maxScore` (and corresponding ray name) from the
(top) candidates JSON referenced by the run record.

This is heuristic and intended for diagnostics, not proofs.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def _utc_timestamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text())


def _write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def _resolve_path(base_dir: Path, raw: str) -> Path:
    p = Path(raw)
    if p.is_absolute():
        return p
    return base_dir / p


@dataclass(frozen=True)
class MaxScoreResult:
    max_score: float
    max_score_ray: str


def _max_score_from_candidates(path: Path) -> MaxScoreResult:
    raw = _read_json(path)
    if not isinstance(raw, list):
        raise TypeError(f"Expected list in candidates JSON: {path}")

    best_score = float("-inf")
    best_ray = ""
    for c in raw:
        if not isinstance(c, dict):
            continue
        score = float(c.get("score", float("-inf")))
        if score > best_score:
            best_score = score
            best_ray = str(c.get("rayName", ""))

    if best_score == float("-inf"):
        return MaxScoreResult(max_score=0.0, max_score_ray="")
    return MaxScoreResult(max_score=best_score, max_score_ray=best_ray)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", required=True, help="Path to sweep index JSON")
    parser.add_argument("--out", default="", help="Output JSON path (default next to index)")
    args = parser.parse_args()

    index_path = Path(args.index)
    index = _read_json(index_path)
    if not isinstance(index, dict):
        raise TypeError("Expected sweep index JSON to be an object")

    runs = index.get("runs", [])
    if not isinstance(runs, list):
        raise TypeError("Expected 'runs' to be a list")

    points_out: list[dict[str, object]] = []
    max_scores: list[float] = []

    for item in runs:
        if not isinstance(item, dict):
            continue

        run_record_path_raw = str(item.get("runRecordPath", ""))
        if not run_record_path_raw:
            continue
        run_record_path = _resolve_path(index_path.parent, run_record_path_raw)

        run_record = _read_json(run_record_path)
        if not isinstance(run_record, dict):
            continue

        base_dir = run_record_path.parent
        candidates_raw = str(run_record.get("archivedTopCandidatesJson") or run_record.get("topCandidatesJson") or "")
        if not candidates_raw:
            continue

        candidates_path = _resolve_path(base_dir, candidates_raw)
        ms = _max_score_from_candidates(candidates_path)

        pt = item.get("point", {})
        points_out.append(
            {
                "point": pt,
                "runTimestampUtc": run_record.get("timestampUtc", item.get("runTimestampUtc", "")),
                "runRecordPath": str(run_record_path),
                "candidatesPath": str(candidates_path),
                "maxScore": ms.max_score,
                "maxScoreRay": ms.max_score_ray,
            }
        )
        max_scores.append(ms.max_score)

    summary = {
        "generatedAtUtc": _utc_timestamp(),
        "indexPath": str(index_path),
        "count": len(points_out),
        "points": points_out,
        "aggregate": {
            "max": max(max_scores) if max_scores else 0.0,
            "min": min(max_scores) if max_scores else 0.0,
            "mean": (sum(max_scores) / len(max_scores)) if max_scores else 0.0,
        },
    }

    if args.out:
        out_path = Path(args.out)
        if not out_path.is_absolute():
            out_path = index_path.parent / out_path
    else:
        out_path = index_path.parent / "sweep_summary.json"

    _write_json(out_path, summary)
    print(f"Wrote sweep summary: {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
