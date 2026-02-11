"""sweep_parameters.py

Phase 3 helper: parameter sweeps for the toy pipeline.

This is intentionally conservative and test-friendly:
- `--dry-run` writes the sweep grid to JSON without running Mathematica.
- When executing, the default behavior sets `AQEI_TEST_MODE=1` unless `--full` is passed.

Artifacts are written under `runs/` (which is git-ignored).
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from itertools import product
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class SweepPoint:
    AQEI_NUM_BASIS: int
    AQEI_SIGMA: float
    AQEI_GRID: int


def _utc_timestamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def _parse_csv_ints(s: str) -> list[int]:
    return [int(x.strip()) for x in s.split(",") if x.strip()]


def _parse_csv_floats(s: str) -> list[float]:
    return [float(x.strip()) for x in s.split(",") if x.strip()]


def _parse_csv_ints_or_empty(s: str) -> list[int]:
    s = s.strip()
    if not s:
        return []
    return _parse_csv_ints(s)


def build_sweep(
    nbasis: Iterable[int],
    sigmas: Iterable[float],
    grids: Iterable[int],
) -> list[SweepPoint]:
    return [
        SweepPoint(AQEI_NUM_BASIS=n, AQEI_SIGMA=s, AQEI_GRID=g)
        for n, s, g in product(nbasis, sigmas, grids)
    ]


def write_plan(points: list[SweepPoint], out_path: Path) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "generatedAtUtc": _utc_timestamp(),
        "count": len(points),
        "points": [asdict(p) for p in points],
    }
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--nbasis", default="2,3", help="Comma-separated basis sizes")
    parser.add_argument("--sigmas", default="0.7,0.8", help="Comma-separated sigma values")
    parser.add_argument("--grid", type=int, default=32, help="Grid size")
    parser.add_argument("--grids", default="", help="Optional comma-separated grid sizes (overrides --grid)")
    parser.add_argument("--dry-run", action="store_true", help="Only write the sweep plan JSON")
    parser.add_argument("--out", default="", help="Output path for plan JSON (default under runs/)")
    parser.add_argument("--full", action="store_true", help="Do not force AQEI_TEST_MODE=1 when executing")

    args = parser.parse_args()

    nbasis = _parse_csv_ints(args.nbasis)
    sigmas = _parse_csv_floats(args.sigmas)
    grids = _parse_csv_ints_or_empty(args.grids)
    if not grids:
        grids = [int(args.grid)]

    points = build_sweep(nbasis=nbasis, sigmas=sigmas, grids=grids)

    sweep_ts = _utc_timestamp()

    repo_root = Path(__file__).resolve().parents[1]
    if args.out:
        out_path = Path(args.out)
        if not out_path.is_absolute():
            out_path = repo_root / out_path
    else:
        out_path = repo_root / "runs" / "sweeps" / sweep_ts / "sweep_plan.json"

    write_plan(points, out_path)

    if args.dry_run:
        print(f"Wrote plan: {out_path}")
        return 0

    # Execute the plan.
    from python.orchestrator import run_pipeline

    sweep_dir = repo_root / "runs" / "sweeps" / sweep_ts
    index_path = sweep_dir / "index.json"
    sweep_dir.mkdir(parents=True, exist_ok=True)
    run_index: list[dict[str, object]] = []

    for p in points:
        env = {
            "AQEI_NUM_BASIS": str(p.AQEI_NUM_BASIS),
            "AQEI_SIGMA": str(p.AQEI_SIGMA),
            "AQEI_GRID": str(p.AQEI_GRID),
        }
        if not args.full:
            env["AQEI_TEST_MODE"] = "1"

        record = run_pipeline(repo_root=repo_root, env=env)
        run_record_path = repo_root / "runs" / record["timestampUtc"] / "run.json"
        run_index.append(
            {
                "point": asdict(p),
                "runTimestampUtc": record["timestampUtc"],
                "runRecordPath": str(run_record_path),
            }
        )

        # Persist after each point so partial sweeps still yield a useful index.
        index_payload = {
            "generatedAtUtc": sweep_ts,
            "planPath": str(out_path),
            "count": len(run_index),
            "runs": run_index,
        }
        index_path.write_text(json.dumps(index_payload, indent=2, sort_keys=True) + "\n")

    print(f"Wrote sweep index: {index_path}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
