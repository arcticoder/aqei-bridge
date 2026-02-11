"""multi_ray_analysis.py

Phase 3 helper: compute a simple multi-ray overlap / connectedness proxy.

We treat each ray as the union of all exported `activeConstraints` across its
candidates, then compute Jaccard overlaps between rays.

This is heuristic and intended for sweep diagnostics, not proofs.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
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


def _parse_csv_floats(s: str) -> list[float]:
    return [float(x.strip()) for x in s.split(",") if x.strip()]


@dataclass(frozen=True)
class RayConstraints:
    ray_index: int
    ray_name: str
    constraints: frozenset[int]


def _union_constraints_by_ray(candidates: list[dict[str, Any]]) -> list[RayConstraints]:
    names: dict[int, str] = {}
    accum: dict[int, set[int]] = defaultdict(set)

    for c in candidates:
        ray_index = int(c.get("rayIndex", 0))
        ray_name = str(c.get("rayName", ""))
        names[ray_index] = ray_name
        for k in c.get("activeConstraints", []) or []:
            accum[ray_index].add(int(k))

    rays: list[RayConstraints] = []
    for ray_index in sorted(accum):
        rays.append(RayConstraints(ray_index=ray_index, ray_name=names.get(ray_index, ""), constraints=frozenset(accum[ray_index])))
    return rays


def _jaccard(a: frozenset[int], b: frozenset[int]) -> tuple[float, int, int]:
    inter = len(a & b)
    union = len(a | b)
    if union == 0:
        return 1.0, inter, union
    return inter / union, inter, union


def _components(ray_indices: list[int], edges: list[tuple[int, int]]) -> list[list[int]]:
    parent = {i: i for i in ray_indices}

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a: int, b: int) -> None:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra

    for a, b in edges:
        union(a, b)

    groups: dict[int, list[int]] = defaultdict(list)
    for i in ray_indices:
        groups[find(i)].append(i)

    return [sorted(v) for _, v in sorted(groups.items(), key=lambda kv: min(kv[1]))]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidates", required=True, help="Path to top_candidates.json")
    parser.add_argument("--out", required=True, help="Output JSON path")
    parser.add_argument("--threshold", type=float, default=0.0, help="Jaccard threshold for edges (default 0.0)")
    parser.add_argument("--theta", type=float, default=0.5, help="Connectedness proxy threshold (default 0.5)")
    parser.add_argument(
        "--thresholds",
        default="",
        help="Optional comma-separated thresholds; emits components/edge-count per threshold",
    )
    args = parser.parse_args()

    candidates_path = Path(args.candidates)
    out_path = Path(args.out)

    candidates_raw = _read_json(candidates_path)
    if not isinstance(candidates_raw, list):
        raise TypeError("Expected candidates JSON to be a list")

    rays = _union_constraints_by_ray(candidates_raw)

    ray_indices = [r.ray_index for r in rays]
    ray_index_set = set(ray_indices)

    pairs: list[dict[str, object]] = []
    edges: list[tuple[int, int]] = []

    theta = float(args.theta)

    for i in range(len(rays)):
        for j in range(i + 1, len(rays)):
            r1, r2 = rays[i], rays[j]
            jac, inter, uni = _jaccard(r1.constraints, r2.constraints)
            pairs.append(
                {
                    "rayA": r1.ray_index,
                    "rayB": r2.ray_index,
                    "jaccard": jac,
                    "intersection": inter,
                    "union": uni,
                }
            )
            if jac >= float(args.threshold):
                edges.append((r1.ray_index, r2.ray_index))

    comps = _components(ray_indices, edges)

    threshold_sweep: list[dict[str, object]] = []
    if args.thresholds.strip():
        for th in sorted(set(_parse_csv_floats(args.thresholds))):
            th_edges: list[tuple[int, int]] = []
            for p in pairs:
                a = int(p["rayA"])
                b = int(p["rayB"])
                if a not in ray_index_set or b not in ray_index_set:
                    continue
                if float(p["jaccard"]) >= th:
                    th_edges.append((a, b))

            th_components = _components(ray_indices, th_edges)
            threshold_sweep.append(
                {
                    "threshold": th,
                    "edgeCount": len(th_edges),
                    "components": th_components,
                    "summary": {
                        "componentCount": len(th_components),
                        "largestComponent": max((len(c) for c in th_components), default=0),
                    },
                }
            )

    payload = {
        "generatedAtUtc": _utc_timestamp(),
        "inputCandidates": str(candidates_path),
        "threshold": float(args.threshold),
        "thresholds": args.thresholds,
        "connectedness": {
            "theta": theta,
            "pairCount": len(pairs),
            "meanJaccard": (sum(float(p["jaccard"]) for p in pairs) / len(pairs)) if pairs else 0.0,
            "fractionPairsAboveTheta": (
                (sum(1 for p in pairs if float(p["jaccard"]) >= theta) / len(pairs)) if pairs else 0.0
            ),
        },
        "rays": [
            {
                "rayIndex": r.ray_index,
                "rayName": r.ray_name,
                "constraintCount": len(r.constraints),
            }
            for r in rays
        ],
        "jaccardPairs": pairs,
        "components": comps,
        "thresholdSweep": threshold_sweep,
    }

    # Optional: if we have a threshold sweep, summarize a crude “connectivity threshold”.
    if threshold_sweep and len(rays) > 0:
        ray_count = len(rays)
        connected_at: float | None = None
        for item in threshold_sweep:
            summ = item.get("summary", {})
            if isinstance(summ, dict) and int(summ.get("largestComponent", 0)) == ray_count:
                connected_at = float(item.get("threshold", 0.0))
                break
        payload["connectedness"]["connectivityThreshold"] = connected_at

    _write_json(out_path, payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
