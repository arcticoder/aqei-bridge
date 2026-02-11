"""minkowski_poset.py

Generate a small 1+1 discrete causal graph ("Minkowski-ish" poset) for diagnostics.

This is a tiny, deterministic generator intended for visualization and for
exercising causal-graph tooling without external dependencies.

We model events as integer lattice points (t, x) with:
- t in [0, tmax]
- x in [0, xmax]

Edges are local "future-step" edges from (t, x) to (t+1, x+dx) where dx ∈ {-1, 0, 1}
and the destination stays in-bounds.

This is not a faithful discretization of the full relation
  (Δt)^2 >= (Δx)^2, Δt > 0
but its reachability relation is a simple proxy.

Outputs JSON in the format:
  {"edges": [[[t,x],[t',x']], ...]}

Optionally writes a DOT file for Graphviz.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable


def build_edges(tmax: int, xmax: int) -> list[list[list[int]]]:
    edges: list[list[list[int]]] = []
    for t in range(tmax + 1):
        for x in range(xmax + 1):
            if t == tmax:
                continue
            for dx in (-1, 0, 1):
                xx = x + dx
                if 0 <= xx <= xmax:
                    edges.append([[t, x], [t + 1, xx]])

    # Deterministic ordering.
    edges.sort(key=lambda e: (e[0][0], e[0][1], e[1][0], e[1][1]))
    return edges


def to_dot(edges: list[list[list[int]]], *, name: str = "MinkowskiPoset") -> str:
    nodes: set[tuple[int, int]] = set()
    for (t0, x0), (t1, x1) in edges:
        nodes.add((t0, x0))
        nodes.add((t1, x1))

    def q(node: tuple[int, int]) -> str:
        # DOT string literal of a JSON array.
        return json.dumps([node[0], node[1]])

    lines: list[str] = [f"digraph {name} {{"]
    for n in sorted(nodes):
        lines.append(f"  {q(n)};")
    for (t0, x0), (t1, x1) in edges:
        lines.append(f"  {q((t0, x0))} -> {q((t1, x1))};")
    lines.append("}")
    return "\n".join(lines) + "\n"


def main(argv: Iterable[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--tmax", type=int, default=5, help="Max time coordinate (inclusive)")
    p.add_argument("--xmax", type=int, default=5, help="Max space coordinate (inclusive)")
    p.add_argument("--out", required=True, help="Output JSON path")
    p.add_argument("--dot-out", default="", help="Optional DOT output path")
    p.add_argument("--name", default="MinkowskiPoset", help="DOT graph name")
    args = p.parse_args(list(argv) if argv is not None else None)

    if args.tmax < 0 or args.xmax < 0:
        raise SystemExit("--tmax and --xmax must be nonnegative")

    edges = build_edges(args.tmax, args.xmax)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps({"edges": edges}, indent=2, sort_keys=True) + "\n")
    print(f"Wrote graph JSON: {out_path}")

    if args.dot_out:
        dot_path = Path(args.dot_out)
        dot_path.parent.mkdir(parents=True, exist_ok=True)
        dot_path.write_text(to_dot(edges, name=args.name))
        print(f"Wrote DOT: {dot_path}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
