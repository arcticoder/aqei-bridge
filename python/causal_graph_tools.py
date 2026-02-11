"""causal_graph_tools.py

Small, deterministic helpers for directed causal graphs.

This is intentionally dependency-free (no networkx) so it can run in CI.

Input format (JSON):
- edges: list[list[hashable, hashable]] or list[dict{"src":..., "dst":...}]
- futures: dict[node, list[node]] interpreted as edges (node -> each future)

Example:
  {"edges": [["a","b"],["b","c"]]}

Subcommands:
- ctc: print whether a directed cycle exists (proxy for a CTC)
- dot: write a Graphviz DOT file for visualization
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


@dataclass(frozen=True)
class DiGraph:
    nodes: frozenset[str]
    adj: dict[str, frozenset[str]]


def _to_node_id(x: Any) -> str:
    # Deterministic stringification for DOT/node IDs.
    if isinstance(x, str):
        return x
    return json.dumps(x, sort_keys=True)


def _load_edges(payload: dict[str, Any]) -> list[tuple[str, str]]:
    if "edges" in payload:
        raw_edges = payload["edges"]
        if not isinstance(raw_edges, list):
            raise ValueError("'edges' must be a list")

        edges: list[tuple[str, str]] = []
        for e in raw_edges:
            if isinstance(e, list) and len(e) == 2:
                src, dst = e
            elif isinstance(e, dict) and "src" in e and "dst" in e:
                src, dst = e["src"], e["dst"]
            else:
                raise ValueError("Each edge must be [src, dst] or {src:..., dst:...}")
            edges.append((_to_node_id(src), _to_node_id(dst)))

        return edges

    if "futures" in payload:
        futures = payload["futures"]
        if not isinstance(futures, dict):
            raise ValueError("'futures' must be an object mapping node -> list[node]")

        edges: list[tuple[str, str]] = []
        # Deterministic ordering: sort by stringified node IDs.
        src_ids = sorted((_to_node_id(k), k) for k in futures.keys())
        for src_id, src_key in src_ids:
            dsts = futures[src_key]
            if not isinstance(dsts, list):
                raise ValueError("Each futures value must be a list")
            dst_ids = sorted(_to_node_id(d) for d in dsts)
            for dst_id in dst_ids:
                edges.append((src_id, dst_id))

        return edges

    raise ValueError("JSON must contain either key 'edges' or key 'futures'")


def load_digraph(path: Path) -> DiGraph:
    payload = json.loads(path.read_text())
    if not isinstance(payload, dict):
        raise ValueError("Top-level JSON must be an object")

    edges = _load_edges(payload)

    nodes: set[str] = set()
    tmp_adj: dict[str, set[str]] = defaultdict(set)
    for src, dst in edges:
        nodes.add(src)
        nodes.add(dst)
        tmp_adj[src].add(dst)

    adj: dict[str, frozenset[str]] = {n: frozenset(tmp_adj.get(n, set())) for n in nodes}
    return DiGraph(nodes=frozenset(nodes), adj=adj)


def has_directed_cycle(g: DiGraph) -> bool:
    """Detects a directed cycle using Kahn's algorithm.

    Returns True iff the graph contains a directed cycle.
    """

    indeg: dict[str, int] = {n: 0 for n in g.nodes}
    for src, nbrs in g.adj.items():
        for dst in nbrs:
            indeg[dst] = indeg.get(dst, 0) + 1
            indeg.setdefault(src, 0)

    q: deque[str] = deque([n for n, d in indeg.items() if d == 0])
    visited = 0
    while q:
        n = q.popleft()
        visited += 1
        for m in g.adj.get(n, frozenset()):
            indeg[m] -= 1
            if indeg[m] == 0:
                q.append(m)

    return visited != len(indeg)


def to_dot(g: DiGraph, *, name: str = "CausalGraph") -> str:
    # Stable ordering for deterministic diffs.
    nodes = sorted(g.nodes)
    edges: list[tuple[str, str]] = []
    for src in nodes:
        for dst in sorted(g.adj.get(src, frozenset())):
            edges.append((src, dst))

    def q(s: str) -> str:
        # DOT string literal.
        return json.dumps(s)

    lines: list[str] = [f"digraph {name} {{"]
    for n in nodes:
        lines.append(f"  {q(n)};")
    for src, dst in edges:
        lines.append(f"  {q(src)} -> {q(dst)};")
    lines.append("}")
    return "\n".join(lines) + "\n"


def cmd_ctc(args: argparse.Namespace) -> int:
    g = load_digraph(Path(args.graph_json))
    cyc = has_directed_cycle(g)
    if args.json:
        out = {"hasCycle": bool(cyc), "nodeCount": len(g.nodes)}
        print(json.dumps(out, sort_keys=True))
    else:
        print("CYCLE" if cyc else "ACYCLIC")
    return 0


def cmd_dot(args: argparse.Namespace) -> int:
    g = load_digraph(Path(args.graph_json))
    dot = to_dot(g, name=args.name)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(dot)
    print(f"Wrote DOT: {out_path}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="cmd", required=True)

    p_ctc = sub.add_parser("ctc", help="Detect a directed cycle (CTC proxy)")
    p_ctc.add_argument("graph_json", help="Path to JSON file containing edges")
    p_ctc.add_argument("--json", action="store_true", help="Emit machine-readable JSON")
    p_ctc.set_defaults(func=cmd_ctc)

    p_dot = sub.add_parser("dot", help="Export a Graphviz DOT representation")
    p_dot.add_argument("graph_json", help="Path to JSON file containing edges")
    p_dot.add_argument("--out", required=True, help="Output .dot file")
    p_dot.add_argument("--name", default="CausalGraph", help="DOT graph name")
    p_dot.set_defaults(func=cmd_dot)

    return p


def main(argv: Iterable[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(list(argv) if argv is not None else None)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
