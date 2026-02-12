"""poset_interval_tools.py

Compute simple order-interval (Alexandrov interval) diagnostics on a finite directed graph.

This is intentionally dependency-free and operates on the same JSON formats as
`python/causal_graph_tools.py`:
- {"edges": [[src, dst], ...]}  (or objects {"src":..., "dst":...})
- {"futures": {node: [nodes...]}}

The interval computed here is a *toy* Alexandrov-style interval:

  I(p, q) := { r | p ->* r and r ->* q }

where ->* is reachability in the directed graph. Endpoints are included.

Subcommands:
- interval: compute I(p,q) and print/write JSON; optionally export an induced DOT.
"""

from __future__ import annotations

import argparse
import json
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

from causal_graph_tools import DiGraph, _to_node_id, load_digraph, to_dot


@dataclass(frozen=True)
class IntervalResult:
    p: str
    q: str
    interval_nodes: tuple[str, ...]

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "p": self.p,
            "q": self.q,
            "intervalNodes": list(self.interval_nodes),
            "intervalSize": len(self.interval_nodes),
        }


def _parse_node_arg(raw: str) -> Any:
    """Parse --p/--q args.

    Accepts JSON literals (e.g. '"a"', '[2,3]') or bare strings ('a').
    """

    try:
        return json.loads(raw)
    except json.JSONDecodeError:
        return raw


def _reachable_from(g: DiGraph, start: str) -> frozenset[str]:
    seen: set[str] = set()
    q: deque[str] = deque([start])
    while q:
        n = q.popleft()
        if n in seen:
            continue
        seen.add(n)
        for m in g.adj.get(n, frozenset()):
            if m not in seen:
                q.append(m)
    return frozenset(seen)


def _reverse_graph(g: DiGraph) -> DiGraph:
    rev_adj: dict[str, set[str]] = {n: set() for n in g.nodes}
    for src, nbrs in g.adj.items():
        for dst in nbrs:
            rev_adj[dst].add(src)
    return DiGraph(nodes=g.nodes, adj={n: frozenset(rev_adj[n]) for n in g.nodes})


def compute_interval(g: DiGraph, p: str, q: str) -> IntervalResult:
    if p not in g.nodes:
        raise ValueError(f"Node p not in graph: {p}")
    if q not in g.nodes:
        raise ValueError(f"Node q not in graph: {q}")

    fwd = _reachable_from(g, p)
    rev = _reachable_from(_reverse_graph(g), q)
    interval = sorted(fwd.intersection(rev))
    return IntervalResult(p=p, q=q, interval_nodes=tuple(interval))


def _induced_subgraph(g: DiGraph, nodes: frozenset[str]) -> DiGraph:
    adj: dict[str, frozenset[str]] = {}
    for n in nodes:
        adj[n] = frozenset(m for m in g.adj.get(n, frozenset()) if m in nodes)
    return DiGraph(nodes=frozenset(nodes), adj=adj)


def cmd_interval(args: argparse.Namespace) -> int:
    g = load_digraph(Path(args.graph_json))

    p_obj = _parse_node_arg(args.p)
    q_obj = _parse_node_arg(args.q)
    p = _to_node_id(p_obj)
    q = _to_node_id(q_obj)

    res = compute_interval(g, p, q)
    obj = res.to_json_obj()

    if args.out is not None:
        out_path = Path(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(obj, sort_keys=True) + "\n")
        if not args.json:
            print(f"Wrote: {out_path}")

    if args.dot_out is not None:
        nodes = frozenset(res.interval_nodes)
        sub = _induced_subgraph(g, nodes)
        dot = to_dot(sub, name=args.name)
        dot_path = Path(args.dot_out)
        dot_path.parent.mkdir(parents=True, exist_ok=True)
        dot_path.write_text(dot)
        if not args.json:
            print(f"Wrote DOT: {dot_path}")

    if args.json:
        print(json.dumps(obj, sort_keys=True))
    return 0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="cmd", required=True)

    p_int = sub.add_parser("interval", help="Compute the Alexandrov-style interval I(p,q)")
    p_int.add_argument("graph_json", help="Path to JSON file containing edges or futures")
    p_int.add_argument("--p", required=True, help="Node p (JSON literal or bare string)")
    p_int.add_argument("--q", required=True, help="Node q (JSON literal or bare string)")
    p_int.add_argument("--out", help="Write output JSON to this path")
    p_int.add_argument("--json", action="store_true", help="Emit machine-readable JSON to stdout")
    p_int.add_argument("--dot-out", help="Write induced-subgraph DOT to this path")
    p_int.add_argument("--name", default="Interval", help="DOT graph name")
    p_int.set_defaults(func=cmd_interval)

    return p


def main(argv: Iterable[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(list(argv) if argv is not None else None)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
