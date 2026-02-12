"""poset_homology_proxy.py

Discrete poset/graph homology proxy (Phase 3 helper)
----------------------------------------------------

This script computes a lightweight invariant aligned with the Lean development in
`lean/src/AqeiBridge/PosetHomologyProxy.lean`:

- C₀ is the free module on vertices.
- C₁ is the free module on (directed) edges.
- ∂₁(e : src→dst) = dst - src.

The 1-cycle space Z₁ is ker(∂₁). Over a field (we use ℚ as the model), its
dimension equals:

  dim Z₁ = |E| - rank(∂₁).

For the incidence boundary of a directed graph, rank(∂₁) is |V| - c where c is
#weakly-connected components of the underlying undirected graph, hence

  dim Z₁ = |E| - |V| + c    (and 0 when |V| = 0).

This is *not* a CTC detector: Z₁ can be nontrivial in DAGs (e.g. a diamond).

Subcommands:
- z1: compute proxy data for a graph JSON
- sweep-minkowski: generate a family of Minkowski-ish posets and summarize Z₁
- emit-lean: emit a Lean data/conjecture stub file from summary JSON

All outputs are deterministic.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

# When executed as a script (e.g. `python python/poset_homology_proxy.py`), the local
# `python/` dir isn't necessarily on sys.path.
sys.path.insert(0, str(Path(__file__).resolve().parent))

from causal_graph_tools import DiGraph, has_directed_cycle, load_digraph
from minkowski_poset import build_edges


def _utc_timestamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def _write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def _undirected_components(g: DiGraph) -> int:
    # Underlying undirected adjacency.
    und: dict[str, set[str]] = {n: set() for n in g.nodes}
    for src, dsts in g.adj.items():
        for dst in dsts:
            und.setdefault(src, set()).add(dst)
            und.setdefault(dst, set()).add(src)

    seen: set[str] = set()
    comps = 0
    for start in sorted(g.nodes):
        if start in seen:
            continue
        comps += 1
        stack = [start]
        while stack:
            n = stack.pop()
            if n in seen:
                continue
            seen.add(n)
            for m in und.get(n, set()):
                if m not in seen:
                    stack.append(m)
    return comps


@dataclass(frozen=True)
class Z1Proxy:
    name: str
    node_count: int
    edge_count: int
    weak_component_count: int
    z1_dim: int
    has_directed_cycle: bool

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "nodeCount": int(self.node_count),
            "edgeCount": int(self.edge_count),
            "weakComponentCount": int(self.weak_component_count),
            "z1Dim": int(self.z1_dim),
            "hasDirectedCycle": bool(self.has_directed_cycle),
        }


def compute_z1_proxy(g: DiGraph, *, name: str = "") -> Z1Proxy:
    n = len(g.nodes)
    m = sum(len(g.adj.get(v, frozenset())) for v in g.nodes)
    c = _undirected_components(g) if n > 0 else 0

    # Graph cycle-rank formula (field model): m - n + c.
    z1 = (m - n + c) if n > 0 else 0
    if z1 < 0:
        z1 = 0

    return Z1Proxy(
        name=name,
        node_count=n,
        edge_count=m,
        weak_component_count=c,
        z1_dim=z1,
        has_directed_cycle=has_directed_cycle(g),
    )


def _emit_lean(results: list[Z1Proxy], out_path: Path) -> None:
    max_z1 = max((r.z1_dim for r in results), default=0)

    lines: list[str] = []
    lines.append("/- Auto-generated from python/poset_homology_proxy.py. -/")
    lines.append("import Std")
    lines.append("")
    lines.append("namespace AqeiBridge")
    lines.append("")
    lines.append("structure PosetZ1Result where")
    lines.append("  name : String")
    lines.append("  nodeCount : Nat")
    lines.append("  edgeCount : Nat")
    lines.append("  weakComponentCount : Nat")
    lines.append("  z1Dim : Nat")
    lines.append("  hasDirectedCycle : Bool")
    lines.append("deriving Repr")
    lines.append("")

    lines.append("def posetZ1Results : List PosetZ1Result := [")
    for r in results:
        lines.append("  {")
        lines.append(f"    name := {json.dumps(r.name)},")
        lines.append(f"    nodeCount := {int(r.node_count)},")
        lines.append(f"    edgeCount := {int(r.edge_count)},")
        lines.append(f"    weakComponentCount := {int(r.weak_component_count)},")
        lines.append(f"    z1Dim := {int(r.z1_dim)},")
        lines.append(f"    hasDirectedCycle := {str(bool(r.has_directed_cycle)).lower()}")
        lines.append("  },")
    lines.append("]")
    lines.append("")

    lines.append(f"def posetZ1DimMax : Nat := {int(max_z1)}")
    lines.append("")

    # Skeleton conjectures: intentionally weak placeholders.
    lines.append("/--")
    lines.append("Export certificate skeleton: replace `True` with a real invariant statement.")
    lines.append("-/")
    lines.append("theorem posetZ1Results_exported : True := by")
    lines.append("  trivial")
    lines.append("")

    lines.append("/--")
    lines.append("Conjecture-shaped placeholder for future bound proofs.")
    lines.append("For example, you may want a statement relating `posetZ1DimMax` to a model parameter.")
    lines.append("-/")
    lines.append("theorem conjecture_posetZ1DimMax_bound : True := by")
    lines.append("  trivial")
    lines.append("")

    lines.append("end AqeiBridge")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n")


def cmd_z1(args: argparse.Namespace) -> int:
    g = load_digraph(Path(args.graph_json))
    res = compute_z1_proxy(g, name=str(args.name or ""))
    obj = res.to_json_obj()

    if args.out:
        _write_json(Path(args.out), obj)
        if not args.json:
            print(f"Wrote: {args.out}")

    if args.json or not args.out:
        print(json.dumps(obj, sort_keys=True))
    return 0


def cmd_sweep_minkowski(args: argparse.Namespace) -> int:
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    tmaxs = [int(x.strip()) for x in str(args.tmaxs).split(",") if x.strip()]
    xmaxs = [int(x.strip()) for x in str(args.xmaxs).split(",") if x.strip()]

    results: list[Z1Proxy] = []
    for tmax in tmaxs:
        for xmax in xmaxs:
            name = f"minkowski_t{tmax}_x{xmax}"
            edges = build_edges(tmax=tmax, xmax=xmax)
            graph_path = out_dir / f"{name}.json"
            graph_path.write_text(json.dumps({"edges": edges}, indent=2, sort_keys=True) + "\n")

            # Load via the same path to normalize node IDs.
            g = load_digraph(graph_path)
            results.append(compute_z1_proxy(g, name=name))

    summary = {
        "generatedAtUtc": _utc_timestamp(),
        "count": len(results),
        "results": [r.to_json_obj() for r in results],
    }

    summary_path = out_dir / (args.summary_name or "poset_z1_sweep.json")
    _write_json(summary_path, summary)

    if args.lean_out:
        _emit_lean(results, Path(args.lean_out))
        print(f"Wrote Lean: {args.lean_out}")

    print(f"Wrote: {summary_path}")
    return 0


def cmd_emit_lean(args: argparse.Namespace) -> int:
    src = Path(args.summary_json)
    payload = json.loads(src.read_text())
    raw_results = payload.get("results", [])
    if not isinstance(raw_results, list):
        raise SystemExit("Expected 'results' list in summary JSON")

    results: list[Z1Proxy] = []
    for r in raw_results:
        if not isinstance(r, dict):
            continue
        results.append(
            Z1Proxy(
                name=str(r.get("name", "")),
                node_count=int(r.get("nodeCount", 0)),
                edge_count=int(r.get("edgeCount", 0)),
                weak_component_count=int(r.get("weakComponentCount", 0)),
                z1_dim=int(r.get("z1Dim", 0)),
                has_directed_cycle=bool(r.get("hasDirectedCycle", False)),
            )
        )

    out_path = Path(args.out)
    _emit_lean(results, out_path)
    print(f"Wrote Lean: {out_path}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="cmd", required=True)

    p_z1 = sub.add_parser("z1", help="Compute Z1 proxy data for a graph JSON")
    p_z1.add_argument("graph_json", help="Path to a graph JSON (edges or futures-map)")
    p_z1.add_argument("--name", default="", help="Optional name label")
    p_z1.add_argument("--out", default="", help="Write output JSON to this path")
    p_z1.add_argument("--json", action="store_true", help="Emit machine-readable JSON to stdout")
    p_z1.set_defaults(func=cmd_z1)

    p_sw = sub.add_parser("sweep-minkowski", help="Generate Minkowski-ish posets and summarize Z1")
    p_sw.add_argument("--tmaxs", default="2,3", help="Comma-separated tmax values")
    p_sw.add_argument("--xmaxs", default="2,3", help="Comma-separated xmax values")
    p_sw.add_argument("--out-dir", required=True, help="Directory to write graphs + summary")
    p_sw.add_argument("--summary-name", default="", help="Summary JSON filename")
    p_sw.add_argument(
        "--lean-out",
        default="",
        help="Optional Lean output path (e.g. lean/src/AqeiBridge/GeneratedPosetConjectures.lean)",
    )
    p_sw.set_defaults(func=cmd_sweep_minkowski)

    p_lean = sub.add_parser("emit-lean", help="Emit Lean data/conjecture stubs from sweep summary JSON")
    p_lean.add_argument("summary_json", help="Path to summary JSON produced by sweep-minkowski")
    p_lean.add_argument("--out", required=True, help="Output Lean file path")
    p_lean.set_defaults(func=cmd_emit_lean)

    return p


def main(argv: Iterable[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(list(argv) if argv is not None else None)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
