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
import random
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


def _digraph_from_nodes_edges(nodes: Iterable[str], edges: Iterable[tuple[str, str]]) -> DiGraph:
    # Preserve isolated nodes (important for comparing perturbations).
    node_set = frozenset(nodes)
    tmp_adj: dict[str, set[str]] = {n: set() for n in node_set}
    for src, dst in edges:
        if src not in tmp_adj:
            tmp_adj[src] = set()
        tmp_adj[src].add(dst)
    adj: dict[str, frozenset[str]] = {n: frozenset(tmp_adj.get(n, set())) for n in node_set}
    return DiGraph(nodes=node_set, adj=adj)


def _sorted_edges(g: DiGraph) -> list[tuple[str, str]]:
    edges: list[tuple[str, str]] = []
    for src in sorted(g.nodes):
        for dst in sorted(g.adj.get(src, frozenset())):
            edges.append((src, dst))
    return edges


def _lowpass_smooth_cyclic(values: list[float], *, window: int) -> list[float]:
    """Toy FFT-like smoothing, implemented dependency-free.

    This is a simple cyclic moving-average low-pass filter.
    """

    n = len(values)
    if n == 0:
        return []
    if window <= 1:
        return list(values)
    if window > n:
        window = n
    if window % 2 == 0:
        window += 1
        if window > n:
            window = n if n % 2 == 1 else max(1, n - 1)

    k = window // 2
    out: list[float] = []
    for i in range(n):
        s = 0.0
        for j in range(-k, k + 1):
            s += values[(i + j) % n]
        out.append(s / float(2 * k + 1))
    return out


def _event_node_id(t: int, x: int) -> str:
    # Match causal_graph_tools._to_node_id for non-string nodes.
    return json.dumps([int(t), int(x)], sort_keys=True)


def _minkowski_nodes(tmax: int, xmax: int) -> list[str]:
    nodes: list[str] = []
    for t in range(tmax + 1):
        for x in range(xmax + 1):
            nodes.append(_event_node_id(t, x))
    return nodes


def _minkowski_edges_step_cone(*, tmax: int, xmax: int, radius_fn: callable | None = None) -> list[tuple[str, str]]:
    """Build directed edges (t increases by 1) with a local step-cone radius.

    Baseline corresponds to radius 1 everywhere, matching minkowski_poset.build_edges.
    """

    edges: list[tuple[str, str]] = []
    for t in range(tmax + 1):
        for x in range(xmax + 1):
            if t == tmax:
                continue
            r = int(radius_fn(t, x)) if radius_fn is not None else 1
            if r < 0:
                r = 0
            for dx in range(-r, r + 1):
                xx = x + dx
                if 0 <= xx <= xmax:
                    edges.append((_event_node_id(t, x), _event_node_id(t + 1, xx)))

    edges.sort(key=lambda e: (e[0], e[1]))
    return edges


def _parse_csv_floats(s: str) -> list[float]:
    items = [x.strip() for x in str(s).split(",") if x.strip()]
    return [float(x) for x in items]


def _parse_csv_ints(s: str) -> list[int]:
    items = [x.strip() for x in str(s).split(",") if x.strip()]
    return [int(x) for x in items]


def _minkowski_perturb_payload(
    *,
    tmax: int,
    xmax: int,
    trials: int,
    epsilon: float,
    cutoff: float,
    window: int,
    seed: int,
) -> dict[str, Any]:
    nodes0 = _minkowski_nodes(tmax, xmax)

    base_edges = _minkowski_edges_step_cone(tmax=tmax, xmax=xmax)
    base_g = _digraph_from_nodes_edges(nodes0, base_edges)
    base = compute_z1_proxy(base_g, name=f"minkowski_t{tmax}_x{xmax}_baseline")

    rng = random.Random(int(seed))
    trial_rows: list[dict[str, Any]] = []
    deltas: list[int] = []

    node_count = len(nodes0)
    for trial in range(int(trials)):
        noise = [rng.normalvariate(0.0, 1.0) for _ in range(node_count)]
        smooth = _lowpass_smooth_cyclic(noise, window=int(window))

        def radius_fn(t: int, x: int) -> int:
            idx = t * (xmax + 1) + x
            z = smooth[idx]
            return 2 if (float(epsilon) * z) >= float(cutoff) else 1

        edges = _minkowski_edges_step_cone(tmax=tmax, xmax=xmax, radius_fn=radius_fn)
        g1 = _digraph_from_nodes_edges(nodes0, edges)
        res = compute_z1_proxy(g1, name=f"trial_{trial}")

        dz = int(res.z1_dim - base.z1_dim)
        deltas.append(abs(dz))
        trial_rows.append(
            {
                "trial": int(trial),
                "edgeCount": int(res.edge_count),
                "weakComponentCount": int(res.weak_component_count),
                "z1Dim": int(res.z1_dim),
                "deltaZ1": int(dz),
                "hasDirectedCycle": bool(res.has_directed_cycle),
            }
        )

    mean_delta = (sum(deltas) / float(len(deltas))) if deltas else 0.0
    max_delta = max(deltas) if deltas else 0
    unchanged = sum(1 for d in deltas if d == 0)
    frac_unchanged = (unchanged / float(len(deltas))) if deltas else 0.0

    return {
        "generatedAtUtc": _utc_timestamp(),
        "baseline": base.to_json_obj(),
        "grid": {"tmax": int(tmax), "xmax": int(xmax)},
        "params": {
            "trials": int(trials),
            "epsilon": float(epsilon),
            "cutoff": float(cutoff),
            "window": int(window),
            "seed": int(seed),
            "radius": {"base": 1, "perturbed": 2},
        },
        "trialsData": trial_rows,
        "summary": {
            "meanAbsDeltaZ1": float(mean_delta),
            "maxAbsDeltaZ1": int(max_delta),
            "fractionUnchanged": float(frac_unchanged),
        },
    }


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


def cmd_perturb_fft(args: argparse.Namespace) -> int:
    """Empirical stability sweep for Z1 under toy "FFT" perturbations.

    We model a perturbation as: assign each edge a baseline weight 1.0, add
    smoothed (low-pass) noise, then *drop* edges whose perturbed weight falls
    below a threshold. This changes the edge set, hence changes the boundary
    matrix and its kernel dimension.
    """

    g0 = load_digraph(Path(args.graph_json))
    base = compute_z1_proxy(g0, name=str(args.name or ""))

    nodes0 = sorted(g0.nodes)
    edges0 = _sorted_edges(g0)
    m0 = len(edges0)

    trials = int(args.trials)
    if trials <= 0:
        raise SystemExit("--trials must be positive")

    epsilon = float(args.epsilon)
    threshold = float(args.threshold)
    window = int(args.window)
    seed = int(args.seed)

    rng = random.Random(seed)

    trial_rows: list[dict[str, Any]] = []
    deltas: list[int] = []

    for trial in range(trials):
        noise = [rng.normalvariate(0.0, 1.0) for _ in range(m0)]
        smooth = _lowpass_smooth_cyclic(noise, window=window)

        kept: list[tuple[str, str]] = []
        for (src, dst), z in zip(edges0, smooth):
            w = 1.0 + epsilon * z
            if w >= threshold:
                kept.append((src, dst))

        g1 = _digraph_from_nodes_edges(nodes0, kept)
        res = compute_z1_proxy(g1, name=f"trial_{trial}")
        dz = int(res.z1_dim - base.z1_dim)
        deltas.append(abs(dz))

        trial_rows.append(
            {
                "trial": int(trial),
                "edgeCount": int(res.edge_count),
                "weakComponentCount": int(res.weak_component_count),
                "z1Dim": int(res.z1_dim),
                "deltaZ1": int(dz),
                "hasDirectedCycle": bool(res.has_directed_cycle),
            }
        )

    mean_delta = (sum(deltas) / float(len(deltas))) if deltas else 0.0
    max_delta = max(deltas) if deltas else 0
    unchanged = sum(1 for d in deltas if d == 0)
    frac_unchanged = (unchanged / float(len(deltas))) if deltas else 0.0

    payload: dict[str, Any] = {
        "generatedAtUtc": _utc_timestamp(),
        "name": str(args.name or ""),
        "baseline": base.to_json_obj(),
        "params": {
            "trials": int(trials),
            "epsilon": float(epsilon),
            "threshold": float(threshold),
            "window": int(window),
            "seed": int(seed),
        },
        "trialsData": trial_rows,
        "summary": {
            "meanAbsDeltaZ1": float(mean_delta),
            "maxAbsDeltaZ1": int(max_delta),
            "fractionUnchanged": float(frac_unchanged),
        },
    }

    if args.out:
        _write_json(Path(args.out), payload)
        if not args.json:
            print(f"Wrote: {args.out}")

    if args.json or not args.out:
        print(json.dumps(payload, sort_keys=True))

    return 0


def cmd_sweep_minkowski_perturb(args: argparse.Namespace) -> int:
    """Empirical sweep: Minkowski-ish grid posets under a toy smooth perturbation.

    The perturbation is intentionally simple and computable:
    - Sample i.i.d. Gaussian noise on nodes.
    - Apply a cyclic moving-average low-pass filter ("FFT-like") to the node field.
    - Widen the local step-cone from radius 1 to radius 2 when the filtered field
      crosses a cutoff.

    This changes the edge set, and therefore changes Z1 via |E|-|V|+c.
    """

    tmax = int(args.tmax)
    xmax = int(args.xmax)
    if tmax < 0 or xmax < 0:
        raise SystemExit("--tmax and --xmax must be nonnegative")

    trials = int(args.trials)
    if trials <= 0:
        raise SystemExit("--trials must be positive")

    epsilon = float(args.epsilon)
    cutoff = float(args.cutoff)
    window = int(args.window)
    seed = int(args.seed)

    payload = _minkowski_perturb_payload(
        tmax=tmax,
        xmax=xmax,
        trials=trials,
        epsilon=epsilon,
        cutoff=cutoff,
        window=window,
        seed=seed,
    )

    if args.out:
        _write_json(Path(args.out), payload)
        if not args.json:
            print(f"Wrote: {args.out}")

    if args.json or not args.out:
        print(json.dumps(payload, sort_keys=True))

    return 0


def cmd_scan_minkowski_perturb(args: argparse.Namespace) -> int:
    tmax = int(args.tmax)
    xmax = int(args.xmax)
    trials = int(args.trials)
    if tmax < 0 or xmax < 0:
        raise SystemExit("--tmax and --xmax must be nonnegative")
    if trials <= 0:
        raise SystemExit("--trials must be positive")

    epsilons = _parse_csv_floats(args.epsilons)
    cutoffs = _parse_csv_floats(args.cutoffs)
    windows = _parse_csv_ints(args.windows)
    seed = int(args.seed)

    points: list[dict[str, Any]] = []
    idx = 0
    for epsilon in epsilons:
        for cutoff in cutoffs:
            for window in windows:
                point_seed = seed + 1000003 * idx
                payload = _minkowski_perturb_payload(
                    tmax=tmax,
                    xmax=xmax,
                    trials=trials,
                    epsilon=float(epsilon),
                    cutoff=float(cutoff),
                    window=int(window),
                    seed=int(point_seed),
                )
                points.append(
                    {
                        "params": payload["params"],
                        "summary": payload["summary"],
                    }
                )
                idx += 1

    out_payload: dict[str, Any] = {
        "generatedAtUtc": _utc_timestamp(),
        "grid": {"tmax": int(tmax), "xmax": int(xmax)},
        "sweep": {
            "trials": int(trials),
            "epsilons": epsilons,
            "cutoffs": cutoffs,
            "windows": windows,
            "seed": int(seed),
        },
        "count": int(len(points)),
        "points": points,
    }

    if args.out:
        _write_json(Path(args.out), out_payload)
        if not args.json:
            print(f"Wrote: {args.out}")

    if args.json or not args.out:
        print(json.dumps(out_payload, sort_keys=True))

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

    p_pert = sub.add_parser(
        "perturb-fft",
        help="Toy FFT-like perturbation sweep: drop edges after low-pass noise and measure Z1 stability",
    )
    p_pert.add_argument("graph_json", help="Path to a graph JSON (edges or futures-map)")
    p_pert.add_argument("--name", default="", help="Optional name label")
    p_pert.add_argument("--trials", type=int, default=20, help="Number of perturbation trials")
    p_pert.add_argument("--epsilon", type=float, default=0.05, help="Noise amplitude")
    p_pert.add_argument(
        "--threshold",
        type=float,
        default=0.5,
        help="Keep an edge iff perturbed weight >= threshold (baseline weight is 1.0)",
    )
    p_pert.add_argument("--window", type=int, default=9, help="Low-pass smoothing window (odd preferred)")
    p_pert.add_argument("--seed", type=int, default=0, help="PRNG seed (deterministic)")
    p_pert.add_argument("--out", default="", help="Write output JSON to this path")
    p_pert.add_argument("--json", action="store_true", help="Emit machine-readable JSON to stdout")
    p_pert.set_defaults(func=cmd_perturb_fft)

    p_mink_pert = sub.add_parser(
        "sweep-minkowski-perturb",
        help="Minkowski-ish sweep under smooth perturbations (local cone widening) and Z1 stability stats",
    )
    p_mink_pert.add_argument("--tmax", type=int, default=3, help="Max time coordinate (inclusive)")
    p_mink_pert.add_argument("--xmax", type=int, default=3, help="Max space coordinate (inclusive)")
    p_mink_pert.add_argument("--trials", type=int, default=20, help="Number of perturbation trials")
    p_mink_pert.add_argument("--epsilon", type=float, default=0.2, help="Noise amplitude")
    p_mink_pert.add_argument("--cutoff", type=float, default=0.0, help="Widen cone when epsilon*z >= cutoff")
    p_mink_pert.add_argument("--window", type=int, default=9, help="Low-pass smoothing window")
    p_mink_pert.add_argument("--seed", type=int, default=0, help="PRNG seed (deterministic)")
    p_mink_pert.add_argument("--out", default="", help="Write output JSON to this path")
    p_mink_pert.add_argument("--json", action="store_true", help="Emit machine-readable JSON to stdout")
    p_mink_pert.set_defaults(func=cmd_sweep_minkowski_perturb)

    p_scan = sub.add_parser(
        "scan-minkowski-perturb",
        help="Scan (epsilon, cutoff, window) grids for Minkowski perturbation stability",
    )
    p_scan.add_argument("--tmax", type=int, default=3, help="Max time coordinate (inclusive)")
    p_scan.add_argument("--xmax", type=int, default=3, help="Max space coordinate (inclusive)")
    p_scan.add_argument("--trials", type=int, default=20, help="Trials per grid point")
    p_scan.add_argument("--epsilons", default="0.0,0.2", help="Comma-separated epsilon values")
    p_scan.add_argument("--cutoffs", default="0.0", help="Comma-separated cutoff values")
    p_scan.add_argument("--windows", default="9", help="Comma-separated smoothing-window values")
    p_scan.add_argument("--seed", type=int, default=0, help="Master PRNG seed")
    p_scan.add_argument("--out", default="", help="Write output JSON to this path")
    p_scan.add_argument("--json", action="store_true", help="Emit machine-readable JSON to stdout")
    p_scan.set_defaults(func=cmd_scan_minkowski_perturb)

    return p


def main(argv: Iterable[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(list(argv) if argv is not None else None)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
