"""ctc_scan.py

Convenience wrapper for the repo's toy CTC (cycle) diagnostics.

This script is intentionally small and deterministic. It delegates to:
- python/causal_graph_tools.py (cycle detection)
- python/minkowski_poset.py (optional graph generation)

Typical usage:
- Check a saved graph JSON:
    python python/ctc_scan.py --graph path/to/graph.json

- Generate a tiny Minkowski-ish poset and check it is acyclic:
    python python/ctc_scan.py --minkowski --tmax 5 --xmax 5 --out runs/tmp/poset.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

# When executed as a script (e.g. `python python/ctc_scan.py`), the local `python/`
# directory isn't a package on sys.path by default. Add the script's parent dir
# (the repo's `python/` folder) to sys.path so local imports work reliably.
sys.path.insert(0, str(Path(__file__).resolve().parent))

from causal_graph_tools import has_directed_cycle, load_digraph
from minkowski_poset import build_edges


def _write_minkowski_graph_json(out: Path, *, tmax: int, xmax: int) -> None:
    edges = build_edges(tmax=tmax, xmax=xmax)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({"edges": edges}, indent=2, sort_keys=True) + "\n")


def main() -> int:
    p = argparse.ArgumentParser()
    src = p.add_mutually_exclusive_group(required=True)
    src.add_argument("--graph", default="", help="Path to a graph JSON (edges or futures-map)")
    src.add_argument("--minkowski", action="store_true", help="Generate a Minkowski-ish 1+1 poset and scan it")

    p.add_argument("--tmax", type=int, default=5, help="Max time coordinate (inclusive) for --minkowski")
    p.add_argument("--xmax", type=int, default=5, help="Max space coordinate (inclusive) for --minkowski")
    p.add_argument("--out", default="", help="Output path for generated graph JSON (required for --minkowski)")
    p.add_argument("--json", action="store_true", help="Emit machine-readable JSON")

    args = p.parse_args()

    if args.minkowski:
        if not args.out:
            raise SystemExit("--out is required with --minkowski")
        out_path = Path(args.out)
        _write_minkowski_graph_json(out_path, tmax=int(args.tmax), xmax=int(args.xmax))
        graph_path = out_path
    else:
        graph_path = Path(args.graph)

    g = load_digraph(graph_path)
    cyc = has_directed_cycle(g)

    if args.json:
        print(json.dumps({"hasCycle": bool(cyc), "nodeCount": len(g.nodes)}, sort_keys=True))
    else:
        print("CYCLE" if cyc else "ACYCLIC")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
