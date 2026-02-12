# Phase 4: Search workflow (empirical bounds + diagnostics)

This repo’s “large-scale searches” are intentionally framed as **diagnostics**:
they produce reproducible artifacts under `runs/` that help us decide whether the
toy observable Δ appears bounded under AQEI-like constraints.

They are not proofs of causal stability, and they do not establish continuity of
Lorentzian $J^+$. See `docs/conjecture.md` for the formal vs heuristic separation.

## What we measure (toy)

- Mathematica computes a proxy objective (Δ) in the current 1+1 toy model and
  outputs candidate solutions with per-ray scores.
- Python aggregates and summarizes:
  - per-run best score (`maxScore`, `maxScoreRay`),
  - multi-ray “connectedness proxy” via Jaccard overlap of active constraints.

Interpretation caveat:
- a bounded `maxScore` across a parameter family is only evidence that the
  **toy proxy** is bounded in that regime.

## Run a sweep (bounded, reproducible)

Use `python/sweep_parameters.py` to create and execute a parameter grid.

Dry-run (writes a plan JSON only):

`python python/sweep_parameters.py --dry-run --nbasis 2,3,4 --sigmas 0.6,0.7,0.8 --grids 16,32`

Execute (recommended defaults):

- default execution forces `AQEI_TEST_MODE=1` unless `--full` is passed
- add `--skip-lean` for speed; use `--jobs` only with `--skip-lean`

Example:

`python python/sweep_parameters.py --nbasis 2,3,4 --sigmas 0.6,0.7,0.8 --grids 16,32 --skip-lean --jobs 4 --analyze`

Artifacts:

- `runs/sweeps/<UTC>/sweep_plan.json`
- `runs/sweeps/<UTC>/index.json` (points → per-run `run.json`)
- `runs/sweeps/<UTC>/sweep_summary.json` (if `--analyze` was used)

## Aggregate sweep results

If you didn’t use `--analyze`, you can aggregate later:

`python python/sweep_analysis.py --index runs/sweeps/<UTC>/index.json`

This writes `runs/sweeps/<UTC>/sweep_summary.json` by default.

## Multi-ray diagnostics (within a run)

Given a run’s `top_candidates.json`, produce overlap summaries and an optional
Graphviz DOT file:

`python python/multi_ray_analysis.py --candidates runs/<run>/artifacts/top_candidates.json --out runs/<run>/artifacts/multi_ray.json --threshold 0.2 --theta 0.2 --dot-out runs/<run>/artifacts/multi_ray.dot`

## Causal-graph diagnostics (toy)

For future discrete/toy causal-set experiments, `python/causal_graph_tools.py` provides two
dependency-free helpers:

- **CTC proxy**: detects whether a directed graph contains a cycle.
- **Visualization**: exports a Graphviz DOT file.

Input JSON formats:

- Explicit edges:

`{"edges": [["a","b"], ["b","c"]]}`

- Futures map (convenient when you already have $J^+(p)$ samples):

`{"futures": {"a": ["b","c"], "b": ["c"]}}`

Commands:

`python python/causal_graph_tools.py ctc path/to/graph.json`

`python python/causal_graph_tools.py dot path/to/graph.json --out path/to/graph.dot`

### Generate a small 1+1 poset graph

For quick visualization without external dependencies, generate a tiny discrete causal graph:

`python python/minkowski_poset.py --tmax 5 --xmax 5 --out runs/tmp/poset.json --dot-out runs/tmp/poset.dot`

This uses local “future-step” edges (a simple reachability proxy), and is meant for diagnostics only.

### CTC proxy workflow (toy)

Generate a small 1+1 poset and scan it for cycles:

`python python/ctc_scan.py --minkowski --tmax 5 --xmax 5 --out runs/tmp/poset.json`

Or scan an existing graph JSON:

`python python/ctc_scan.py --graph path/to/graph.json`

## Reporting guidelines

When writing up Phase 4 results in `docs/manuscript.md`:

- report sweep families (grid/basis/sigma ranges) and execution mode (`--test-mode` vs `--full`)
- report bounds as empirical maxima over those families (not as theorems)
- track any sharp transitions in active-set overlap as a lead for refining constraints/observables
