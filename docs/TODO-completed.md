# TODO — completed

(Entries moved here from docs/TODO.md as they are completed.)

## 2026-02-09
- Created `docs/` directory and moved the active TODO tracking here.
- Added `docs/architecture.md` (4-stage pipeline + mermaid diagram).
- Added `docs/conjecture.md` (precise bridge conjecture statement; formal vs heuristic separation).
- Added `docs/toy-model.md` (1+1 toy model assumptions + Δ proxy explanation).
- Expanded README with debugging / common failure modes.
- Added repo-level `run_tests.sh` to run python/mathematica/lean smoke tests.
- Added `docs/TODO-completed.md` and `docs/TODO-BLOCKED.md`.

## 2026-02-09 (later)
- Added timestamped run persistence in `runs/<UTC timestamp>/run.json` via `python/orchestrator.py`.
- Added `tests/test_pipeline.py` (unittest end-to-end smoke test) and wired it into `tests/python_tests.sh`.

## 2026-02-10
- Migrated long-term checklist items into `docs/TODO-backlog.md` so `docs/TODO.md` can remain empty as the active-queue file.

## 2026-02-10 (later)
- Added `--test-mode` flag support in `mathematica/search.wl` and expanded `run_tests.sh` to run explicit smoke checks (`lake build`, Mathematica test-mode, unittest discovery).
- Started `docs/manuscript.md` with a structured outline aligned to `energy-tensor-cone/papers/` style.
- Tightened Phase 2 Lean skeletons:
	- `Spacetime.lean`: added abstract `CausalCurve`/`Jplus` interface and a neighborhood hook.
	- `StressEnergy.lean`: made `StressEnergyTensor` a symmetric matrix; added `LinearizedEinstein` placeholder.
	- `AQEI_Cone.lean`: added a sampling-based `mkFunctionals` helper.
	- `CausalStability.lean`: added an `IsPathConnected` skeleton statement for the admissible region.

## 2026-02-11
- Added MIT `LICENSE` and mentioned it in the README.
- Added `lean/src/AqeiBridge/CausalPoset.lean` with a causal preorder interface and an Alexandrov-style topology (opens are upper sets).
- Proved basic lemmas in `CausalPoset.lean`, including that order-futures (`Jplus`) are open and a monotonicity/antitone property.
- Wired `AqeiBridge.CausalPoset` into `lean/src/AqeiBridge.lean`.
- Updated `docs/manuscript.md` with a short causal-poset/Alexandrov-topology bridge section.
- Updated `docs/TODO-BLOCKED.md` to reflect that the topology substrate exists; remaining cohomology/sheaf step is blocked on choosing a target invariant.
- Made `python/orchestrator.py` pass `--test-mode` to Mathematica when `AQEI_TEST_MODE=1` (used by the end-to-end unit test).

## 2026-02-10
- Added `lean/src/AqeiBridge/SpacetimeCausalPoset.lean` connecting the abstract `Spacetime` causal relation to `CausalPoset` under explicit preorder axioms.
- Added `Spacetime.alexandrovTopology` and proved `isOpen_Jplus_order` by reuse of the order-theoretic lemma.
- Wired `AqeiBridge.SpacetimeCausalPoset` into the top-level import file.
- Updated `docs/manuscript.md` with an explicit “axioms → Alexandrov topology” implementation note.
- Made `tests/mathematica_tests.sh` always run `search.wl` in `--test-mode` to keep `./run_tests.sh` fast.

## 2026-02-10 (later)
- `StressEnergy.lean`: added `StressEnergyTensor.toPerturbation` convenience definition (still a placeholder via `LinearizedEinstein`).
- `AQEI_Cone.lean`: simplified the convexity proof to avoid unused simp-arg lint noise.
- `CausalStability.lean`: introduced typed placeholders for `PerturbedFutures` and `InvariantHomotopyClass`, plus a conjecture-shaped interface axiom mentioning them.
- `docs/manuscript.md`: added an explicit $J^+(p)$ formula and a short “pivot” note about interpreting null results.
- `README.md`: added a brief “Recent progress” note.
- Ran `./run_tests.sh` (passes).

## 2026-02-10 (phase-3 helpers)
- `python/analyze_candidates.py`: emit `maxScore` / `maxScoreRay` metadata into the generated Lean artifact.
- Added `python/sweep_parameters.py` (supports `--dry-run` and defaults to `AQEI_TEST_MODE=1` when executing).
- `tests/python_tests.sh`: smoke-test sweep planner in dry-run mode.
- Added `mathematica/visualize_results.wl` and extended Mathematica tests to generate a PNG plot.
- `mathematica/search.wl`: added optional `--geodesic` observable mode (default off; keeps LP structure by per-basis linearization).
- Ran `./run_tests.sh` (passes).

## 2026-02-11 (multi-ray + sweep aggregation)
- `python/orchestrator.py`: archive per-run artifacts under `runs/<ts>/artifacts/` and record archived paths in `runs/<ts>/run.json`.
- `python/sweep_parameters.py`: on execution, write `runs/sweeps/<ts>/index.json` pointing to each run’s `runs/<run_ts>/run.json`.
- Added `python/multi_ray_analysis.py` (Jaccard overlap + connected components proxy over `activeConstraints`).
- Added `python/sweep_analysis.py` (reads sweep index + run records; computes per-point `maxScore` from candidates JSON).
- Extended `tests/python_tests.sh` with smoke tests for both analysis scripts.
- Ran `./run_tests.sh` (passes).

## 2026-02-10 (geodesic ndsolve + bounds + meshgrid)
- `mathematica/search.wl`: added `--geodesic-ndsolve` mode using an NDSolve ODE proxy closer to $x'' + \Gamma(x) (x')^2 = 0$ (still linearized per-basis weights).
- `tests/mathematica_tests.sh`: exercised `--geodesic-ndsolve` in `--test-mode`.
- `python/multi_ray_analysis.py`: added `--thresholds` sweep output (components vs. threshold) as a lightweight 0th-persistence proxy.
- `python/analyze_candidates.py`: emit `maxScoreUpperRat : Rat` and a placeholder bound theorem in the generated Lean artifact.
- `python/sweep_parameters.py`: added `--grids` (comma-separated) meshgrid support while preserving `--grid`.
- Ran `./run_tests.sh` (passes).

## 2026-02-11 (connectedness proxy + docs)
- `python/multi_ray_analysis.py`: emit an explicit `connectedness` summary (mean pairwise Jaccard; fraction of ray-pairs above `theta`), add `--theta`, and (optionally) derive a crude `connectivityThreshold` from `--thresholds`.
- `docs/manuscript.md`: document the connectedness proxy as heuristic computational evidence (not a proof/invariant).
- `README.md`: mention the connectedness proxy and point Phase 4 scope to `docs/TODO-BLOCKED.md`.
- `docs/TODO-BLOCKED.md`: moved over-scoped Phase 4 items out of the active queue with concrete blockers.
- `tests/python_tests.sh`: extend the multi-ray smoke test to pass `--theta` and assert the new JSON fields.
- Drained `docs/TODO.md` back to empty after completion.

## 2026-02-11 (parallel-safe outputs + proof-plan notes)
- `mathematica/search.wl`: honor `AQEI_RESULTS_DIR` to isolate per-run JSON outputs.
- `python/analyze_candidates.py`: add `--results-dir` and `--out` CLI args (defaults unchanged).
- `python/orchestrator.py`: plumb per-run results/output paths and add `skip_lean` plumbing for sweep-friendly execution.
- `python/sweep_parameters.py`: add `--skip-lean` and `--jobs` (rejects `--jobs>1` without `--skip-lean`).
- `python/multi_ray_analysis.py`: add `--dot-out` to emit a Graphviz DOT overlap graph at the chosen Jaccard threshold.
- `docs/conjecture.md`: add a short “toward proof” section connecting chambers/local constancy to the heuristic diagnostics.
- `tests/python_tests.sh`: smoke-test the new analyze-candidates CLI and DOT output.
- Ran `./run_tests.sh` (passes).
