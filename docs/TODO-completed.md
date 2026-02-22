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

## 2026-02-11 (Lean chamber lemma)
- Added `lean/src/AqeiBridge/Chambers.lean` formalizing a closed-chamber model and proving convex ⇒ path-connected.
- Proved the toy `AQEI_cone` is path-connected assuming feasibility via nonnegative bounds (`0 ≤ B`).
- Wired the module into `lean/src/AqeiBridge.lean` and referenced it in `docs/conjecture.md`.
- Ran `./run_tests.sh` (passes).

## 2026-02-11 (discrete futures constant on chambers)
- Added `lean/src/AqeiBridge/DiscreteChamberStability.lean`: if a parameter-to-`DiscreteSpacetime` map is constant on a chamber, then the induced discrete futures are constant on that chamber (image is a singleton).
- Wired the module into `lean/src/AqeiBridge.lean` and added a short note in `docs/conjecture.md`.
- Ran `./run_tests.sh` (passes).

## 2026-02-11 (chamber-indexed discrete model)
- Added `lean/src/AqeiBridge/ChamberIndexedModel.lean`: constructs `J : StressEnergy n → DiscreteSpacetime Pt` that factors through a chamber index induced by AQEI functionals.
- Proved `J` is constant on each chamber by construction and derived the discrete-future singleton corollary.
- Wired the module into `lean/src/AqeiBridge.lean` and noted it in `docs/conjecture.md`.
- Ran `./run_tests.sh` (passes).

## 2026-02-11 (ClosedChamber ↔ chamberIndex bridge)
- Added `lean/src/AqeiBridge/ChamberClosedChamberBridge.lean` relating the active-set `ClosedChamber` encoding to the sign-pattern `chamberIndex` encoding.
- Proved: `T ∈ ClosedChamber F active` implies `active ⊆ chamberIndex F T`, and on interior points (inactive constraints strict) `chamberIndex F T = active`.
- Wired the module into `lean/src/AqeiBridge.lean` and noted it in `docs/conjecture.md`.
- Ran `./run_tests.sh` (passes).

## 2026-02-11 (Phase 4 ramp-up: docs + sweep tooling)
- Triaged over-scoped Phase 4 items into `docs/TODO-BLOCKED.md` with explicit blockers and next-step concretizations.
- Added `docs/phase4_searches.md` documenting the bounded sweep + aggregation + multi-ray diagnostics workflow.
- `python/sweep_parameters.py`: added `--analyze` to run `python/sweep_analysis.py` automatically after executing a sweep.
- Updated `docs/manuscript.md` with a short “Phase 4: empirical bounds via sweeps (diagnostics)” subsection.
- Updated `README.md` to link the Phase 4 searches doc and clarify blocked scope.
- `tests/python_tests.sh`: ensured the sweep planner smoke test accepts `--analyze`.

## 2026-02-11 (causal-graph diagnostics)
- Added `python/causal_graph_tools.py` (dependency-free) to detect directed cycles (CTC proxy) and export Graphviz DOT.
- Documented the JSON edge format + commands in `docs/phase4_searches.md`.
- Extended `tests/python_tests.sh` with smoke tests for cycle detection and DOT output.
- Updated `docs/TODO-backlog.md` to note that basic multiprocessing exists via `python/sweep_parameters.py --skip-lean --jobs`.
- Ran `./run_tests.sh` (passes).

## 2026-02-11 (poset visualization + futures→graph)
- `python/causal_graph_tools.py`: accept `{"futures": {node: [nodes...]}}` JSON and interpret it as edges.
- Added `python/minkowski_poset.py` to generate a tiny 1+1 discrete poset graph and optionally export DOT.
- Documented the futures-map format and poset generator in `docs/phase4_searches.md`.
- Extended `tests/python_tests.sh` with smoke tests for futures-map input and the poset generator outputs.
- Updated `docs/TODO-backlog.md` to note futures-map support for the CTC proxy.
- Ran `./run_tests.sh` (passes).

## 2026-02-11 (CTC proxy wrapper)
- Added `python/ctc_scan.py` wrapper to scan a graph JSON (edges or futures-map) for directed cycles, or generate a small Minkowski-style poset and confirm it is acyclic.
- Updated `tests/python_tests.sh` with a smoke test covering the wrapper.
- Updated `docs/phase4_searches.md` with a minimal “CTC proxy workflow” example.
- Added a short note to `docs/manuscript.md` pointing at the diagnostic tooling (no new claims).
- Ran `./run_tests.sh` (passes).

## 2026-02-11 (poset interval helper)
- Added `python/poset_interval_tools.py` to compute a toy Alexandrov-style interval $I(p,q)$ on a finite directed graph (reachability-based), with optional induced-subgraph DOT export.
- Documented usage in `docs/phase4_searches.md`.
- Extended `tests/python_tests.sh` with a smoke test for interval JSON + DOT output.
- Ran `./run_tests.sh` (passes).

## 2026-02-11 (Lean: order intervals)
- Added `lean/src/AqeiBridge/CausalIntervals.lean`:
	- order-theoretic past sets `Jminus` and lower sets
	- lower sets are closed in the Alexandrov topology (opens are upper sets)
	- toy interval `Icc(p,q) := {r | p ≤ r ∧ r ≤ q}` and basic lemmas
- Wired the module into `lean/src/AqeiBridge.lean`.
- Ran `./run_tests.sh` (passes).

## 2026-02-12 (Lean: interval topology + continuity substrate)
- `lean/src/AqeiBridge/CausalIntervals.lean`: added `intervalTopology := TopologicalSpace.generateFrom` on the interval subbasis and proved `Icc p q` is open.
- Added `lean/src/AqeiBridge/CausalContinuity.lean`: monotone → continuous for Alexandrov topologies, plus an order-respecting (`le`-based) continuity lemma.
- Added `lean/src/AqeiBridge/DiscreteCausalPoset.lean`: packaged `DiscreteSpacetime` as a reachability `CausalPoset` and proved edge-homomorphisms induce continuous maps.
- Wired new modules into `lean/src/AqeiBridge.lean` and ran `./run_tests.sh` (passes).

## 2026-02-11 (Lean: discrete chronology / cycle proxy)
- Added `lean/src/AqeiBridge/DiscreteChronology.lean`: defined a nontrivial-cycle (CTC proxy) predicate for `DiscreteSpacetime` and proved it is equivalent to failure of antisymmetry for reflexive reachability.
- Wired `AqeiBridge.DiscreteChronology` into `lean/src/AqeiBridge.lean` and ran `./run_tests.sh` (passes).

## 2026-02-11 (Lean: cycle proxy functoriality)
- `lean/src/AqeiBridge/DiscreteChronology.lean`: added `HasDirectedCycle`, `NoSelfEdges`, proved `EdgeHom` preserves `HasDirectedCycle`, and proved `NoSelfEdges ∧ HasDirectedCycle → HasNontrivialCycle`.
- Ran `./run_tests.sh` (passes).

## 2026-02-12 (Lean: homology proxy + global conjecture skeleton)
- Added `lean/src/AqeiBridge/DiscreteHomologyProxy.lean`: defined an incidence boundary `boundary1 : C₁ → C₀` and the 1-cycle space `Z1 := ker boundary1`, plus functoriality under `EdgeHom`.
- Added `lean/src/AqeiBridge/GlobalConjectures.lean`: compilation-safe placeholder for a global “chronology + invariant preservation” statement.
- Updated `docs/manuscript.md` and refined `docs/TODO-BLOCKED.md` to reflect the new unblock path.

## 2026-02-18
- **Publication track manuscript enhancements:**
  - Added "Real-World Applications and Broader Impact" section to `papers/aqei-lean-formalization.tex`
    - Numerical relativity verification (LIGO/VIRGO): H₁ invariance theorem for simulation stability
    - High-precision time synchronization (Deep Space Navigation): Alexandrov topology for certified clock protocols
    - Quantum communication network verification: AQEI cone convexity for causal tampering prevention
  - Added "Integration with Formal Verification" subsection to `papers/aqei-numerical-validation.tex`
    - Documented empirical validation of Lean Theorem 4.1 (100% H₁ invariance over 100 trials)
    - Explained synergy: Lean types ensure Python correctness; empirical results guide proof prioritization
    - Outlined roadmap: computational discovery → conjecture formalization → proof automation → certification
  - Fixed LaTeX compilation issues (removed unused algorithm package)
  - Both manuscripts compile successfully:
    - `aqei-lean-formalization.pdf`: 10 pages
    - `aqei-numerical-validation.pdf`: 12 pages
- **Documentation:**
  - Updated `docs/TODO.md` with Gemini 3 Pro expert analysis of incremental real-world applications
  - Reorganized TODO priorities: manuscript enhancement critical, MATLAB/COMSOL implementation medium priority

## 2026-02-18
- **Publication track manuscript enhancements:**
  - Added "Real-World Applications and Broader Impact" section to papers/aqei-lean-formalization.tex
    - Numerical relativity verification (LIGO/VIRGO): H₁ invariance theorem for simulation stability
    - High-precision time synchronization (Deep Space Navigation): Alexandrov topology for certified clock protocols
    - Quantum communication network verification: AQEI cone convexity for causal tampering prevention
  - Added "Integration with Formal Verification" subsection to papers/aqei-numerical-validation.tex
    - Documented empirical validation of Lean Theorem 4.1 (100% H₁ invariance over 100 trials)
    - Explained synergy: Lean types ensure Python correctness; empirical results guide proof prioritization
    - Outlined roadmap: computational discovery → conjecture formalization → proof automation → certification
  - Fixed LaTeX compilation issues (removed unused algorithm package)
  - Both manuscripts compile successfully:
    - aqei-lean-formalization.pdf: 10 pages
    - aqei-numerical-validation.pdf: 12 pages
- **Documentation:**
  - Updated docs/TODO.md with Gemini 3 Pro expert analysis of incremental real-world applications
  - Reorganized TODO priorities: manuscript enhancement critical, MATLAB/COMSOL implementation medium priority


## 2026-02-22
- **Repository split:** Extracted numerical validation pipeline into standalone repo `aqei-numerical-validation`
  - New repo: https://github.com/arcticoder/aqei-numerical-validation
  - Moved: python numerical scripts (8 scripts), mathematica/ directory, papers/aqei-numerical-validation.tex, docs/h1_stability_results.md, docs/matlab_comsol_integration.md, docs/phase4_searches.md, runs/, tests/python_tests.sh, tests/mathematica_tests.sh, tests/test_pipeline.py
  - Retained in aqei-bridge: lean/, python/orchestrator.py, python/analyze_candidates.py, papers/aqei-lean-formalization.tex, papers/aqei-bridge-hybrid-workflow.md, all formal docs
  - Updated: README.md, run_tests.sh, docs/TODO.md, docs/code-overview.md to reflect split
  - Energy-tensor-cone review: confirmed PRD submission complete (Feb 21), `Candidate_Is_Extreme_Point` proven, provides geometric foundation for bridge conjecture

- **energy-tensor-cone deep review + aqei-bridge adjustments:**
  - Reviewed `AffineToCone.lean`: confirmed homogenization approach embeds affine admissible set as t=1 slice of cone in E×ℝ; all isClosed/convex/cone theorems proven
  - Found `PosetHomologyProxy.lean` H1Map_comp = `homology_functorial` fully proven (no sorry); H1IsoZ1 also proven; updated stale TODO.md entry
  - Added `AQEI_cone_isClosed` to `AQEI_Cone.lean`: proof by list induction, each halfspace closed via `LinearMap.continuous_of_finiteDimensional`; added import `Mathlib.Topology.Algebra.Module.FiniteDimension`
  - Added naming clarification comment to `AQEI_cone`: convex polyhedron NOT homogeneous cone, references energy-tensor-cone/AffineToCone.lean
  - Replaced `axiom admissible_region_pathConnected` with proven theorem: added `hne : (AQEI_cone F).Nonempty` hypothesis, uses `Convex.isPathConnected`; added import `Mathlib.Analysis.Convex.PathConnected`
  - Updated `causal_stability_pathConnected` axiom signature to include `hne` parameter
  - Added 5 missing citations + 5 bibliography entries to `papers/aqei-lean-formalization.tex` (LIGO, Alcubierre numerical GR, Gisin QKD, Ashby GPS, Penrose 1965)
  - Updated `docs/TODO.md`: `homology_functorial` marked ✅ PROVEN, `admissible_region_pathConnected` marked ✅ PROVEN, energy-tensor-cone LOW item updated

- **Proved `h1_stable_small_pert` (HIGH priority TODO):**
  - Created `lean/src/AqeiBridge/H1Stability.lean` with full proof chain:
    - `Edge.ext'`: edge extensionality (proof irrelevance for ok field)
    - `mapEdge_injective`: `mapEdge f hf` injective when vertex map `f` injective
    - `push1_apply_mapEdge`: coefficient extraction identity — `(push1 f hf x)(mapEdge f hf e) = x e`
    - `push1_injective`: `push1 f hf` injective when `f` injective
    - `Z1_eq_bot_of_subgraph`: `Z₁(M₁) = ⊥` follows from `Z₁(M₂) = ⊥ + M₁ ⊆ M₂` (subgraph monotonicity)
    - `dimH1IsZero M`: abbreviation for `Z₁(M, ℤ) = ⊥`
    - `h1_stable_small_pert`: `dimH1IsZero P → EdgeHom P' P id → dimH1IsZero P'`
  - Added import `AqeiBridge.H1Stability` to `lean/src/AqeiBridge.lean`
  - Updated `docs/TODO.md`: `h1_stable_small_pert` marked ✅ PROVEN
  - Added cross-reference comment in `GlobalConjectures.lean` linking to energy-tensor-cone extreme-point result and `h1_stable_small_pert`
