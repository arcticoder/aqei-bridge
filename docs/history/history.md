**Repo + workspace wiring**
- Created public repo https://github.com/arcticoder/aqei-bridge and cloned it into `~/Code/asciimath/aqei-bridge`.
- Set local git identity in the repo via `git config user.name "Arcticoder"` and `git config user.email "10162808+arcticoder@users.noreply.github.com"`.
- Added the folder to energy/energy.code-workspace directly under the `energy (main)` entry.

**4-stage pipeline implemented (end-to-end runnable)**
- **Lean (Stage I)**: lean is a Lake project pinned to Lean `v4.27.0` + Mathlib.
  - Core skeletons live under:
    - lean/src/AqeiBridge/Spacetime.lean
    - lean/src/AqeiBridge/StressEnergy.lean
    - lean/src/AqeiBridge/AQEI_Cone.lean (includes a proved `AQEI_cone_convex`)
    - lean/src/AqeiBridge/CausalStability.lean (typed conjecture skeletons; marked as placeholders)
    - lean/src/AqeiBridge/Tactics/Linear.lean
- **Mathematica (Stages II–III heuristic search)**:
  - mathematica/search.wl implements the 1+1 toy model: Gaussian basis → FFT Green multiplier → ray-integrated Δ proxy → LP maximize Δ subject to synthetic AQEI halfspace constraints.
  - Writes JSON outputs under results (`summary.json`, top_candidates.json).
- **Python orchestration (Stage IV)**:
  - python/orchestrator.py runs: Mathematica → candidate export → `lake build`.
  - python/analyze_candidates.py reads Mathematica JSON, rationalizes floats via `Fraction(...).limit_denominator`, and overwrites lean/src/AqeiBridge/GeneratedCandidates.lean.

**Tests**
- Added lightweight runners in tests/ mirroring the `energy-tensor-cone` style:
  - python_tests.sh, mathematica_tests.sh, lean_tests.sh, build_lean.sh
- Verified locally: Mathematica smoke test passes, Lean build passes, and the full orchestrator runs through to completion.
<!-- ------ -->
---
The `history/` directory has been successfully moved into the docs directory using `git mv`, and the change has been committed to the repository. The file `history.md` is now located at history.md.
<!-- ------ -->
---
**What changed**
- Fixed and committed the Lean formalization chunk:
  - Added a fully formal discrete causality toy model in lean/src/AqeiBridge/DiscreteCausality.lean.
  - Added an abstract conjecture “interface” in lean/src/AqeiBridge/Conjecture.lean (parameterized over the discrete model).
  - Repaired and extended lean/src/AqeiBridge/StressEnergy.lean and added a `StressEnergyTensor` placeholder.
  - Updated lean/src/AqeiBridge.lean imports.
- Cleaned up generated artifacts so runs don’t dirty git:
  - Updated aqei-bridge/.gitignore to ignore runs and treat GeneratedCandidates.lean as generated.
  - Untracked the generated GeneratedCandidates.lean file (it still gets produced at runtime when the pipeline runs).

**Build status**
- `lake build` now succeeds (warnings only).

**TODO.md draining**
- Migrated the long-term checklist into docs/TODO-backlog.md.
- Left docs/TODO.md truly empty; `wc -l docs/TODO.md` returns `0`.
- Noted the migration in docs/TODO-completed.md.

**Commits**
- `d6bb377` — “lean: discrete causality toy + conjecture interface”
- `f0af35b` — “docs: migrate TODO backlog”
<!-- ------ -->
---
**Done (and committed)**
- Tests + CLI knobs
  - Added `--test-mode` support to mathematica/search.wl.
  - Expanded run_tests.sh to explicitly run `lake build`, Mathematica `--test-mode`, and `python -m unittest discover` (and it still runs the existing per-language scripts).
- Phase 2 Lean skeleton progress (compile-safe, still abstract)
  - lean/src/AqeiBridge/Spacetime.lean: added abstract `CausalCurve`, `Jplus`, and a neighborhood hook type.
  - lean/src/AqeiBridge/StressEnergy.lean: made `StressEnergyTensor` a symmetric matrix; added `LinearizedEinstein` placeholder.
  - lean/src/AqeiBridge/AQEI_Cone.lean: added `mkFunctionals` helper for sampling-based constraint lists.
  - lean/src/AqeiBridge/CausalStability.lean: added an `IsPathConnected` skeleton statement for the admissible region.
  - lean/src/AqeiBridge/DiscreteCausality.lean: renamed discrete future-set to `JplusDiscrete` to avoid clashing with spacetime `Jplus`.
- Manuscript draft
  - Created docs/manuscript.md with an outline patterned after the “papers/” style in `energy-tensor-cone`.

**TODO workflow**
- Drained the active queue: docs/TODO.md is empty and `wc -l docs/TODO.md` returns `0`.
- Moved outcomes into:
  - docs/TODO-completed.md
  - docs/TODO-backlog.md (for the deeper homotopy/continuity/Lorentzian-manifold pieces that aren’t realistic to finish in this iteration without overclaiming)

**Commits**
- `32664a0` — tests: add Mathematica `--test-mode` + explicit smoke checks
- `7c7119b` — lean+docs: tighten Phase-2 skeletons + start manuscript
- `c074df4` — docs: drain active TODO queue (keeps TODO.md empty)
<!-- ------ -->
---
**Done**
- Fixed the hanging pipeline test by making Mathematica runs honor `AQEI_TEST_MODE=1` in orchestrator.py, and enabling it in the end-to-end smoke test test_pipeline.py.
- Added the causal preorder/Alexandrov topology substrate in CausalPoset.lean and wired it into AqeiBridge.lean.
- Added MIT licensing via LICENSE and updated README/docs, plus moved the finished queue into TODO-completed.md.

**Validation**
- run_tests.sh now completes successfully (Lean + Mathematica test-mode + Python tests).
- `wc -l docs/TODO.md` is `0`.
<!-- ------ -->
---
Completed: *Commit changes* (5/5)

- Pulled the next backlog chunk into TODO.md (Spacetime → causal preorder → Alexandrov topology), implemented it, and drained TODO.md back to 0 lines.
- Added SpacetimeCausalPoset.lean: `Spacetime.CausalAxioms`, `toCausalPoset`, `alexandrovTopology`, and `isOpen_Jplus_order`.
- Wired it into AqeiBridge.lean and extended the note in manuscript.md.
- Fixed the recurring slow/hanging test behavior by forcing Mathematica tests to use `--test-mode` in mathematica_tests.sh.
- Verified `wc -l docs/TODO.md` is `0`, and committed the changes (`4b53a0a`).
<!-- ------ -->
---
- Implemented the Phase 2 TODO items and cleaned up the TODO workflow again.
- Lean updates:
  - StressEnergy.lean: added `StressEnergyTensor.toPerturbation` (still a deliberate placeholder via `LinearizedEinstein`).
  - AQEI_Cone.lean: simplified the convexity proof to avoid simp-lint noise.
  - CausalStability.lean: added typed placeholders for `PerturbedFutures` + `InvariantHomotopyClass`, and a conjecture-shaped interface axiom mentioning them (no homology dependency yet).
- Docs/README updates:
  - manuscript.md: added explicit $J^+(p)$ formula + a short “pivot” note.
  - README.md: added a brief “Recent progress” section.
  - TODO-BLOCKED.md: removed the stale “license blocked” item and clarified the real blockers.
  - TODO-completed.md: logged the completed items.
- Validation: run_tests.sh passes.
- Workflow done-criterion: `wc -l docs/TODO.md` is `0`.
- Committed as `76d1a49` with a bullet-list message.
<!-- ------ -->
---
- Pulled 5–8 Phase 3 items from the backlog into docs/TODO.md, implemented them, moved the record into docs/TODO-completed.md, and drained TODO.md back to 0 lines.
- Implemented:
  - analyze_candidates.py: emits `maxScore` and `maxScoreRay` into the generated Lean artifact for traceability.
  - sweep_parameters.py: new sweep helper with `--dry-run` (writes sweep plan JSON) and defaults to `AQEI_TEST_MODE=1` when executing.
  - visualize_results.wl: new script that reads `mathematica/results/*.json` and exports a PNG bar chart of candidate scores.
  - search.wl: added optional `--geodesic` observable mode (default off; still linearized per-basis weights so the LP structure remains intact).
  - python_tests.sh: added a dry-run smoke test for the sweep planner.
  - mathematica_tests.sh: runs `visualize_results.wl` (test-mode) and asserts `plot_scores_test.png` exists.
- Validation: run_tests.sh passes.
- Workflow condition: `wc -l docs/TODO.md` is `0`.
- Committed as `a6c2f89` with a bullet-list summary.
<!-- ------ -->
---
**Implemented**
- Sweep execution now writes an index at runs/sweeps/<ts>/index.json pointing at each run’s runs/<run_ts>/run.json via python/sweep_parameters.py.
- Added multi-ray overlap/connectedness proxy (Jaccard over unioned activeConstraints + components) in python/multi_ray_analysis.py.
- Added sweep aggregation that reads the sweep index + run records and computes per-point maxScore/maxScoreRay from candidates JSON in python/sweep_analysis.py.
- Orchestrator archives per-run artifacts under runs/<ts>/artifacts/ and records archived paths in run.json (already done) in python/orchestrator.py.

**Tests**
- Extended bash smoke tests to cover both new analysis scripts in tests/python_tests.sh.
- Ran run_tests.sh successfully (Lean/Mathematica/Python all OK).

**TODO workflow**
- Drained docs/TODO.md to 0 lines (`wc -l` == 0).
- Logged the batch in docs/TODO-completed.md.
<!-- ------ -->
---
I’m going to pull one more backlog item (“ContourPlot visualizations”) into TODO.md, implement it (new Mathematica contour plot export + test coverage), rerun run_tests.sh, then drain TODO.md back to empty so this iteration truly covers 5+ backlog items.
<!-- ------ -->
---
**What shipped**
- Added `--geodesic-ndsolve` (NDSolve ODE proxy) in mathematica/search.wl.
- Exercised `--geodesic-ndsolve` in tests/mathematica_tests.sh.
- Added multi-threshold “0th persistence” style output via `--thresholds` in python/multi_ray_analysis.py.
- Emitted a conservative rational upper bound `maxScoreUpperRat : Rat` into the generated Lean artifact via python/analyze_candidates.py.
- Added meshgrid support `--grids` (comma-separated) in python/sweep_parameters.py.
- Extended smoke tests in tests/python_tests.sh and ran run_tests.sh (passes).

**TODO status**
- docs/TODO.md is empty (`wc -l` == 0).
- Batch logged in docs/TODO-completed.md.
<!-- ------ -->
---
I already moved a 6-item batch out of the backlog into docs/TODO.md, implemented it, ran run_tests.sh (passes), and drained TODO.md back to empty (`wc -l` == 0).

To make that visible in the backlog itself, I checked off the completed Phase 3 items in docs/TODO-backlog.md:
- Geodesic tracing (now includes `--geodesic-ndsolve`)
- Multi-ray connectedness proxy (plus `--thresholds` sweep)
- Lean bound emission from analyze_candidates.py (`maxScoreUpperRat`)
- Parameter sweep meshgrid support + sweep indexing

Remaining unchecked backlog items include 2+1D cylindrical toy and ContourPlot visualizations. If you want, I can pull the next 5–8 items by breaking “2+1D toys” into a small, testable scaffold batch plus the visualization work.
<!-- ------ -->
---
**Done**
- Drained TODO.md to a true 0 lines and committed two batches (connectedness proxy; then backlog batch). Repo is clean (`git status` empty) and `wc -l docs/TODO.md` is 0.

**Backlog batch implemented**
- search.wl now honors `AQEI_RESULTS_DIR` so each run can write JSON outputs to an isolated directory.
- analyze_candidates.py now supports `--results-dir` and `--out` (defaults unchanged).
- orchestrator.py now plumbs configurable results/output paths and supports `skip_lean` (sweep-friendly).
- sweep_parameters.py adds `--skip-lean` and `--jobs` (it rejects `--jobs>1` unless `--skip-lean` is set, because Lean + generated files aren’t parallel-safe otherwise).
- multi_ray_analysis.py adds `--dot-out` to emit a Graphviz DOT overlap graph at the chosen Jaccard `--threshold`.
- conjecture.md now has a short “toward proof” section that explains how the discrete/toy proof plan (chambers/local constancy/adjacency) relates to the heuristic diagnostics.
- python_tests.sh smoke-tests the new analyze-candidates CLI and DOT output; run_tests.sh passes.
<!-- ------ -->
---
Implemented the next backlog slice and kept TODO/commit hygiene intact.

**What changed**
- Added a new Lean “toward proof” module: Chambers.lean
  - Defines a closed-chamber model (`ClosedChamber`) for a finite family of linear AQEI-like constraints.
  - Proves `Convex → IsPathConnected` for these chambers.
  - Proves the toy `AQEI_cone` is path-connected assuming feasibility via nonnegative bounds (`0 ≤ B`, so `T=0` is admissible).
- Wired the new module into AqeiBridge.lean.
- Updated conjecture.md “Toward proof” with a pointer to the Lean lemma.

**Validation**
- Ran run_tests.sh successfully (Lean/Mathematica/Python OK).
- Drained TODO.md back to empty (`wc -l` is 0).

to keep pushing toward the conjecture, next good step is to connect this chamber lemma to the *discrete causality* side: formalize a parameter-to-DiscreteSpacetime map that is locally constant on chambers, then conclude a path-connectedness statement about the induced futures in the discrete toy model.
<!-- ------ -->
---
Implemented the “next good step” as a formal Lean bridge from chambers → discrete futures, and kept TODO hygiene + commits.

**What changed**
- Added DiscreteChamberStability.lean
  - Defines `ConstantOn` and `DiscreteFuture (J, p) := JplusDiscrete (J T) p`.

<!-- ------ -->
---
**Poset homology proxy + discrete sweeps (compile-safe)**

**Lean**
- Added a Mathlib-native `ChainComplex (ModuleCat R) ℕ` proxy for a causal poset’s low-degree homology:
  - lean/src/AqeiBridge/PosetHomologyProxy.lean
  - Uses `C₀` = formal combinations of points, `C₁` = formal combinations of strict edges, with `∂₁(p<q) = q - p`.
  - Exposes `H1 := (posetChainComplex ...).homology 1`.
- Added a generated-artifact module placeholder and wired it into the top-level import:
  - lean/src/AqeiBridge/GeneratedPosetConjectures.lean (generated/overwritten)

**Python**
- Added python/poset_homology_proxy.py:
  - Computes the Z₁ proxy dimension `|E| - |V| + c` (weak components) from graph JSON.
  - Supports a small Minkowski-ish sweep and emits a Lean data/conjecture stub file.

**Tests / CI hygiene**
- Updated tests/python_tests.sh to smoke-test the Z₁ proxy on a diamond DAG and verify Lean emission.
- Updated tests/lean_tests.sh to create a placeholder for GeneratedPosetConjectures.lean when absent.
- Added GeneratedPosetConjectures.lean to .gitignore.

**Validation**
- Full run_tests.sh returns green (warnings only).
  - Proves: if `J` is constant on a closed chamber, then the image of `DiscreteFuture` on that chamber is a singleton (so futures don’t “jump” within a chamber).
- Wired it into AqeiBridge.lean.
- Added a one-line note to conjecture.md pointing to this discrete-toy implication.

**Validation + workflow**
- Ran run_tests.sh successfully (Lean/Mathematica/Python OK).
- Moved the completed items into TODO-completed.md, drained TODO.md back to truly empty (`wc -l` is 0), and committed (`d8e3a3e`).

to push one step further, the natural follow-on is to *define an explicit chamber-indexed discrete model* `J : StressEnergy n → DiscreteSpacetime Pt` that provably factors through the chamber index (so the “constant on chambers” hypothesis becomes a theorem rather than an assumption).
<!-- ------ -->
---
Implemented the chamber-indexed discrete model `J` and made “constant on chambers” a theorem by construction.

- Added ChamberIndexedModel.lean
  - Defines `chamberIndex` and `Chamber`.
  - Defines `chamberIndexedJ : StressEnergy n → DiscreteSpacetime Pt` via `J T := model (chamberIndex F T)`.
  - Proves `chamberIndexedJ_constantOn_chamber` and the discrete-future singleton corollary `discreteFuture_image_singleton_of_chamberIndexedJ`.
- Wired the module into AqeiBridge.lean.
- Updated conjecture.md to reference the new construction.
- Ran run_tests.sh (passes), drained TODO.md to truly empty, logged completion in TODO-completed.md, and committed (`34966f6`).

next step: connect this `chamberIndex` notion to the earlier `ClosedChamber` active-set definition (so we can explicitly relate “active constraints” diagnostics to these sign-pattern chambers)
<!-- ------ -->
---
I’m going to add a small Lean bridge module proving how `ClosedChamber F active` relates to the sign-pattern `chamberIndex` (including the clean equality result under strictness for inactive constraints), then run run_tests.sh, drain TODO.md, and commit.
<!-- ------ -->
---
Bridge lemmas are implemented and wired into Lean + docs; next I’ll run run_tests.sh to confirm everything compiles, then drain TODO.md and commit this batch.
<!-- ------ -->
---
Completed: *Run tests, drain TODO, commit* (4/4)

Implemented the `ClosedChamber` ↔ `chamberIndex` connection end-to-end, with tests + TODO hygiene + commit.

- Added ChamberClosedChamberBridge.lean
  - `active_subset_chamberIndex_of_mem_closedChamber`: `T ∈ ClosedChamber F active → active ⊆ chamberIndex F T`
  - `chamberIndex_eq_active_of_mem_closedChamber_of_inactive_strict`: if all inactive constraints are strict, then `chamberIndex F T = active`
  - `mem_Chamber_of_mem_closedChamber_of_inactive_strict`: packages the equality as membership in `Chamber F active`
- Wired import in AqeiBridge.lean.
- Noted the relationship in conjecture.md.
- Ran run_tests.sh (passes), drained TODO.md back to empty, logged the batch in TODO-completed.md, and committed (`73aba03`).
<!-- ------ -->
---
I’ve reshaped the active queue into a small 6-item batch and moved the over-scoped Phase 4 items into TODO-BLOCKED.md with concrete blockers. Next I’ll implement the Phase 4 searches doc + the `--analyze` sweep flag + the small README/manuscript updates, then run run_tests.sh, drain TODO.md, and commit.
<!-- ------ -->
---
- Verified the Phase 4 ramp-up work is already implemented: aqei-bridge/docs/phase4_searches.md, `--analyze` in aqei-bridge/python/sweep_parameters.py, and the doc cross-links in aqei-bridge/README.md + aqei-bridge/docs/manuscript.md.
- Drained the active queue: aqei-bridge/docs/TODO.md is now truly empty (`wc -l` = 0), and logged the batch in aqei-bridge/docs/TODO-completed.md.
- Ran run_tests.sh in `aqei-bridge`: all tests passed (Lean warnings only; Mathematica emitted non-fatal EGL/MESA warnings as before).
- Committed the batch: `ae50c80` “Phase 4 ramp-up: sweep docs + auto analysis” (includes docs, `--analyze`, test smoke update, README/manuscript links, TODO hygiene).
<!-- ------ -->
---
**Done**
- Promoted a concrete batch from backlog into TODO, implemented it, ran run_tests.sh (passes), drained TODO back to 0 lines, and committed.

**What changed**
- Added a dependency-free directed-graph helper: aqei-bridge/python/causal_graph_tools.py
  - `ctc`: detects directed cycles (CTC proxy)
  - `dot`: exports Graphviz DOT
  - JSON input: `{"edges": [[src, dst], ...]}` (also accepts `{"src":..,"dst":..}` entries)
- Documented usage in aqei-bridge/docs/phase4_searches.md.
- Extended smoke tests in aqei-bridge/tests/python_tests.sh.
- Updated aqei-bridge/docs/TODO-backlog.md to mark basic multiprocessing as done (`--jobs` for sweeps with `--skip-lean`).
- Logged completion in aqei-bridge/docs/TODO-completed.md and drained aqei-bridge/docs/TODO.md.

**Commit**
- `331f1d4` — “Add causal-graph diagnostics helpers”
<!-- ------ -->
---
- Pulled the next backlog slice into TODO, implemented it, ran run_tests.sh (passes), drained TODO back to 0 lines, and committed.
- Added futures-map support to the CTC proxy: python/causal_graph_tools.py now accepts `{"futures": {...}}` as well as `{"edges": ...}`.
- Added a CI-friendly poset visualization generator: python/minkowski_poset.py writes `edges` JSON and optional DOT.
- Documented both in docs/phase4_searches.md and added smoke tests in tests/python_tests.sh.
- Logged completion in docs/TODO-completed.md and updated the note in docs/TODO-backlog.md.
<!-- ------ -->
---
**Closed CTC-proxy batch**
- Logged completion in TODO-completed.md and drained TODO.md back to `wc -l == 0`.
- Committed remaining docs/tests updates (the wrapper import fix was already committed earlier).

**Next TODO batch completed (poset/interval viz helper)**
- Added Alexandrov-style interval tool poset_interval_tools.py (`I(p,q) := { r | p ->* r and r ->* q }`) with optional induced-subgraph DOT export.
- Documented usage in phase4_searches.md.
- Added smoke coverage in python_tests.sh.
- Ran run_tests.sh (All tests: OK), drained TODO.md, and committed.
<!-- ------ -->
---
Lean-side “proof substrate” is the higher-likelihood direction here: it directly grows the formal framework we’d actually need for a proof, whereas bigger/distributed sweeps mainly produce more empirical evidence.

What I did next (and closed the TODO loop):
- Added a Lean module for order-theoretic past sets + intervals: CausalIntervals.lean
  - `Jminus`, `IsLowerSet`, proved lower sets are closed in the Alexandrov topology (opens are upper sets)
  - defined `Icc(p,q) := {r | p ≤ r ∧ r ≤ q}` plus basic lemmas
- Wired it into the top-level import: AqeiBridge.lean
- Ran run_tests.sh (All tests: OK)
- Logged completion in TODO-completed.md, drained TODO.md back to `wc -l == 0`, and committed (`e2215b8`)
<!-- ------ -->
---
I pushed the Lean side toward an actual *obstruction-style* proof step: a discrete “chronology / CTC proxy” that becomes a crisp antisymmetry failure, plus a functorial directed-cycle proxy that composes with graph homomorphisms.

**What I Added (proof-relevant lemmas)**
- New module: lean/src/AqeiBridge/DiscreteChronology.lean
  - `HasNontrivialCycle` (distinct points mutually reachable under reflexive-transitive closure)
  - `IsAntisymmReachableRefl` and lemma `HasNontrivialCycle ↔ ¬ IsAntisymmReachableRefl`
  - `HasDirectedCycle := ∃ p, Relation.TransGen M.edge p p` (nonempty cycle)
  - `NoSelfEdges := ∀ p, ¬ edge p p`
  - `EdgeHom` preserves `HasDirectedCycle`
  - `NoSelfEdges ∧ HasDirectedCycle → HasNontrivialCycle` (toy “CTCs imply failure of chronology”)

**Wiring + Tests**
- Wired the new module into lean/src/AqeiBridge.lean
- Ran run_tests.sh: `All tests: OK` (still just warnings)

**TODO Discipline**
- Logged both completed Lean mini-batches in docs/TODO-completed.md
- Confirmed docs/TODO.md is truly empty (`wc -l == 0`)

**Repo State**
- Uncommitted changes are currently:
  - docs/TODO-completed.md
  - lean/src/AqeiBridge.lean
  - lean/src/AqeiBridge/CausalIntervals.lean
  - plus new/untracked: `CausalContinuity`, `DiscreteCausalPoset`, `DiscreteChronology`
<!-- ------ -->
---
**Chronological Review**
- Work progressed in small “drain TODO” batches: implement → run run_tests.sh → move items to completed log → ensure active TODO is empty.
- Phase 4 ramp-up (docs + sweep tooling) landed first, then dependency-free Python diagnostics for cycles/posets/intervals, then a Lean “proof-substrate” push: Alexandrov/interval facts + discrete chronology (cycle ↔ antisymmetry failure).
- The most recent proof-oriented step in history is the discrete chronology/CTC proxy formalization and its functorial directed-cycle variant.

**Intent Mapping**
- User goal: “work towards proving our conjecture,” interpreted as prioritizing Lean substrate + obstruction-style invariants (not just larger empirical sweeps).
- The repo workflow constraint stayed central: keep the active queue empty at rest and keep the history/TODO logs auditable.

**Technical Inventory (what actually exists now)**
- Lean: discrete chronology + cycle proxies, interval/order substrate, and continuity/topology bridges (logged in aqei-bridge/docs/TODO-completed.md).
- Python: causal graph cycle detection (CTC proxy), Minkowski-style poset generator, reachability-interval extraction, DOT exporters (described in aqei-bridge/docs/history/history.md).
- Docs/process: active queue file aqei-bridge/docs/TODO.md + completed log aqei-bridge/docs/TODO-completed.md + narrative history aqei-bridge/docs/history/history.md.

**Most Recent Agent Commands & Tool Results (trigger context)**
- `git status --porcelain` in `aqei-bridge` returned empty output (working tree clean).
- `wc -l` on aqei-bridge/docs/TODO.md returned `0` (TODO is truly empty).
- `tail` on aqei-bridge/docs/history/history.md shows the latest recorded batches: Phase 4 ramp-up + Python CTC/poset tooling + Lean interval substrate + Lean discrete chronology.
- `git log -n 8 --oneline` shows the tip includes the Lean discrete chronology work at `HEAD` (commit `0d4ccf7`).
- Verified that the commit hashes referenced inside the history narrative (e.g., `ae50c80`, `331f1d4`, `34966f6`) do exist in this repo (via `git cat-file -t`).

**Current State**
- Active queue is empty: aqei-bridge/docs/TODO.md.
- Recent “done” items and the exact claims about what was implemented/tested are captured in aqei-bridge/docs/TODO-completed.md and summarized narratively in aqei-bridge/docs/history/history.md.
<!-- ------ -->
---
Implemented a compiling Lean “homology proxy” and got the full run_tests.sh suite back to green.

- New module: aqei-bridge/lean/src/AqeiBridge/DiscreteHomologyProxy.lean
  - Defines an `Edge` as data `(src,dst)` + proof, avoiding the `Prop`-as-`Type` blocker.
  - Defines chain groups `C₀ := Pt →₀ R`, `C₁ := Edge M →₀ R`, boundary `boundary1 : C₁ →ₗ[R] C₀`, and cycle space `Z1 := LinearMap.ker boundary1`.
  - Adds functorial pushforwards `push0`, `push1` under `EdgeHom` plus naturality (`boundary1_natural`) and “cycles map to cycles” (`push1_mem_Z1`).

- Wired into the project imports: aqei-bridge/lean/src/AqeiBridge.lean

- Verification: run_tests.sh now reports “Lean tests: OK / All tests: OK” (only existing linter warnings remain).
<!-- ------ -->
---
**Status**
- Poset chain-complex proxy is compiling again, with `H1 := (posetChainComplex ...).homology 1` working via Mathlib’s homology API in aqei-bridge/lean/src/AqeiBridge/PosetHomologyProxy.lean.
- run_tests.sh is green (warnings only).

**Next Steps to Stay on Track**
- **(1) Unblock Homology/Sheaf (Lean / Mathlib chain complexes)**: Extend the low-degree `C₀/C₁` complex toward an actual poset/order-complex chain complex (or a controlled truncation), and add basic lemmas relating your earlier `Z1 := ker ∂₁` proxy to Mathlib notions (`cycles`, `homology`).
- **(2) Large-Scale Discrete Searches (sweeps → Lean conjectures)**: Run deterministic sweeps over generated causal posets/graphs, compute proxy invariants (cycle counts, ranks, obstruction flags), and emit Lean conjecture stubs automatically (same style as your existing “GeneratedCandidates” pipeline).
- **(3) Generalize proofs to “continuous limits” (Mathlib topology)**: Connect invariants to Alexandrov/topological structure, then prove invariance under the morphisms you care about (order-embeddings/isomorphisms, suitable continuity notions already present in your causal-poset files).
- **(4) Manuscript expansion**: Write the invariant definitions + experimental sweep results as a “discrete evidence” section, then a “formal proxy” section that cleanly states what is proved in Lean today vs. what’s conjectural.
- **(5) Integrate global fragments (Lean global conjecture)**: Replace the placeholder “Homology” in the global conjecture layer with the concrete `H1` (or a functorial wrapper around it), and restate the chronology/obstruction invariance axiom in terms of that object.
<!-- ------ -->
---
**What I did (next steps implementation)**
- Added a discrete sweep + Lean emission helper: aqei-bridge/python/poset_homology_proxy.py
  - `z1`: computes the poset/graph $Z_1$ proxy dimension `|E| - |V| + c` (weak components) from graph JSON.
  - `sweep-minkowski`: generates small Minkowski-ish posets and summarizes the proxy; can also overwrite a generated Lean module.
- Added a new generated Lean artifact (with a safe placeholder): aqei-bridge/lean/src/AqeiBridge/GeneratedPosetConjectures.lean
- Wired it into the build by importing it from aqei-bridge/lean/src/AqeiBridge.lean
- Updated CI/test harness:
  - aqei-bridge/tests/python_tests.sh now smoke-tests the diamond DAG has `z1Dim = 1` and checks Lean emission.
  - aqei-bridge/tests/lean_tests.sh now creates a placeholder if the generated file isn’t present.
  - aqei-bridge/.gitignore ignores the generated file.
- Logged the batch in aqei-bridge/docs/history/history.md

**Validation**
- `bash tests/python_tests.sh`: OK
- run_tests.sh: OK (warnings only)

**How to use**
- Compute on a graph JSON: `python poset_homology_proxy.py z1 path/to/graph.json --json`
- Run a small sweep and overwrite the Lean stub:
  - `python poset_homology_proxy.py sweep-minkowski --tmaxs 1,2 --xmaxs 1 --out-dir runs/tmp/poset --lean-out lean/src/AqeiBridge/GeneratedPosetConjectures.lean`
<!-- ------ -->
---
**Done**
- Added a Lean bridge showing the kernel-based `Z1 := LinearMap.ker boundary1` matches Mathlib’s chain-complex `cycles` in degree 1 via a canonical isomorphism `cycles1IsoZ1`.
- Implemented the bridge in aqei-bridge/lean/src/AqeiBridge/PosetHomologyProxy.lean using:
  - `HomologicalComplex.cyclesIsoSc'` to avoid non-definitional `ComplexShape.down` `next/prev`
  - `ShortComplex.cyclesIsoKernel` + `ModuleCat.kernelIsoKer` to land in `LinearMap.ker boundary1` (i.e. `Z1`)
- Added simp lemmas for `d 1 0` (`posetChainComplex_d_1_0` and `_hom`) to make the rewrite to `boundary1` stable.

**Validation**
- Ran `cd /home/echo_/Code/asciimath/aqei-bridge && ./run_tests.sh` — all stages completed successfully (warnings only, no errors).
<!-- ------ -->
---

**Poset homology proxy: `H₁ ≅ Z₁` (low-degree truncation)**

**Lean**
- Strengthened the earlier bridge `cycles 1 ≅ Z1` into a full homology-level statement:
  - In the low-degree proxy chain complex (where `d₂ = 0` by construction), proved `H₁ ≅ Z₁`.
  - Implemented as `H1IsoZ1` in `aqei-bridge/lean/src/AqeiBridge/PosetHomologyProxy.lean`.
- Added a simp lemma fixing the “incoming differential is zero” fact in a stable way:
  - `posetChainComplex_d_2_1 : d 2 1 = 0`.

**Key idea**
- Use Mathlib’s characterization of homology as a cokernel:
  - `homologyIsCokernel` gives `H₁` as the cokernel of `toCycles 2 1 : C₂ ⟶ cycles 1`.
  - Since `d 2 1 = 0`, we show `toCycles 2 1 = 0`, hence `cokernel (0) ≅ cycles 1` via `cokernelZeroIsoTarget`.
  - Compose `H₁ ≅ cycles 1` with the existing `cycles1IsoZ1`.

**Validation**
- Ran `cd /home/echo_/Code/asciimath/aqei-bridge && ./run_tests.sh` — green (warnings only).

**Note on scope**
- This is a strengthening of the *poset homology proxy* (a clean formal fact about the truncated `C₀/C₁` chain complex). It is **not** the main AQEI/causal-stability conjecture.
<!-- ------ -->
---
Implemented the next “invariance layer” on top of the poset homology proxy.

- Added an induced pushforward `pushZ1 : Z1(P) →ₗ[R] Z1(Q)` for any strict-edge-preserving map, using `push1_mem_Z1` (aqei-bridge/lean/src/AqeiBridge/PosetHomologyProxy.lean).
- Defined `EdgeIso` (a point equivalence preserving `<` both ways) and proved `Z₁` invariance as a `LinearEquiv` `pushZ1Equiv` plus a `ModuleCat`-level isomorphism `Z1ModuleIso` ([PosetHomologyProxy invariance core](aqei-bridge/lean/src/AqeiBridge/PosetHomologyProxy.lean#L186-L268)).
- Derived `H₁` invariance `H1IsoOfEdgeIso` by transporting along the existing bridge `H1IsoZ1` ([H1 invariance](aqei-bridge/lean/src/AqeiBridge/PosetHomologyProxy.lean#L434-L449)).

run_tests.sh in `aqei-bridge/` is green (warnings only). This still doesn’t prove the global conjecture—this is infrastructure to let the proxy behave like an actual invariant under (edge-)isomorphisms.
<!-- ------ -->
---