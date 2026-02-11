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