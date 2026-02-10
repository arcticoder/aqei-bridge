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