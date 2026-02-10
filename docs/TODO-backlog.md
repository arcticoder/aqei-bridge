# TODO — backlog

This is the long-term checklist migrated out of `docs/TODO.md` so that `docs/TODO.md` can stay empty (per workflow rule: it should represent the active queue only).

Phase 1 items were completed in earlier commits; see `docs/TODO-completed.md`.

## Phase 2: Formalize Core Concepts in Lean (High Priority)
- [ ] Formalize basic GR/spacetime structures in `Spacetime.lean` (Lorentzian manifolds, causal curves, future sets J⁺(p), small neighborhoods). Include math: e.g., a curve γ is causal if $g(\dot{\gamma}, \dot{\gamma}) \le 0$.
- [ ] Complete `StressEnergy.lean`: Define finite-dim stress-energy tensors, mappings to metric perturbations (linearized Einstein).
- [ ] Complete / expand `AQEI_Cone.lean`: Formalize AQEI-admissible set as intersection of half-spaces from linear functionals (sampling-based cone), prove convexity / cone properties. Use Mathlib for convex sets.
- [ ] In `CausalStability.lean` (or `Conjecture.lean`): State the conjecture formally (e.g., as ∀ small admissible T, the family of perturbed causal futures is path-connected with fixed homotopy class).
- [ ] Add basic lemmas: small perturbations preserve local causality, continuity of J⁺ under metric perturbations (use Mathlib topology / continuity).
- [ ] Create `GeneratedCandidates.lean` stubs for Python-emitted results (e.g., conjectured inequalities from numerical max Δ).

## Phase 3: Improve Heuristics & Bridge (Medium-High Priority)
- [ ] Replace synthetic/ad-hoc AQEI inequalities in `search.wl` with more faithful proxies (derive from actual AQEI sampling functionals in the manuscript; add non-linear constraints if needed via other optimizers).
- [ ] Improve causal observable in Mathematica: beyond $\int h\, d\lambda$ along rays — add ray tracing for actual null geodesics in perturbed metric; check focusing/defocusing or horizon formation proxies.
- [ ] Add multi-ray / multi-point analysis: check path-connectedness proxy (e.g., whether families of J⁺ overlap continuously).
- [ ] Explore higher-dimensional toy models (start with 2+1D cylindrical or toroidal grid).
- [ ] Enhance `analyze_candidates.py`: translate high-score candidates into Lean-usable statements (e.g., conjectured bounds on Δ, potential counterexample shapes).
- [ ] Add Python support for parameter sweeps and Pareto analysis.

## Phase 4: Toward Proof / Disproof (Medium-Long Term)
- [ ] Run large-scale searches: look for candidates that produce large Δ or qualitative causal changes despite constraints.
- [ ] If candidates show bounded Δ: formalize bound in Lean as lemma, with proof sketch.
- [ ] Transition toy → realistic: perturb Minkowski, then simple curved backgrounds.
- [ ] Incorporate a linearized Einstein solver (or post-Newtonian) in the Mathematica/Python loop.
- [ ] Attempt Lean proofs of special cases (vacuum perturbations, weak-field limits, 1+1D toy fully formalized).
- [ ] If counterexample-like behavior appears: refine conjecture (local vs global, neighborhood size).

## General / Ongoing
- [ ] Add local test scripts: `run_tests.sh` to execute `test_pipeline.py`, `lake build`, and `wolframscript -file search.wl`.
- [ ] Integrate / depend on Mathlib more deeply (topology, analysis, differential geometry).
- [ ] Review / incorporate ideas from history (see `docs/history/`).
- [ ] License the repo (e.g., MIT).
- [ ] Add visualization outputs from Mathematica (plots of h, rays, constraints).
