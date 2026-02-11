# TODO: Active Queue for AQEIBridge Workflow

Focus on completing Phase 2 formalizations (build on recent discrete causality toy from commit d6bb377). Then advance Phase 3. Limit to 5-10 items; move completed to docs/TODO-completed.md (create if needed). Recent progress (from commits 0072fe7, d6bb377, etc.): End-to-end pipeline runnable, discrete Lean toy added, history.md updated—reflect this by checking off related backlog items.

## Phase 2: Formalize Core Concepts in Lean (High Priority, Next 1-2 days)
- [x] Formalize basic GR/spacetime structures in `Spacetime.lean`: Done via discrete causality toy (causal curves, J⁺); extend to continuous with Mathlib.Analysis.NormedSpace.
- [ ] Complete `StressEnergy.lean`: Define symmetric tensors, linearized map. Sample:
  ```lean
  structure StressEnergyTensor where
    components : SymMatrix ℝ 4
    def toPerturbation (T : StressEnergyTensor) : MetricPerturbation := linearizedEinstein T
  ```
- [ ] Expand `AQEI_Cone.lean`: Add sampling constructor; prove convexity. Use recent history.md insights from Copilot.
- [ ] Refine `CausalStability.lean`: Update conjecture with homotopy (Mathlib.Homology). Incorporate discrete toy results. Sample:
  ```lean
  conjecture CausalStability {M : Type*} [DiscreteCausalPoset M] (ε : ℝ) :
    ∀ T : StressEnergyTensor, AQEIAdmissible T ∧ ‖T‖ < ε →
      PathConnected (PerturbedFutures M T) ∧ InvariantHomotopyClass M T
  ```
- [ ] Add lemmas: Perturbations preserve causality continuity; use uniform topology.

## Immediate Cross-Phase Tasks
- [x] Add local test scripts: Done via run_tests.sh and tests/ (commit 3cbc3d2).
- [ ] Start manuscript draft in `docs/manuscript.md`: Outline (Intro, Conjecture, Pipeline, Lean proofs, Bridge to topology). Add LaTeX:
  \[ J^+(p) = \{ q \mid \exists \gamma: p \to q, \, g(\dot{\gamma}, \dot{\gamma}) \leq 0 \} \]
  Discuss pivot potential if no counterexamples in expanded searches.
- [ ] Update README with latest commits: Link to history.md updates, emphasize end-to-end run.
```

## General / Ongoing
- [ ] Incorporate history.md: non-linear opts for search.wl (unblocked: Use NMaximize with proxies).
- [ ] Replace synthetic AQEI (unblocked): Use Fewster-style worldline averages as proxy; sample functional ∫ T φ ds ≥ 0 with φ bump functions.