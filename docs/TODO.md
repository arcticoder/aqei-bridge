# TODO: aqei-bridge — Lean 4 Formal Verification Track

> All completed items are recorded in `docs/TODO-completed.md`.
> Blocked items are in `docs/TODO-BLOCKED.md`.
> Long-term backlog is in `docs/TODO-backlog.md`.

---

## Open Items

### Quantitative dim H₁ formula (backlog)
- [ ] Prove the explicit Betti-number formula `dim Z₁(P) = |E(P)| - |V(P)| + c(G(P))`
      in Lean, and use it to give a concrete numerical bound in the paper.
      Blocked on: formalizing connected-component counting for `FiniteCausalPoset`.
      Tracked in `docs/TODO-backlog.md`.

### Paper: update `papers/discrete-causal-posets-lean4.tex`
- [ ] Update §4 to list `jplus_hausdorff_le_card_diff_of_subgraph` (A.4) as a new theorem.
- [ ] Update module list to include `ChamberConstancy.lean`, `GraphDistance.lean`,
      `DiscreteHausdorff.lean`.
- [ ] Rebuild PDF: `cd papers && pdflatex discrete-causal-posets-lean4.tex`.

### V&V / UQ
- [ ] Run full `./run_tests.sh` and confirm zero errors/warnings from Lean build.
- [ ] Confirm `tests/lean_tests.sh` still passes after all module additions.

---

## Summary of Completed Phases

| Phase | Item | Lean file | Status |
|---|---|---|---|
| Paper rewrite | discrete-causal-posets-lean4.tex | — | ✅ |
| A.1 | `jplus_hausdorff_le_one_of_edge_diff` | DiscreteFutureContinuity | ✅ |
| A.2 | `h1_dim_le_of_subgraph` | H1Stability | ✅ |
| A.3 | `jplus_hausdorff_le_chain` | DiscreteFutureContinuity | ✅ |
| A.4 | `jplus_hausdorff_le_card_diff_of_subgraph` | DiscreteFutureContinuity | ✅ |
| B.1 | Counterexample note on IsCompatible | OrderComplexBridge | ✅ |
| B.2 | `h1_oc_stable_of_subgraph` | OrderComplexProxy | ✅ |
| B.3 | `h1_oc_eq_bot_of_acyclic` | OrderComplexProxy | ✅ |
| C.1 | `chamber_constancy_global` | ChamberConstancy | ✅ |
| C.2 | `H1Cech_vanishes_of_exact` | Cech01 | ✅ |
| Bridge | `aqei_bridge_conjecture_discrete` | DiscreteStabilityBridge | ✅ |
| Bridge | `admissible_region_pathConnected` | CausalStability | ✅ |
| UQ infra | `boundedDist_triangle`, `discreteHausdorff_triangle` | GraphDistance, DiscreteHausdorff | ✅ |
