# TODO: aqei-bridge — Lean 4 Formal Verification Track

> All completed items are recorded in `docs/TODO-completed.md`.
> Blocked items are in `docs/TODO-BLOCKED.md`.
> Long-term backlog is in `docs/TODO-backlog.md`.

---

## Open Items

### Rank formula sorry (backlog item 4, partial)
- [ ] Complete `rank_Z1_formula` (sorry in `DiscreteH1QuantitativeUpgrade.lean`):
      prove the Betti-number identity `rank Z₁(M) + |V| = |E_directed| + c(G_undir)`
      using spanning forests + `card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`.
      Depends on: connecting `boundary1` image rank to Laplacian null space over ℝ/ℤ.

### Paper: update `papers/discrete-causal-posets-lean4.tex`
- [ ] Update §4 to include A.5 (`h1_quantitative_upgrade`), `DiscreteConnectedComponents`,
      and the partial result `rank_Z1_formula` (sorry).
- [ ] Rebuild PDF: `cd papers && pdflatex discrete-causal-posets-lean4.tex`.

---

## Summary of Completed Phases

| Phase | Item | Lean file | Status |
|---|---|---|---|
| Paper rewrite | discrete-causal-posets-lean4.tex | — | ✅ |
| A.1 | `jplus_hausdorff_le_one_of_edge_diff` | DiscreteFutureContinuity | ✅ |
| A.2 | `h1_dim_le_of_subgraph` | H1Stability | ✅ |
| A.3 | `jplus_hausdorff_le_chain` | DiscreteFutureContinuity | ✅ |
| A.4 | `jplus_hausdorff_le_card_diff_of_subgraph` | DiscreteFutureContinuity | ✅ |
| A.5 | `h1_quantitative_upgrade` + `numComponents_antitone` | DiscreteH1QuantitativeUpgrade, DiscreteConnectedComponents | ✅ (1 sorry) |
| B.1 | Counterexample note on IsCompatible | OrderComplexBridge | ✅ |
| B.2 | `h1_oc_stable_of_subgraph` | OrderComplexProxy | ✅ |
| B.3 | `h1_oc_eq_bot_of_acyclic` | OrderComplexProxy | ✅ |
| C.1 | `chamber_constancy_global` | ChamberConstancy | ✅ |
| C.2 | `H1Cech_vanishes_of_exact` | Cech01 | ✅ |
| Bridge | `aqei_bridge_conjecture_discrete` | DiscreteStabilityBridge | ✅ |
| Bridge | `admissible_region_pathConnected` | CausalStability | ✅ |
| UQ infra | `boundedDist_triangle`, `discreteHausdorff_triangle` | GraphDistance, DiscreteHausdorff | ✅ |
