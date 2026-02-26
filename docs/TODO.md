# TODO: aqei-bridge — Lean 4 Formal Verification Track

> All completed items are recorded in `docs/TODO-completed.md`.
> Blocked items are in `docs/TODO-BLOCKED.md`.
> Long-term backlog is in `docs/TODO-backlog.md`.

---

## Open Items

### Rank formula — one remaining sorry (spanning forest lower bound)
- [ ] Close `rank_im_boundary1_add_numComponents_ge` (sorry in `DiscreteH1QuantitativeUpgrade.lean`):
      prove `|Pt| ≤ rank(im ∂₁) + c(M)` via a spanning forest argument.
      A spanning forest of `undirGraph M` has `|V| - c(M)` edges; each such edge (oriented
      by choosing the original directed edge) contributes a linearly independent boundary
      vector, proved by leaf-removal induction on each spanning tree component.
      As of this commit, `rank_Z1_formula` and all other lemmas in the file are sorry-free;
      only this one sub-lemma retains a sorry.

### Paper: update `papers/discrete-causal-posets-lean4.tex`
- [ ] Update §4 to include A.5 (`h1_quantitative_upgrade`), `DiscreteConnectedComponents`,
      and `rank_Z1_formula` (all proved; note the one remaining sorry in
      `rank_im_boundary1_add_numComponents_ge`).
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
| A.5 | `h1_quantitative_upgrade` + `rank_Z1_formula` + `numComponents_antitone` | DiscreteH1QuantitativeUpgrade, DiscreteConnectedComponents | ✅ (1 sorry: spanning forest lb) |
| B.1 | Counterexample note on IsCompatible | OrderComplexBridge | ✅ |
| B.2 | `h1_oc_stable_of_subgraph` | OrderComplexProxy | ✅ |
| B.3 | `h1_oc_eq_bot_of_acyclic` | OrderComplexProxy | ✅ |
| C.1 | `chamber_constancy_global` | ChamberConstancy | ✅ |
| C.2 | `H1Cech_vanishes_of_exact` | Cech01 | ✅ |
| Bridge | `aqei_bridge_conjecture_discrete` | DiscreteStabilityBridge | ✅ |
| Bridge | `admissible_region_pathConnected` | CausalStability | ✅ |
| UQ infra | `boundedDist_triangle`, `discreteHausdorff_triangle` | GraphDistance, DiscreteHausdorff | ✅ |
