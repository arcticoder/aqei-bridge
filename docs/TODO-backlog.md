## Replacement for docs/TODO-backlog.md
```
# TODO: Backlog (Long-Term)

Refined with completions (e.g., a9a7f64 poset viz/generator; 331f1d4 CTC diagnostics; 9ec13aa Phase 4 docs). Promote unblocked to active. If conjecture holds (no CTCs in searches), pivot to manuscript/arXiv. Review post-active.

## Phase 4: Toward Proof / Disproof & Bridge Conjecture (Long Term)
- [ ] Full conjecture proof: Generalize chamber stability to continuous. LaTeX: Path-connected family iff \(\forall T, \epsilon: J^+(p; g + h_T) \sim J^+(p; g)\) in homotopy class.
- [ ] Bridge: Implement full sheaf. Sample Lean:
  ```lean
  def SheafOnPoset (P : CausalPoset) : Sheaf (OpenEmbedding AlexandrovTopology P) where
    presheaf := fun U => SectionsOver U
  conjecture ChronologyProtection (P : CausalPoset) : NoCTC P ↔ SheafCohomology P 1 = 0 := sorry
  ```
- [ ] Cluster support: Beyond multiprocessing (implemented); add job scheduler.

## General / Ongoing
- [ ] Visualizations: Enhance poset graphs with Alexandrov basis. Sample Mathematica:
  ```mathematica
  alexandrovPlot = Graphics[Table[Rectangle[MinMax /@ Transpose[interval]], {interval in alexandrovBasis}]];
  Export["alexandrov.png", alexandrovPlot];
  ```