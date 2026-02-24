# TODO: Backlog (Long-Term Mathematical Targets)

Promote items to `docs/TODO.md` in small batches when unblocked.
All items must strengthen one of three formal pillars:
1. Convex polyhedral geometry — AQEI cone structure.
2. Functorial homology — Z₁ = ker ∂₁, pushforward injectivity.
3. Metric stability of futures — discrete Hausdorff bounds.

## Phase 4: Structural Generalization

- [ ] Prove chamber-constancy → global constancy theorem for invariants on AQEI_cone(F):

  If Φ : AQEI_cone(F) → α is locally constant on polyhedral chambers,
  and the cone is nonempty (hence path-connected by `admissible_region_pathConnected`),
  then Φ is globally constant on the cone.

  Mathematically:
  $$\text{Convex}(C) \land C \neq \emptyset \land \Phi|_{\text{chamber}} = \text{const} \;\Rightarrow\; \Phi \text{ constant on } C.$$

  Lean sketch:
  ```lean
  theorem chamber_constancy_global
    (C : Set V) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (Φ : V → α)
    (hloc : ∀ chamber, IsChamber chamber → ∀ T₁ T₂ ∈ chamber, Φ T₁ = Φ T₂)
    : ∀ T₁ T₂ ∈ C, Φ T₁ = Φ T₂
  ```

- [ ] Define finite Čech H¹ for Alexandrov opens of a finite poset and prove
  vanishing for acyclic posets:

  $$\text{acyclic}(P) \;\Rightarrow\; H^1_{\check{C}}(P) = 0.$$

  Build on `Cech01.lean` where `d1_comp_d0 = 0` and `H1Cech := ker(d1) ⧸ im(d0)`
  are already defined.

  Use coefficient object `F(U) = set of monotone maps U → ℤ` with restriction maps
  given by function restriction (not "sections of futures" — keep it concrete).

- [ ] Extend discrete Lipschitz bound to k-edge perturbations with explicit linear
  dependence on k:

  $$d_H(J^+(P,p),\; J^+(Q,p)) \le k \quad \text{when } |\mathrm{adj}_P - \mathrm{adj}_Q| = k.$$

- [ ] Prove dim H₁(P') ≤ dim H₁(P) under subgraph inclusion (quantitative upgrade):

  $$|E'| - |V| + c(G') \le |E| - |V| + c(G).$$

## Infrastructure (Optional)

- [ ] Deterministic poset visualizer with canonical vertex labeling,
  to ensure isomorphism-invariant output when validating combinatorial invariants.
  (Only useful if needed to generate counterexample candidates for open conjectures.)
