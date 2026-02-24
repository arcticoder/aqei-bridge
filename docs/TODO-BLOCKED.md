# TODO: Blocked Items

Minimal after latest commits (e.g., diagnostics/posets unblock proxies). Moved unblock paths to active.

- [ ] Full Mathlib sheaf cohomology: Still blocked on infrastructure; use a presheaf proxy + homology alternative.
	- Unblocked scaffold (Lean): `lean/src/AqeiBridge/AlexandrovPresheaf.lean` defines `OpenInAlexandrov` and a minimal `PresheafOnPoset` interface (objects + restriction maps).
	- Unblocked scaffold (Mathlib interface): `lean/src/AqeiBridge/AlexandrovPresheafMathlib.lean` defines a genuine Mathlib presheaf `TopCat.Presheaf CommRingCat` on the Alexandrov topological space: continuous ℝ-valued functions on opens (`realContinuousPresheaf`).
	- Sanity instantiation: `lean/src/AqeiBridge/Examples/DiamondPresheaf.lean` builds this presheaf on a 4-point diamond preorder (`Fin 2 × Fin 2` with product order).
	- Next concretization (Lean — avoid "sections of futures"):
		- Define `F(U) = set of monotone maps U → ℤ` with restriction maps given by function restriction.
		- Implement a Čech 0/1-cochain complex for a *finite* open cover: `C⁰ = ∏_i F(U_i)`, `C¹ = ∏_{i<j} F(U_i ∩ U_j)`, coboundary `d⁰ : C⁰ → C¹` given by restriction difference.
		- Define `H¹ := ker(d¹) / im(d⁰)` as a `Submodule` quotient in `ModuleCat`.
		- Prove `H¹ = 0` for acyclic posets using the existing chain-complex equivalence.

- [x] Poset homology / order complex in Lean (full): **DONE** — both cycle proxies are fully bridged.
	- Unblocked starter: a minimal chain-level 1-cycle proxy is now implemented in Lean for causal posets (`PosetHomologyProxy.lean`) and for directed graphs (`DiscreteHomologyProxy.lean`).
	- Unblocked scaffold (Lean): `lean/src/AqeiBridge/FiniteCausalPoset.lean` defines `FiniteCausalPoset (n : ℕ)` on `Fin n` with decidable relation + a computable `Chains` enumeration.
	- Unblocked infrastructure: functorial pushforwards + invariance under point `OrderIso` (so the proxy behaves like an actual invariant under isomorphism).
	- **DONE: `OrderComplexBridge.lean`** proves the full equivalence:
		- `Z1_oc_eq_bot_of_posethom`: PosetHom acyclicity ⇒ OC acyclicity
		- `Z1_posethom_eq_bot_of_oc`: OC acyclicity ⇒ PosetHom acyclicity (under `IsCompatible`)
		- `Z1_oc_eq_bot_iff`: the bidirectional equivalence for compatible posets
	- (see `TODO-completed.md`, 2026-02-22)

- [ ] Replace synthetic AQEI constraints with worldline sampling bumps in Mathematica: blocked here (Mathematica pipeline moved).
	- Location: implement in `aqei-numerical-validation/mathematica/`.
	- **Linearity requirement:** any new constraint weights must keep the AQEI cone polyhedral (i.e. constraints must remain linear in the stress-energy coefficients). Precompute bump weights as fixed scalars so that `AQEI_cone(F)` stays a finite halfspace intersection.

- [x] **DONE** Future-set topology/continuity (Hausdorff distance on subsets) in Lean:
	- `GraphDistance.lean`: bounded shortest-path proxy `boundedDist` on `Fin n`.
	- `DiscreteHausdorff.lean`: `discreteHausdorff` for `Finset` parameterized by arbitrary distance.
	- `DiscreteFutureContinuity.lean`: `jplus_discreteHausdorff_coverage` — Lipschitz-style bound for `JplusFinset` under edge perturbations.
	- **Moved to TODO-completed.md (2026-02-22).**

- [ ] Curved toy adjacency model: blocked here (numerical solver work moved).
	- Location: implement in `aqei-numerical-validation`.
	- **No PDE solving.** Pick a single fixed combinatorial discretization (e.g. a
	  Regge-calculus-inspired triangulated 2-disk with 10–20 vertices) and define its
	  causal adjacency matrix by hand from a known closed-form curvature.
	  The observable must run `< 1s` deterministically in `--test-mode`.
