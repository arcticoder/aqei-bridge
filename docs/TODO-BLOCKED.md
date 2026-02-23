# TODO: Blocked Items

Minimal after latest commits (e.g., diagnostics/posets unblock proxies). Moved unblock paths to active.

- [ ] Full Mathlib sheaf cohomology: Still blocked on infrastructure; use a presheaf proxy + homology alternative.
	- Unblocked scaffold (Lean): `lean/src/AqeiBridge/AlexandrovPresheaf.lean` defines `OpenInAlexandrov` and a minimal `PresheafOnPoset` interface (objects + restriction maps).
	- Unblocked scaffold (Mathlib interface): `lean/src/AqeiBridge/AlexandrovPresheafMathlib.lean` defines a genuine Mathlib presheaf `TopCat.Presheaf CommRingCat` on the Alexandrov topological space: continuous ℝ-valued functions on opens (`realContinuousPresheaf`).
	- Sanity instantiation: `lean/src/AqeiBridge/Examples/DiamondPresheaf.lean` builds this presheaf on a 4-point diamond preorder (`Fin 2 × Fin 2` with product order).
	- Next concretization (Lean): define a presheaf of “sections of futures” over Alexandrov opens and implement a Čech-style H¹ for finite covers, or reduce to a chain-complex proxy on a finite basis of opens.
		- Suggested minimal step: implement a Čech 0/1-cochain complex for a *finite* cover of an open and define `H¹` as a quotient kernel/image in `CommRingCat` or `ModuleCat`.

- [ ] Poset homology / order complex in Lean (full): still blocked on selecting a concrete (finite) poset representation + a minimal invariant target (order complex vs graph/CW proxy).
	- Unblocked starter: a minimal chain-level 1-cycle proxy is now implemented in Lean for causal posets (`PosetHomologyProxy.lean`) and for directed graphs (`DiscreteHomologyProxy.lean`).
	- Unblocked scaffold (Lean): `lean/src/AqeiBridge/FiniteCausalPoset.lean` defines `FiniteCausalPoset (n : ℕ)` on `Fin n` with decidable relation + a computable `Chains` enumeration.
	- Unblocked infrastructure: functorial pushforwards + invariance under point `OrderIso` (so the proxy behaves like an actual invariant under isomorphism).
	- **DONE: `OrderComplexBridge.lean`** proves `Z1_oc_eq_bot_of_posethom`: the PosetHomologyProxy acyclicity (`Z1 = ⊥`) implies OC acyclicity (`Z1_oc = ⊥`), via an explicit injection `OC1 P → Edge (P.toCausalPoset)` and boundary-map commutativity (see `TODO-completed.md`, 2026-02-22).
	- Next concretization: prove the converse direction (OC acyclicity implies Poset acyclicity when `P.rel a b → a ≤ b` in `Fin n`), giving a full isomorphism of the two proxies on "upward" posets.

- [ ] Replace synthetic AQEI constraints with worldline sampling bumps in Mathematica: blocked here (Mathematica pipeline moved).
	- Location: implement in `aqei-numerical-validation/mathematica/`.
	- Next concretization: add an *optional* mode that precomputes bump weights on the existing grid so constraints remain linear in coefficients.

- [x] **DONE** Future-set topology/continuity (Hausdorff distance on subsets) in Lean:
	- `GraphDistance.lean`: bounded shortest-path proxy `boundedDist` on `Fin n`.
	- `DiscreteHausdorff.lean`: `discreteHausdorff` for `Finset` parameterized by arbitrary distance.
	- `DiscreteFutureContinuity.lean`: `jplus_discreteHausdorff_coverage` — Lipschitz-style bound for `JplusFinset` under edge perturbations.
	- **Moved to TODO-completed.md (2026-02-22).**

- [ ] Realistic backgrounds (e.g., Schwarzschild) and curved sweeps: blocked here (numerical solver work moved).
	- Location: implement in `aqei-numerical-validation` (Python numeric sweep harness + deterministic `--test-mode`).
	- Next concretization: pick one toy discretization and an observable that runs <1s deterministically.
