# TODO: Blocked Items

Minimal after latest commits (e.g., diagnostics/posets unblock proxies). Moved unblock paths to active.

- [ ] Full Mathlib sheaf cohomology: Still blocked on infrastructure; use a presheaf proxy + homology alternative.
	- Unblocked scaffold (Lean): `lean/src/AqeiBridge/AlexandrovPresheaf.lean` defines `OpenInAlexandrov` and a minimal `PresheafOnPoset` interface (objects + restriction maps).
	- Next concretization (Lean): define a presheaf of “sections of futures” over Alexandrov opens and implement a Čech-style H¹ for finite covers, or reduce to a chain-complex proxy on a finite basis of opens.

- [ ] Poset homology / order complex in Lean (full): still blocked on selecting a concrete (finite) poset representation + a minimal invariant target (order complex vs graph/CW proxy).
	- Unblocked starter: a minimal chain-level 1-cycle proxy is now implemented in Lean for causal posets (`PosetHomologyProxy.lean`) and for directed graphs (`DiscreteHomologyProxy.lean`).
	- Unblocked infrastructure: functorial pushforwards + invariance under point `OrderIso` (so the proxy behaves like an actual invariant under isomorphism).
	- Next concretization: pick one target invariant (e.g. order complex simplicial homology) and prove one lemma tying it to chronology proxies.
		- Suggested rep: a finite poset structure with an explicit `Finset` of events + decidable relation.
		- Suggested target: order complex `Δ(P)` and simplicial/chain homology in degree 1; relate it to the existing `Z1 := ker ∂₁` proxy.

- [ ] Replace synthetic AQEI constraints with worldline sampling bumps in Mathematica: blocked here (Mathematica pipeline moved).
	- Location: implement in `aqei-numerical-validation/mathematica/`.
	- Next concretization: add an *optional* mode that precomputes bump weights on the existing grid so constraints remain linear in coefficients.

- [ ] Future-set topology/continuity (Hausdorff distance on subsets) in Lean: blocked on choosing a metric/topology on the base space and aligning it with the repo’s current abstract `Spacetime` interface.
	- Unblocked scaffold (Lean): `lean/src/AqeiBridge/DiscreteHausdorff.lean` defines a Hausdorff-style distance `discreteHausdorff` for `Finset` parameterized by an arbitrary distance function.
	- Next concretization: specialize to a discrete metric (graph distance / Hamming / Jaccard) and prove a Lipschitz-style bound for futures under edge perturbations.

- [ ] Realistic backgrounds (e.g., Schwarzschild) and curved sweeps: blocked here (numerical solver work moved).
	- Location: implement in `aqei-numerical-validation` (Python numeric sweep harness + deterministic `--test-mode`).
	- Next concretization: pick one toy discretization and an observable that runs <1s deterministically.
