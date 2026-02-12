# TODO: Blocked Items

Minimal after latest commits (e.g., diagnostics/posets unblock proxies). Moved unblock paths to active.

- [ ] Full Mathlib sheaf cohomology: Still blocked on infrastructure; use homology alt in active.

- [ ] Poset homology / order complex in Lean: blocked on selecting a concrete (finite) poset representation and a minimal invariant we can compute/prove without pulling in heavy sheaf infrastructure.
	- Next concretization: start with a finite directed graph/poset representation and prove a small lemma (e.g., acyclic graph ⇒ trivial 1-cycle proxy) before attempting full `Homology`.

- [ ] Replace synthetic AQEI constraints with worldline sampling bumps in Mathematica: blocked on a concrete, test-mode-friendly discretization that preserves linearity (LP structure) and a parameterization consistent with the current toy pipeline.
	- Next concretization: add an *optional* mode that precomputes bump weights on the existing grid so constraints remain linear in coefficients.

- [ ] Future-set topology/continuity (Hausdorff distance on subsets) in Lean: blocked on choosing a metric/topology on the base space and aligning it with the repo’s current abstract `Spacetime` interface.
	- Next concretization: prove a discrete analogue first (finite sets with Hamming/Jaccard distance) and only then consider Hausdorff.

- [ ] Realistic backgrounds (e.g., Schwarzschild) and curved sweeps: blocked on solver stack choice + deterministic runtime constraints.
	- Next concretization: pick one toy discretization and an observable we can compute robustly under `--test-mode`.
