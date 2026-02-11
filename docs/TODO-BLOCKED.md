# TODO: Blocked Items

This file holds tasks that are currently too underspecified or too expensive/non-deterministic for the repo’s CI + reproducibility goals.

- [ ] Sheaf cohomology in Lean (Mathlib): blocked on choosing a concrete target invariant and on Mathlib API maturity for the specific cohomology machinery we’d need.
	- Next concretization: start with `Topology.Sheaves` basics on Alexandrov/poset sites and define a *simple* computable obstruction (even if it is only a proxy).

- [ ] Realistic curved backgrounds (e.g. Schwarzschild): blocked on selecting a discretization + solver stack that fits deterministic CI runs, plus defining a comparable “future observable”.
	- Next concretization: pin a single toy discretization (2D slice, fixed gauge) and an observable we can compute robustly.

- [ ] Linearized solver “in the loop”: blocked on a stable PDE/ODE solver choice and performance constraints (Mathematica NDSolve / SciPy) plus a Lean-side interface that doesn’t overclaim analytic content.
	- Next concretization: introduce an explicit numerical tolerance/seed protocol and a small regression dataset in `runs/` (still git-ignored) with documented invariance checks.

- [ ] Weak-field continuity of Lorentzian $J^+$ (1+1D special case): blocked on pinning down a topology/metric on the hyperspace of futures so the statement is precise.
	- Next concretization: pick a *toy* metric on futures (e.g. finite sampling / reachability proxy) and prove the discrete analogue first.

- [ ] “Large-scale” global maximize Δ searches: blocked on CI/runtime and nondeterminism concerns for heavy optimizers.
	- Next concretization: define a bounded sweep family with fixed seeds + timeouts and report empirical bounds as diagnostics (not proofs).