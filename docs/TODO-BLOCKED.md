# TODO: Blocked Items

Minimal based on latest commits (Phase 2/3 progress unblocked most via implementations). 

- [ ] Integrate Mathlib sheaf cohomology: Blocked on maturity; alt: Use Topology.Sheaf basics for posets (move to active if ready).
- [x] License: Unblocked—committed MIT default (implied in doc refreshes, commit 94aea93).

## Phase 4 tasks (moved out of active TODO)

- [ ] Large-scale searches (global maximize Δ): blocked on choosing a computational method that fits our reproducibility + CI constraints (Mathematica `NMaximize` / evolutionary methods are slow + nondeterministic in CI).
- [ ] Realistic backgrounds (Schwarzschild perturbations): blocked on selecting a concrete toy discretization + dependencies (likely SciPy ODE solve) and defining the “observable” to compare to `J^+`.
- [ ] Linearized solver “in loop”: blocked on (a) a stable PDE solver choice for the toy, and (b) a Lean-side interface that doesn’t pretend Mathlib has PDE stubs it doesn’t.
- [ ] Prove special cases (weak-field 1+1D continuity of `J^+`): blocked on pinning down a topology/metric on the space of futures to even state the continuity lemma precisely.