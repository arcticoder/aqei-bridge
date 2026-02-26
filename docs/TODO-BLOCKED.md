# TODO: Blocked Items

## Still Blocked

- [ ] **Full Mathlib sheaf cohomology**: Use `lean/src/AqeiBridge/Cech01.lean` scalar Čech complex.
  Next step: define `F(U) = monotone maps U → ℤ`, implement full Čech 0/1/2 cochain complex,
  prove `H¹ = 0` for acyclic posets.
  Blocked on: connecting `F(U)` restriction to `Cech01`'s abstract complex scaffold.

- [ ] **Mathematica worldline bumps**: Pipeline moved to `aqei-numerical-validation`.
  No action in this repo.

- [ ] **Curved toy adjacency model**: Numerical solver work moved to `aqei-numerical-validation`.
  No action in this repo.

## Unblocked (resolved)

- [x] Poset homology / order complex — `OrderComplexProxy.lean` + `OrderComplexBridge.lean`
- [x] Future-set topology / Hausdorff distance — `GraphDistance.lean` + `DiscreteHausdorff.lean`
- [x] Čech H¹ vanishing scaffold — `Cech01.lean`
