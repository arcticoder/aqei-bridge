# TODO: Active Queue for AQEIBridge Workflow

Based on latest commits (e.g., cdd944a updating backlog with Phase 3 completions, 33ec9a5 implementing geodesic and bounds, c10aaa8 Phase 2 implementations), check off completed items and promote Phase 4 tasks. Conjecture remains unproven but supported by bounded searches—no pivot needed yet. Start manuscript expansion for documentation/proof consolidation. Focus on bridge to topological conjecture via causal posets. Limit to 5-10 items; move completed to docs/TODO-completed.md.

## Phase 3: Improve Heuristics & Bridge (Medium Priority)
- [x] Add 2+1D toys: Done with cylindrical grid refinements (implied in Phase 3 enhancements, commit b0e5dd5).
- [ ] Refine multi-ray analysis: Add math for connectedness proxy (e.g., \( \int_{rays} \Delta(\gamma) d\mu > \theta \) for overlap). Sample Python:
  ```python
  import numpy as np
  def connectedness_proxy(rays, deltas, theta=0.5):
      overlaps = np.sum([delta > theta for delta in deltas])
      return overlaps / len(rays)  # Fraction of overlapping futures
  ```

## Phase 4: Toward Proof / Disproof & Bridge Conjecture (High Priority, Next 1-2 days)
- [ ] Large-scale searches: Maximize Δ with Phase 3 tools; if bounded, add Lean lemma. Math: Bound \( \Delta \leq \sup_{T \in \mathcal{C}_{AQEI}} \int h_T d\lambda \). Sample Mathematica:
  ```mathematica
  constraints = Table[Integrate[T φ_i, {t, -∞, ∞}] >= 0, {i, samplers}];
  maxDelta = NMaximize[{Δ[h /. LinearizedEinstein[T]], constraints}, params, Method -> "DifferentialEvolution"];
  ```
- [ ] Realistic backgrounds: Implement Schwarzschild perturbations. Math: Metric \( ds^2 = -(1 - 2M/r) dt^2 + (1 - 2M/r)^{-1} dr^2 + r^2 dΩ^2 + h \). Sample Python solver:
  ```python
  from scipy.integrate import solve_ivp
  def schwarzschild_geodesic(t, y, M, h_pert):
      r, theta, phi, pr, ptheta = y  # State vector
      drdt = pr / (1 - 2*M/r)  # + perturbation term from h
      return [drdt, ...]  # Full eqs with h
  sol = solve_ivp(schwarzschild_geodesic, [0, tmax], y0, args=(M, h))
  ```
- [ ] Linearized solver: Refine in loop. Sample Lean formalization:
  ```lean
  def LinearizedEinstein {M : LorentzianManifold} (T : StressEnergyTensor) : MetricPerturbation :=
    solve (δG g = 8 * π * T)  -- Using Mathlib PDE stubs
  lemma BoundedPert : ∀ T ∈ AQEI_Cone, ‖LinearizedEinstein T‖ ≤ C * ‖T‖ := sorry
  ```
- [ ] Prove special cases: Weak-field 1+1D. Math: In limit ε→0, J⁺ continuous via \( d_H(J^+_g, J^+_{g+h}) \leq O(ε) \) (Hausdorff distance). Sample Lean:
  ```lean
  lemma WeakFieldStability (ε : ℝ) (hε : ε small) : ∀ T, Norm T < ε → Continuous (CausalFutureMap T) := by
    rw [continuity_def]; intro U open; ... -- Proof sketch using topology
  ```

## Immediate Cross-Phase Tasks
- [ ] Expand manuscript in `docs/manuscript.md`: Add sections on proofs, bridge conjecture. Include math: Causal poset \( (M, \preceq) \) where \( p \preceq q \) iff q ∈ J⁺(p). Topology: Alexandrov intervals [p,q] = {r | p ≼ r ≼ q}.
- [ ] Update README: Highlight Phase 4 focus, bridge to chronology protection invariant.
```

