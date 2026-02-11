# TODO: Backlog (Long-Term)

Lower-priority or dependent items. Review regularly; move to active TODO.md as capacity allows. Aligned with proving core conjecture and bridging to "Chronology protection as topological invariant" (add causal sets, Alexandrov topology, order invariants).

## Phase 3: Improve Heuristics & Bridge (Medium Priority)
- [ ] Improve causal observable in `search.nb`: Add null geodesic ray tracing (solve \ddot{x}^μ + Γ^μ_{αβ} \dot{x}^α \dot{x}^β = 0 numerically). Check focusing via Raychaudhuri equation proxy. Sample Mathematica:
  ```mathematica
  geodesicEq = {x''[λ] + Christoffel[x[λ], t[λ]] x'[λ]^2 == 0, ...};  (* Perturbed metric *)
  NDSolve[geodesicEq, {t, x}, {λ, 0, L}]
  ```
- [ ] Add multi-ray analysis: Proxy path-connectedness by continuous overlap of J⁺(p) under parameter sweeps (e.g., vary ε, check homotopy via persistent homology approx in Python).
- [ ] Explore 2+1D toys: Use cylindrical grid in Mathematica; export to Python for analysis.
- [ ] Enhance `analyze_candidates.py`: Emit Lean conjectures (e.g., "conjecture Bound : Δ ≤ 1.5"). Add Pareto fronts using scipy.optimize. Sample Python:
  ```python
  from scipy.optimize import pareto_front
  fronts = pareto_front(scores, constraints)
  with open('lean/GeneratedCandidates.lean', 'a') as f:
      f.write(f'conjecture FromRun{run_id} : Δ ≤ {max_bound} := sorry\n')
  ```
- [ ] Add parameter sweeps: Use numpy.meshgrid for σ, N_basis; log results.

## Phase 4: Toward Proof / Disproof & Bridge Conjecture (Long Term)
- [ ] Large-scale searches: Use cluster runs (if available) for Δ maximization; if bounded, lemma-ize in Lean.
- [ ] Transition to realistic backgrounds: Start with Minkowski perturbations, then Schwarzschild (use post-Newtonian in Mathematica).
- [ ] Incorporate linearized Einstein: Full solver in Python/Mathematica loop. Sample:
  ```mathematica
  h = DSolve[LinearizedEinsteinEqs == 8 Pi T, h, {t, x}];
  ```
- [ ] Prove special cases in Lean: Vacuum (T=0), weak-field (ε<<1), 1+1D toy.
- [ ] If counterexamples: Refine to local causality or smaller neighborhoods.
- [ ] Bridge integration: Add causal poset in `Spacetime.lean` (partial order on events), Alexandrov topology; conjecture reformulation as invariant sheaf cohomology.

## General / Ongoing
- [ ] Review/incorporate history.md ideas (e.g., non-linear opts, discrete proxies).
- [ ] Add visualizations: Mathematica ContourPlot[h[t,x]]; export PNGs to docs/.

## Phase 2 (deeper formalization subparts)
- [ ] Upgrade `Spacetime.lean` from abstract placeholders to a genuine Lorentzian-manifold development (or a refined discrete model) with a nontrivial `CausalCurve` and `J⁺`.
- [ ] In `CausalStability.lean`: refine the conjecture statement to include *global causal homotopy class invariance* once a concrete causal model exists.
- [ ] Prove continuity/stability lemmas for `J⁺` under small perturbations (likely via a discrete approximation first, then manifold topology).
- [ ] Replace `LinearizedEinstein` placeholder with a meaningful interface (and later an implementation or an axiom tied to external analytic results).