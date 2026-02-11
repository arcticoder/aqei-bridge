# TODO: Active Queue for AQEIBridge Workflow

Updated per latest commits (e.g., cdd944a completing Phase 3 backlog items; a8bafa9 geodesic/sweeps; 33ec9a5 bounds/geodesics; b0e5dd5 analysis/visuals; c10aaa8 Phase 2). Check off completed; promote Phase 4 for proof focus. Limit to 5-10 items; move done to TODO-completed.md.

## Phase 4: Toward Proof / Disproof & Bridge Conjecture (High Priority, Next 1-2 days)
- [ ] Large-scale searches: Run Δ maximization with sweeps; formalize if bounded. Math: Seek \(\sup_{T \in \mathcal{C}_{AQEI}} \Delta(T) < \infty\) where \(\Delta = \int_{\gamma} h_{ab} k^a k^b d\lambda\) along null \(\gamma\). Sample Python (extend orchestrator.py):
  ```python
  import numpy as np
  from multiprocessing import Pool
  def delta_max_worker(params):
      # params: (sigma, N_basis, epsilon)
      run_pipeline(params)  # From Phase 3
      return compute_delta()  # Max causal shift
  param_grid = np.meshgrid(np.linspace(0.1, 1, 10), range(5, 20), np.logspace(-3, -1, 5))
  with Pool(4) as p:
      deltas = p.map(delta_max_worker, param_grid.ravel())
  bound = np.max(deltas)
  print(f"Computed bound: {bound}")
  ```
- [ ] Realistic backgrounds: Implement Schwarzschild perturbations. LaTeX: Perturbed metric \( g_{ab} + h_{ab} \), with \( h \) from \(\delta G_{ab} = 8\pi T_{ab}\). Sample Mathematica:
  ```mathematica
  schwarzMetric = - (1 - 2 M / r) dt^2 + (1 - 2 M / r)^(-1) dr^2 + r^2 (dθ^2 + Sin[θ]^2 dφ^2);
  linearizedEq = D[ h[μ,ν], {x^ρ, 2}] + ... == 8 π T[μ,ν];  (* Simplified Regge-Wheeler gauge *)
  hSol = NDSolve[linearizedEq /. AQEIConstraints, h, {t, 0, tmax}];
  ```
- [ ] Linearized solver refinement: Integrate in loop for curved backgrounds. Sample Lean bound:
  ```lean
  lemma PerturbationBound {M : LorentzianManifold} (T : StressEnergyTensor) (hT : AQEIAdmissible T) :
    ‖LinearizedEinstein T‖ ≤ C * ‖T‖ := by
      sorry  -- Proof via energy estimates, use Mathlib.Analysis.Normed
  ```
- [ ] Prove special cases: Weak-field stability. Math: Show path-connectedness via \( d_H(J^+_g, J^+_{g+h}) \leq O(\|h\|) \) (Hausdorff dist). Sample Lean:
  ```lean
  import Mathlib.MeasureTheory.Measure.Hausdorff
  lemma WeakFieldConnected (ε : ℝ) (hε : 0 < ε) (T : StressEnergyTensor) (hT : ‖T‖ < ε) :
    PathConnected (FamilyCausalFutures (g + LinearizedEinstein T)) := by
      apply continuous_family; -- Use topology continuity
      rw [hausdorff_dist_bound]; exact O(ε) from pert_bound
  ```
- [ ] Bridge integration: Add poset invariants. LaTeX: Causal poset \((M, \preceq)\), Alexandrov topology basis \{ [p,q] = \{ r \mid p \preceq r \preceq q \} \}.

## Immediate Cross-Phase Tasks
- [ ] Expand manuscript: Add Phase 4 results, bridge section. Include LaTeX conjecture reformulation: Chronology protection iff \( H^1(M, \mathcal{F}) = 0 \) for sheaf \(\mathcal{F}\) on causal events.
- [ ] Update README: Reflect Phase 4 shift, latest commits.
```


