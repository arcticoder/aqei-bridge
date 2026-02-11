# TODO: Backlog (Long-Term)

Refined: Moved unblocked items to active TODO.md (e.g., formalizations leveraging recent discrete toy). Aligned with proving conjecture + bridge to topological chronology (add causal sets/posets from recent Lean work). Review after Phase 2.

## Phase 3: Improve Heuristics & Bridge (Medium Priority)
- [ ] Improve causal observable: Add geodesic tracing. Sample Mathematica (unblocked from synthetic):
  ```mathematica
  NDSolve[{t''[λ] == 0, x''[λ] + PerturbedGamma[x[λ]] (x'[λ])^2 == 0}, {t, x}, {λ, 0, 1}]
  ```
- [ ] Multi-ray analysis: Proxy connectedness via overlap; use Python persistent homology (networkx/scipy).
- [ ] 2+1D toys: Cylindrical grid; build on 1+1D pipeline (commit b91cc67).
- [ ] Enhance analyze_candidates.py: Emit Lean bounds. Sample:
  ```python
  with open('lean/Generated.lean', 'w') as f:
      f.write(f'conjecture DeltaBound : Δ ≤ {computed_bound} := sorry')
  ```
- [ ] Parameter sweeps: Numpy meshgrid; log via recent orchestrator updates.

## Phase 4: Toward Proof / Disproof & Bridge Conjecture (Long Term)
- [ ] Large-scale searches: Maximize Δ; if bounded, lemma in Lean.
- [ ] Realistic backgrounds: Minkowski to Schwarzschild; use post-Newtonian.
- [ ] Linearized solver: Full in loop. Sample:
  ```mathematica
  hSol = DSolve[δG == 8 π δT, h, {t,x}];
  ```
- [ ] Prove cases: Weak-field, 1+1D (extend discrete toy).
- [ ] Counterexamples: Refine neighborhood size.
- [ ] Bridge: Add poset in Spacetime.lean (partial order); Alexandrov topology; conjecture as invariant cohomology. Use history.md Sonnet 4.5 ideas on discrete proxies.

## General / Ongoing
- [ ] Visualizations: ContourPlot; export to docs/.