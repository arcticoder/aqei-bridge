# TODO: Backlog (Long-Term)

Updated with completions (e.g., cdd944a Phase 3 checks, b0e5dd5 visualizations/analysis). Promote proofs/bridge to active. If conjecture holds (from searches), pivot to full bridge conjecture formalization/manuscript. Review post-Phase 4.

## Phase 4: Toward Proof / Disproof & Bridge Conjecture (Long Term)
- [ ] Counterexamples check: Refine if emerge. Math: Check if ∃ T s.t. homotopy class changes, e.g., formation of closed timelike curves (CTC) via \( \pi_1(\mathcal{J}) \neq 0 \).
- [ ] Bridge integration: Implement sheaf cohomology. Sample Mathematica poset viz:
  ```mathematica
  poset = RelationGraph[Precedes, events, VertexLabels -> Automatic];
  cohomology = SheafCohomology[poset, sheaf];  (* Placeholder with custom sheaf *)
  ```
- [ ] Prove full conjecture: General case using order invariants. Sample Lean:
  ```lean
  conjecture TopologyChronologyProtection (M : CausalPoset) :
    InvariantUnderPert (SheafCohomology M) ∧ NoCTCIfAcyclic M
  ```

## General / Ongoing
- [x] Replace synthetic AQEI: Done with Fewster averages (commit a8bafa9 updates).
- [ ] Add cluster support: For large searches; use multiprocessing in Python.
  ```python
  from multiprocessing import Pool
  def search_worker(params): return maximize_delta(params)
  with Pool(4) as p: results = p.map(search_worker, param_list)
  ```
- [ ] Visualizations: Add poset graphs. Sample Python:
  ```python
  import networkx as nx
  import matplotlib.pyplot as plt
  G = nx.DiGraph([(p, q) for p in events for q in J_plus(p)])
  nx.draw(G, with_labels=True); plt.savefig('poset.png')
  ```