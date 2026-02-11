# TODO: Backlog (Long-Term)

Updated with completions (e.g., cdd944a Phase 3 checks; b0e5dd5 visuals/analysis). Promote proofs/bridge to active. If conjecture holds, pivot to manuscript submission/full bridge formalization. Review after active queue.

## Phase 4: Toward Proof / Disproof & Bridge Conjecture (Long Term)
- [ ] Counterexamples check: Scan for homotopy changes, e.g., CTC via non-trivial \(\pi_1(\mathcal{J})\). Sample Python detector:
  ```python
  def detect_ctc(futures):
      # futures: dict of perturbed J+
      graph = nx.DiGraph([(p, q) for p in points for q in futures[p]])
      return nx.has_cycle(graph)  # Proxy for closed timelike curves
  ```
- [ ] Full conjecture proof: Generalize using invariants. Sample Mathematica poset:
  ```mathematica
  events = Table[{t, x}, {t, 0, 10}, {x, 0, 10}];
  precedes[p_, q_] := (q[[1]] - p[[1]])^2 >= (q[[2]] - p[[2]])^2 && q[[1]] > p[[1]];
  posetGraph = RelationGraph[precedes, events];
  alexandrovBasis = Table[Select[events, precedes[p, #] && precedes[#, q] &], {p, events}, {q, events}];
  ```
- [ ] Bridge: Implement sheaf cohomology proxy. Lean sketch:
  ```lean
  structure CausalPoset where
    events : Type*
    precedes : events → events → Prop
    refl_trans : Reflexive precedes ∧ Transitive precedes
  def SheafCohomology (P : CausalPoset) (F : SheafOnPoset P) : Type* := sorry  -- H^1
  conjecture ChronologyInvariant (P : CausalPoset) : Acyclic P → H¹(P, F) = 0 := sorry
  ```

## General / Ongoing
- [ ] Add cluster support: Extend multiprocessing for searches.
- [ ] Visualizations: Add poset graphs. Sample Python:
  ```python
  import networkx as nx
  import matplotlib.pyplot as plt
  G = nx.DiGraph()
  for p in events:
      for q in J_plus(p): G.add_edge(p, q)
  nx.draw(G, with_labels=True)
  plt.savefig('docs/poset_viz.png')
  ```