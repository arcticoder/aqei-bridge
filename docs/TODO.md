# TODO: Active Queue for AQEIBridge Workflow

Updated per latest commits (e.g., a9a7f64 futures-map/poset viz; bddac7b Minkowski poset; 15e17fa directed-graph/docs; 331f1d4 diagnostics; 9ec13aa Phase 4 reshape). Previously empty—promote unblocked items from BLOCKED/backlog. Focus on Phase 4 proofs/bridge. Limit to 5-10 items; move done to TODO-completed.md.

## Phase 4: Toward Proof / Disproof & Bridge Conjecture (High Priority, Next 1-2 days)
- [ ] Unblock sheaf cohomology: Implement simpler order-complex homology in Lean (pre-sheaf). LaTeX: Poset homology \( H_k(P) \) via chain complex on simplices (increasing chains). Sample Lean:
  ```lean
  import Mathlib.Topology.Algebra.ChainComplex
  structure OrderComplex (P : CausalPoset) where
    simplices : ∀ k : ℕ, Set (IncreasingChain P k)
  def PosetHomology (P : CausalPoset) (k : ℕ) : Type* := Homology (ChainComplexOf OrderComplex P) k
  lemma AcyclicImpliesTrivialHomology (P : CausalPoset) (h : Acyclic P) : PosetHomology P 1 = 0 := sorry
  ```
- [ ] Replace synthetic AQEI: Select explicit worldline samplings (e.g., Fewster \(\phi\) bumps). Math: Constraints \(\int_{-\infty}^{\infty} T_{ab} k^a k^b f(t) dt \geq 0\) for null \(k\), smooth \(f \geq 0\). Sample Mathematica:
  ```mathematica
  phi[t_] := Exp[-t^2 / (2 sigma^2)];  (* Bump function *)
  aqeiConstraint = NIntegrate[T00[t] phi[t - tau], {t, -∞, ∞}] >= 0;
  NMaximize[{Delta, aqeiConstraint}, params];
  ```
- [ ] Continuity lemmas: Define topology on futures (Hausdorff on power set). LaTeX: \( d_H(A, B) = \max(\sup_{a \in A} d(a, B), \sup_{b \in B} d(b, A)) \). Sample Lean:
  ```lean
  import Mathlib.MeasureTheory.Measure.Hausdorff
  def FutureTopology : TopologicalSpace (Set M) := induced (hausdorffDist) UniformSpace.toTopologicalSpace
  lemma ContinuousFutures (T : StressEnergyTensor) (h : Small T) : Continuous (fun ε => CausalFuture (g + ε * LinearizedEinstein T)) := sorry
  ```
- [ ] Counterexamples check: Integrate CTC detector with poset generators. Sample Python (extend causal_graph_tools.py):
  ```python
  import networkx as nx
  def detect_ctc_from_json(json_path):
      with open(json_path) as f:
          futures = json.load(f)  # {point: list of future points}
      G = nx.DiGraph([(p, q) for p, qs in futures.items() for q in qs])
      return nx.find_cycle(G) is not None  # True if CTC proxy
  ```
- [ ] Realistic backgrounds: Extend sweeps to Schwarzschild with poset discretization.

## Immediate Cross-Phase Tasks
- [ ] Expand manuscript: Add discrete proofs, poset homology, bridge to \( H^1(P, \mathcal{F}) = 0 \) implying no CTCs.

