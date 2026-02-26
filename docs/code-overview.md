# Code Overview: AQEIBridge Repository

A guided tour of the Lean 4 source files.

**Last updated:** 2026-02-23

---

## Lean 4 Formalization (`lean/src/AqeiBridge/`)

### Stress-energy and AQEI cone

#### `StressEnergy.lean`
Finite-dimensional stress-energy vectors: `StressEnergy n := Fin n → ℝ`.
`AQEIFunctional n` packages a linear functional `L` and a bound `B`.

#### `AQEI_Cone.lean`
Convex polyhedron `AQEI_cone F` as a finite halfspace intersection.
Key theorems: `AQEI_cone_convex`, `AQEI_cone_isClosed`.

---

### Abstract causal structure

#### `CausalPoset.lean`
Abstract causal preorder `CausalPoset` (reflexive, transitive).
`causalFuture p`, monotonicity, union lemmas.

#### `CausalIntervals.lean`
Order intervals, Alexandrov topology, `causalFuture_open`.

#### `CausalContinuity.lean`
Thin interface layer for continuity statements (future work hook).

#### `SpacetimeCausalPoset.lean`
Interface axioms linking a Lorentzian spacetime to the abstract causal poset.
Placeholder for full differential-geometry integration.

#### `Spacetime.lean`
Lorentzian manifold interface skeleton (axiomatized; not yet formally developed).

---

### Discrete graph models

#### `DiscreteCausalPoset.lean`
Directed finite graph as a causal poset: `DiscreteSpacetime`, `Edge`, `JplusFinset`.

#### `DiscreteCausality.lean`
`EdgeHom` (strict-edge-preserving maps), composition, identity.

#### `DiscreteChronology.lean`
Chronology and acyclicity predicates for discrete spacetimes.

#### `FiniteCausalPoset.lean`
Finite causal poset with chain enumeration; bridge to simplex types.

---

### Discrete Hausdorff and graph distance

#### `DiscreteHausdorff.lean`
`discreteHausdorff d A B` — symmetric Hausdorff distance over a discrete metric.

#### `GraphDistance.lean`
`boundedDist n adj` — bounded shortest-path proxy distance on `Fin n`.

#### `DiscreteFutureContinuity.lean`
`jplus_discreteHausdorff_coverage`: `discreteHausdorff (boundedDist adj) (J⁺(P,p)) (J⁺(Q,p)) ≤ n`.
Lipschitz-style bound for J⁺ sets under graph perturbations.

---

### Homological invariants — chain complex proxy

#### `DiscreteHomologyProxy.lean`
Low-degree chain complex C₀ ← C₁ for discrete graphs.
`Z1 P R := ker(boundary1 P R)`.

#### `PosetHomologyProxy.lean`
Full Mathlib HomologicalComplex proxy: `posetChainComplex`, `H1`.
**Key theorems:** `H1Map_id`, `H1Map_comp` (functoriality), `H1IsoZ1` (H₁ ≅ Z₁).
Also: `H1IsoOfEdgeIso` (invariance under graph isomorphism).

---

### Homological invariants — order complex

#### `OrderComplexProxy.lean`
Simplex types `OC1`, `OC2`; boundary maps `bdy1`, `bdy2`; `bdy1_comp_bdy2 = 0`.
`Z1_oc`, `B1_oc`, `H1_oc` — order-complex cycle/boundary/homology modules.

#### `OrderComplexBridge.lean`
**Key theorem:** `Z1_oc_eq_bot_iff` — full bidirectional equivalence
`Z1_oc R P = ⊥ ↔ Z1 P.toCausalPoset R = ⊥` under `IsCompatible`.

---

### Homological invariants — Čech cohomology proxy

#### `Cech01.lean`
Finite Čech cochain complex: `C0`, `C1`, `C2`, `d0`, `d1`.
`d1_comp_d0 = 0`. `H1Cech := ker(d1) / im(d0)`.
Sanity lemma: `h1Cech_denom_top_of_exact`.

---

### Alexandrov topology / presheaf interface

#### `AlexandrovPresheaf.lean`
Presheaf of sections over the Alexandrov topology of a causal poset.

#### `AlexandrovPresheafMathlib.lean`
Bridge from the Alexandrov presheaf to the Mathlib presheaf API
(`CategoryTheory.Presheaf`). Used for future sheaf-cohomology integration.

---

### Chamber geometry

#### `Chambers.lean`
`Chamber F active` / `ClosedChamber F active` — polyhedral chambers in
stress-energy space cut by (in)active AQEI constraints.
**Key theorems:** `closedChamber_convex`, `closedChamber_isPathConnected`.

#### `ChamberIndexedModel.lean`
Index-set model: maps chamber index to a `DiscreteSpacetime`.

#### `ChamberClosedChamberBridge.lean`
Bridge between open `Chamber` and closed `ClosedChamber` membership conditions.

#### `DiscreteChamberStability.lean`
Toy implication: if the spacetime map `J` is constant on a chamber, then the
discrete causal future `J⁺(p)` is also constant.

---

### Stability and bridge theorems

#### `H1Stability.lean`
**Core theorem:** `h1_stable_small_pert` — H₁=0 is monotone under subgraph inclusion.
Supporting: `mapEdge_injective`, `push1_injective`, `Z1_eq_bot_of_subgraph`.
**A.2:** `h1_dim_le_of_subgraph` — `Module.rank ℤ (Z₁ M₁) ≤ Module.rank ℤ (Z₁ M₂)`.

#### `DiscreteConnectedComponents.lean`
Connected-component infrastructure for `DiscreteSpacetime`:
- `undirGraph M : SimpleGraph Pt` — symmetrize directed edges via `SimpleGraph.fromRel`.
- `numComponents M : ℕ` — `Fintype.card (undirGraph M).ConnectedComponent`.
- `numComponents_antitone` — `EdgeHom M₁ M₂ id → numComponents M₂ ≤ numComponents M₁`.

#### `DiscreteH1QuantitativeUpgrade.lean`
**A.5 — Betti-number / quantitative H₁ upgrade** (1 sorry):
- `numDirEdges M : ℕ` — directed edge count.
- `rank_Z1_formula` [sorry] — `rank Z₁ + |V| = |E_directed| + c(G_undir)`.
- `h1_quantitative_upgrade` — `numDirEdges M₁ + numComponents M₁ ≤ numDirEdges M₂ + numComponents M₂`
  under `EdgeHom M₁ M₂ id`. Proof: A.2 + rank formula (Cardinal calc).

#### `CausalStability.lean`
`admissible_region_pathConnected` — AQEI cone is path-connected (given nonemptiness).
Wraps `Convex.isPathConnected` from Mathlib.

#### `DiscreteStabilityBridge.lean`
**Main bridge:** `aqei_bridge_conjecture_discrete` + `aqei_bridge_full`.
Packages H₁ stability + AQEI cone path-connectedness in a single theorem.

---

### Open conjectures and axiom interface

#### `Conjecture.lean`
`causal_futures_path_connected` — the original informal conjecture, now trivially
discharged in the discrete model.

#### `GlobalConjectures.lean`
`global_h1_invariance` (interface axiom), `acyclic_iff_of_orderIso` (proven).

---

### Static test data

#### `GeneratedPosetConjectures.lean`
Static Lean data file containing example poset Z₁ dimension results
(`posetZ1Results`) computed from Minkowski-like test graphs.
Imported by the top-level `AqeiBridge.lean` as a sanity data fixture.
*(Previously auto-generated; now a checked-in static fixture.)*

---

## Tests

```bash
./run_tests.sh      # filtered lake build + lean_tests.sh
tests/build_lean.sh # lake build with Mathlib noise suppressed
```

Output log: `lean/build.log`.

## Papers

`papers/discrete-causal-posets-lean4.tex` — the formal methods manuscript
targeting CPP / ITP / JAR.
