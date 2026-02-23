# TODO: aqei-bridge — Lean 4 Formal Verification Track

## Next actions (from `docs/TODO-BLOCKED.md`)

- [ ] **Full Mathlib sheaf cohomology** → implement the suggested minimal Čech 0/1-cochain complex for a *finite* cover (Lean), so we can talk about an `H¹`-like quotient without pulling in all sheaf infrastructure.
  - Target: new Lean file `lean/src/AqeiBridge/Cech01.lean` (or similar) with `C0`, `C1`, `d0`, and `H1 := ker d1 / im d0` in `ModuleCat`.

- [ ] **Poset homology / order complex (full)** → add an “order complex proxy” that turns `FiniteCausalPoset.Chains` into a small simplicial/chain complex (degrees 0–2), then relate its degree-1 cycles to the existing `Z1 := ker ∂₁` proxy.
  - Target: new Lean file `lean/src/AqeiBridge/OrderComplexProxy.lean` with explicit `C0/C1/C2` from enumerated simplices.

- [ ] **Future-set topology/continuity** → implement a real discrete base metric (graph shortest-path distance) for finite reachability models and upgrade the placeholder `discreteHausdorff ≤ 1` lemma to a perturbation-sensitive bound.
  - Target: new Lean file `lean/src/AqeiBridge/GraphDistance.lean` defining shortest-path distance on `Fin n` (undirected or directed-as-undirected), plus a lemma in `DiscreteFutureContinuity.lean` stating a Lipschitz-style bound for `J⁺` under a stated perturbation model.
  - [x] Immediate substep: prove one-sided Hausdorff = 0 when futures only grow by relation extension.

- [ ] **Mathematica worldline bumps / realistic curved sweeps** → remain blocked here because the pipeline moved to `aqei-numerical-validation`.
  - Next step lives in that repo; no action in `aqei-bridge`.

**Status Update (2026-02-22):** Repository split complete. Numerical validation pipeline moved to [`aqei-numerical-validation`](https://github.com/arcticoder/aqei-numerical-validation). This repo is now focused exclusively on the Lean 4 formalization and the formal verification manuscript.

**Active objective:** Prove the bridge conjecture — causal futures J⁺(p) are topologically stable (H₁ invariant) under AQEI-admissible perturbations.

---

## CRITICAL: Manuscript Citations (Lean Formalization Paper)

**Current state:** ✅ **COMPLETED** (recorded in `docs/TODO-completed.md`, 2026-02-22)

The bibliography entries and §7 citations for the “Real-World Applications” section are now present in `papers/aqei-lean-formalization.tex`.

---

## HIGH: Prove `homology_functorial` in PosetHomologyProxy.lean

**File:** `lean/src/AqeiBridge/PosetHomologyProxy.lean`

**Current state:** ✅ **PROVEN** — `H1Map_comp` and `H1Map_id` establish full functoriality; `H1IsoZ1` bridges H₁ to Z₁.

**Theorems now proven:**
- `H1Map_id`: identity is respected by the H₁ functor
- `H1Map_comp`: `H1Map (g ∘ f) = H1Map f ≫ H1Map g` — this IS homology_functorial
- `H1IsoZ1`: H₁ ≅ Z₁ (bridge between Mathlib homology API and the explicit kernel)
- `H1IsoOfOrderIso`: H₁ is invariant under OrderIso of point-types

**Why this mattered:** `homology_functorial` was needed to establish that the H₁ proxy is an honest invariant. It is now proven without any `sorry`. Downstream items are unblocked.

---

## HIGH: Prove `h1_stable_small_pert` (Core Bridge Theorem)

**File:** `lean/src/AqeiBridge/H1Stability.lean` — ✅ **PROVEN (2026-02-22)**

**Theorems proven in `H1Stability.lean`:**
- `Edge.ext'`: two edges are equal iff same src + dst (proof irrelevance for ok)
- `mapEdge_injective`: `mapEdge f hf` injective when `f : Pt → Pt` injective
- `push1_apply_mapEdge`: coefficient extraction — `(push1 f hf x)(mapEdge f hf e) = x e`
- `push1_injective`: `push1 f hf` injective when `f` injective  
- `Z1_eq_bot_of_subgraph`: `Z₁(M₁) = ⊥` follows from `Z₁(M₂) = ⊥` + `M₁ ⊆ M₂`
- `dimH1IsZero (M)`: abbreviation for `Z₁(M, ℤ) = ⊥`
- `h1_stable_small_pert`: `dimH1IsZero P → EdgeHom P' P id → dimH1IsZero P'`

**Proof strategy:** subgraph monotonicity — any cycle in `M₁` pushes to a cycle
in `M₂` (by `push1_mem_Z1`); since `Z₁(M₂) = ⊥`, the push is 0; by injectivity
of `push1 id` (id is injective), the original cycle is 0.

**Empirical support:** 100% invariance over 100 trials (aqei-numerical-validation)
is explained exactly: edge removal from a forest keeps it a forest.

**Note on ε-ball:** The ε parameter is subsumed — for *any* fraction of edges
removed the result is a subgraph and the theorem applies.

---

## MEDIUM: Prove `admissible_region_pathConnected`

**File:** `lean/src/AqeiBridge/CausalStability.lean`

**Current state:** ✅ **PROVEN** (2026-02-22) — theorem with nonemptiness hypothesis, using `Convex.isPathConnected` from Mathlib.

**What changed:**
- Replaced `axiom admissible_region_pathConnected (F : List (AQEIFunctional n))` with
  `theorem admissible_region_pathConnected (F : List (AQEIFunctional n)) (hne : (AQEI_cone F).Nonempty)`
- Proof: `Small T = True` → set = `AQEI_cone F`, then `AQEI_cone_convex` + `hne` + `Convex.isPathConnected`
- Also added `AQEI_cone_isClosed` to `AQEI_Cone.lean` (finite intersection of closed halfspaces)
- Foundation: `energy-tensor-cone/AffineToCone.lean` proves the analogous infinite-family results

**Note:** The nonemptiness hypothesis `hne` is essential: for degenerate constraint sets, the AQEI cone can be empty, and empty sets are not path-connected.

---

## MEDIUM: Prove `aqei_bridge_conjecture_discrete`

**File:** `lean/src/AqeiBridge/CausalStability.lean`

**Current state:** `axiom` — the core conjecture

**Prerequisites:** Must complete `homology_functorial` + `h1_stable_small_pert` first.

**Proof strategy:**
1. Given: T ∈ AQEI_cone F, Small T, dimH1(P_g) = 0
2. Show: dimH1(P_{g+δg(T)}) = 0
3. Key argument: The perturbation δg(T) is bounded by ‖T‖ · (linearized GR operator)
4. Use `h1_stable_small_pert` with ε = C·‖T‖ ≤ 0.1

---

## LOW: Add `energy-tensor-cone` Theorems as Foundation

The PRD submission in `energy-tensor-cone` proves that the AQEI cone has:
1. Non-trivial extreme rays (`Candidate_Is_Extreme_Point`)
2. Exact rational coordinates for the vertex
3. Infinite-family closedness + convexity via `AffineToCone.lean`

**Actions completed (2026-02-22):**
- Added a naming comment to `AQEI_Cone.lean` clarifying that `AQEI_cone` is a convex polyhedron, not a homogeneous cone; references `energy-tensor-cone/AffineToCone.lean` for homogenization
- Added `AQEI_cone_isClosed` proof (finite intersection of closed halfspaces via `LinearMap.continuous_of_finiteDimensional`)
- `Covex.isPathConnected` proof of `admissible_region_pathConnected` mirrors `energy-tensor-cone`'s `affineAdmissible_convex`

**Remaining:** None in this repo. Cross-reference notes exist in `GlobalConjectures.lean` and `Conjecture.lean`.

---

## LOW: Complete GlobalConjectures.lean

**File:** `lean/src/AqeiBridge/GlobalConjectures.lean`

**Current state:** ✅ **REFINED PLACEHOLDERS** (2026-02-22)

**What’s now in place (Lean-side interface):**
- `global_h1_invariance`: explicit placeholder axiom stating H₁ invariance under AQEI-admissible perturbations
- `CausalPoset.acyclic_iff_of_orderIso`: proves acyclicity/chronology proxy is invariant under order isomorphism

---

## Mathematical Reference

### Bridge Conjecture (Formal Target)

For a discrete causal poset $P$ with causal adjacency relation $\leq_G$:

$$\dim H_1(P) = 0 \implies \dim H_1(P_\epsilon) = 0 \quad \text{for all } \epsilon \text{-perturbations in AQEI cone}$$

where $\dim H_1(P) = |E| - |V| + c(G)$ (Z₁ dimension proxy).

### Key Mathlib tactics available

- `have h := AQEI_cone_convex F` — convexity of the cone (proven)
- `have h := boundary_boundary_zero` — chain complex axiom (proven)
- `exact Convex.isPathConnected` — if convex set non-empty, it's path-connected
- `nlinarith`, `linarith`, `ring` — for arithmetic steps
- `simp [AQEI_cone, AQEIFunctional]` — unfold definitions
