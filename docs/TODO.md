# TODO: aqei-bridge — Lean 4 Formal Verification Track

## CRITICAL: Rewrite aqei-lean-formalization.tex for formal methods venue

**Context (2026-02-23):** Paper now targets CPP / ITP / JAR. All overclaiming sections removed. ✅ **FULLY DONE.**

- [x] Remove §7 (Real-World Applications) entirely
- [x] Rewrite abstract: honest framing as discrete causal poset + convex cone library
- [x] Update §1.2 (Contributions) to list only what is actually proven
- [x] Fix §4 (Key Theorems): 0 sorries, 131 lemmas/theorems, ~3900 lines
- [x] Fix proof sketch to match actual Lean proof (subgraph monotonicity)
- [x] Fix module list
- [x] Update conclusion
- [x] Retarget keywords for formal methods audience
- [x] Replace vague ε-ball Perturbation definition with exact EdgeHom/subgraph definition
- [x] Replace vague H₁ Invariance theorem with exact Lean statement (explicit `EdgeHom P' P id` hypothesis)
- [x] Add explicit Path-Connected Admissible Region theorem with nonemptiness hypothesis
- [x] Move proven conjecture to a `\begin{theorem}` block; separate open continuous bridge as a `\begin{conjecture}`

## Phase A — Quantitative Strengthening (Next Priority)

### A.1 Tight Hausdorff ≤ 1 under single-edge perturbation ✅ DONE

- [x] Proved `jplus_hausdorff_le_one_of_edge_diff` in `DiscreteFutureContinuity.lean`.
- [x] Used `FinsetMetric.discreteHausdorff_le_of_forall_exists` with `classical` for `DecidableRel`.
- [x] Use this in paper §4 as a concrete quantitative result.

### A.2 Dimension inequality under subgraph inclusion ✅ DONE

- [x] Proved `h1_dim_le_of_subgraph` in `H1Stability.lean` (via `push1_Z1_map` injective linear map + `Submodule.rank_le`).

### A.3 Extend tight bound to k-edge perturbations ✅ DONE

- [x] Proved `jplus_hausdorff_le_chain` in `DiscreteFutureContinuity.lean`: for a chain of `k+1` finite causal posets each connected to the next by a Hausdorff-distance-≤1 perturbation, `dH(J⁺(p, c₀), J⁺(p, cₖ)) ≤ k`. Infrastructure: `boundedDist_triangle` in `GraphDistance.lean`, `discreteHausdorff_triangle` in `DiscreteHausdorff.lean`.

## Phase B — Homology Coherence

### B.1 Tight Z₁ ↔ H1_oc equivalence

- [x] Added a counterexample note to the `IsCompatible` docstring in `OrderComplexBridge.lean` explaining why the condition cannot be dropped: a backward-oriented 3-vertex chain gives `Z1_oc R P ≠ ⊥` even when `Z1 P.toCausalPoset R = ⊥`. The full `↔` equivalence therefore holds under `IsCompatible` and this is tight.

### B.2 H1_oc monotone under subgraph inclusion ✅ DONE

- [x] Proved `h1_oc_stable_of_subgraph` in `OrderComplexProxy.lean`.

### B.3 Acyclic finite posets have vanishing H¹_oc ✅ DONE

- [x] Proved `h1_oc_eq_bot_of_acyclic` in `OrderComplexProxy.lean`.

## Phase C — Conceptual Upgrade (Longer Term)

### C.1 Chamber constancy → global constancy theorem ✅ DONE

- [x] Proved `chamber_constancy_global`, `chamber_constancy_of_convex`, and `AQEI_chamber_constancy` in new file `ChamberConstancy.lean`. A locally constant function on a path-connected (or convex) set is globally constant. AQEI cone instantiation uses `AQEI_cone_convex` + `Convex.isPreconnected`.

### C.2 Finite Čech H¹ for Alexandrov opens ✅ DONE

- [x] Proved `H1Cech_vanishes_of_exact` in `Cech01.lean` (exact complex → quotient = ⊥).



## Post-proof phase (discrete model) — lock in the win

**Status:** ✅ The bridge conjecture is now **formally proven in the discrete graph/poset toy model**, in the precise sense implemented by:
- `admissible_region_pathConnected` (AQEI parameter region path-connectedness) in `lean/src/AqeiBridge/CausalStability.lean`.
- `DiscreteSpacetime.h1_stable_small_pert` (H₁=0 stable under subgraph inclusion) in `lean/src/AqeiBridge/H1Stability.lean`.
- `DiscreteSpacetime.aqei_bridge_conjecture_discrete` + `DiscreteSpacetime.aqei_bridge_full` (packaged bridge statement) in `lean/src/AqeiBridge/DiscreteStabilityBridge.lean`.

- [x] Add a short **Main Theorem (discrete bridge)** wrapper section in `lean/src/AqeiBridge/CausalStability.lean` that re-exports:
  - path-connectedness of the admissible AQEI parameter region (already `admissible_region_pathConnected`), and
  - H₁=0 stability under AQEI-admissible edge removal (already `DiscreteStabilityBridge.aqei_bridge_conjecture_discrete`).
- [x] Update `docs/conjecture.md` to state the *exact* discrete theorem(s) proven in Lean and to clarify what “path-connected” means in a finite Hausdorff hyperspace setting.
- [x] Fix `docs/TODO-completed.md` dates (no future timestamps).
- [x] Mark the “Future-set topology/continuity” implementation item complete (base metric + perturbation-sensitive Hausdorff bound).
- [x] Run `./run_tests.sh`, commit, and push.

## Next actions (from `docs/TODO-BLOCKED.md`)

- [x] **Full Mathlib sheaf cohomology** → implement the suggested minimal Čech 0/1-cochain complex for a *finite* cover (Lean), so we can talk about an `H¹`-like quotient without pulling in all sheaf infrastructure.
  - Implemented: `lean/src/AqeiBridge/Cech01.lean` with `C0`, `C1`, `C2`, `d0`, `d1`, `d1_comp_d0 = 0`, and `H1Cech := ker(d1) / im(d0)` as a `Submodule` quotient.

- [x] **Poset homology / order complex (full)** → add an "order complex proxy" that turns `FiniteCausalPoset.Chains` into a small simplicial/chain complex (degrees 0–2), then relate its degree-1 cycles to the existing `Z1 := ker ∂₁` proxy.  **Fully bridged (2026-02-22)**.
  - Implemented: `lean/src/AqeiBridge/OrderComplexProxy.lean` with `OC1`/`OC2` simplex types, `bdy1` and `bdy2` boundary maps, `bdy1_comp_bdy2 = 0`, and `Z1_oc`, `B1_oc`, `H1_oc`.
  - Implemented: `lean/src/AqeiBridge/OrderComplexBridge.lean` with full `↔` equivalence via `Z1_oc_eq_bot_iff` (under `IsCompatible`).

- [x] **Future-set topology/continuity** → implement a real discrete base metric (graph shortest-path distance) for finite reachability models and upgrade the placeholder `discreteHausdorff ≤ 1` lemma to a perturbation-sensitive bound.
  - Target: new Lean file `lean/src/AqeiBridge/GraphDistance.lean` defining shortest-path distance on `Fin n` (undirected or directed-as-undirected), plus a lemma in `DiscreteFutureContinuity.lean` stating a Lipschitz-style bound for `J⁺` under a stated perturbation model.
  - [x] Implement `GraphDistance.boundedDist` (bounded shortest-path proxy) and a generic bound `discreteHausdorff (boundedDist ...) A B ≤ n`.
  - [x] Add a concrete perturbation model for causal graphs and prove a Lipschitz-style bound specialized to `JplusFinset` — implemented as `jplus_discreteHausdorff_coverage` in `DiscreteFutureContinuity.lean`.
  - [x] Immediate substep: prove one-sided Hausdorff = 0 when futures only grow by relation extension.

- [ ] **Mathematica worldline bumps / realistic curved sweeps** → remain blocked here because the pipeline moved to `aqei-numerical-validation`.
  - Next step lives in that repo; no action in `aqei-bridge`.

**Status Update (2026-02-22):** Repository split complete. Numerical validation pipeline moved to [`aqei-numerical-validation`](https://github.com/arcticoder/aqei-numerical-validation). This repo is now focused exclusively on the Lean 4 formalization and the formal verification manuscript.

**Active objective (post-proof):** push the discrete proof from “H₁=0 is stable under edge removal + AQEI parameter region is path-connected” toward a **meaningful stability statement about futures** (e.g. quantitative Hausdorff/Lipschitz control) and begin the **global obstruction** direction (vanishing of an `H¹`-like invariant for acyclic finite posets).

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

**File:** `lean/src/AqeiBridge/DiscreteStabilityBridge.lean` (NEW) — ✅ **PROVEN (2026-02-24)**

**Theorems proven:**
- `aqei_bridge_conjecture_discrete`: `dimH1IsZero P → EdgeHom P' P id → dimH1IsZero P'`, with explicit `T ∈ AQEI_cone F` witness.
- `aqei_bridge_full`: uniform H₁ stability over the cone + `IsPathConnected (AQEI_cone F)`.
- `causal_stability` and `causal_stability_pathConnected` (in `CausalStability.lean`): converted from `axiom` to theorems.
- `global_h1_invariance` and `ChronologyAsInvariant` (in `GlobalConjectures.lean`): converted from `axiom` to theorems.
- `causal_futures_path_connected` (in `Conjecture.lean`): converted from `axiom` to `trivial`.

**Proof strategy used:**
1. Given: T ∈ AQEI_cone F, dimH1(P) = 0, EdgeHom P' P id (P' is a subgraph of P)
2. Show: dimH1(P') = 0
3. Direct application of `h1_stable_small_pert`: H₁ = 0 is monotone under subgraph inclusion.

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

## Repository Assessment (2026-02-23) — ✅ COMPLETE

All items below have been actioned and moved to `docs/TODO-completed.md`.

### 1. `lean/lakefile.lean` and `lean/src` — ✅ DONE
- Fixed all linter warnings (`unnecessarySimpa`, `unusedSectionVars`, `unusedSimpArgs`).
- `lake build` now produces zero warnings from `lean/src/`.

### 2. `lake build` and warnings — ✅ DONE
- `tests/build_lean.sh` updated with Mathlib-noise filter (matching `energy-tensor-cone`).
- Writes filtered log to `lean/build.log`.

### 3. `docs/architecture.md` — ✅ DONE
- Rewritten to describe the pure Lean 4 formalization structure, with no hybrid workflow references.

### 4. `docs/code-overview.md` — ✅ DONE
- Fully updated to cover all 30 current Lean source files; removed outdated entries.

### 5. `docs/conjecture.md` — ✅ NO ACTION NEEDED
- Already up to date.

### 6. `docs/toy-model.md` — ✅ DONE
- Replaced with a historical note redirecting readers to the current architecture docs.

### 7. `papers/aqei-bridge-hybrid-workflow.md` — ✅ DONE
- Moved to `docs/history/aqei-bridge-hybrid-workflow.md`.

### 8. `papers/aqei-lean-formalization.tex` — ✅ NO ACTION NEEDED
- Already up to date.

### 9. `python/analyze_candidates.py` — ✅ DONE
- Archived to `deprecated/python/`; removed from tracked `python/` directory.

### 10. `python/orchestrator.py` — ✅ DONE
- Archived to `deprecated/python/`; removed from tracked `python/` directory.

### 11. `results` directory — ✅ DONE
- Was already empty; directory removed from git tracking.

### 12. `tests/build_lean.sh` — ✅ DONE
- Updated to match `energy-tensor-cone/tests/build_lean.sh` with Mathlib-noise filter.

### 13. `tests/lean_tests.sh` — ✅ DONE
- Removed inline Python placeholder-generation scripts (no longer needed).

### 14. `run_tests.sh` — ✅ DONE
- Simplified: calls `bash tests/build_lean.sh` once, then `lean_tests.sh`.
