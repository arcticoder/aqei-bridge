# Conjecture: Causal Stability Under AQEI-Admissible Perturbations

This document separates three kinds of statement clearly:
1. **Proven in Lean** — machine-checked, zero `sorry`.
2. **Quantitative current strength** — exact bound value and proof status.
3. **Conjectural / open** — not formalized; aspirational direction.

---

## A. Proven Discrete Bridge (Lean-formalized)

### A.1 Discrete Bridge Theorem

> **Lean name:** `DiscreteSpacetime.h1_stable_small_pert`
> **File:** `lean/src/AqeiBridge/H1Stability.lean`

**Statement:**  
Let `P` be a finite causal poset.  
If `Z₁(P, ℤ) = ⊥` and `P'` is a subgraph of `P`
(i.e. there exists `EdgeHom P' P id` — identity on vertices, subset on edges),  
then `Z₁(P', ℤ) = ⊥`.

**Mathematical form:**
$$
Z_1(P;\mathbb{Z}) = 0 \;\land\; P' \subseteq P \;\Longrightarrow\; Z_1(P';\mathbb{Z}) = 0
$$

**Mechanism:**  
The pushforward chain map
$$
\mathrm{push}_1 : C_1(P') \to C_1(P)
$$
is injective (proved as `push1_injective` using injectivity of `id` on vertices).
Any 1-cycle in $P'$ pushes to a 1-cycle in $P$; since $Z_1(P) = \bot$, that push
is zero; by injectivity the original cycle is zero.

**Key lemmas used:** `push1_apply_mapEdge`, `push1_injective`, `Z1_eq_bot_of_subgraph`.

**Note on "ε-perturbation":** In this formalization, "edge perturbation" = subgraph
inclusion. Any subset of edges (regardless of magnitude) is covered by the theorem
because the proof uses only the inclusion structure, not any metric bound.

### A.1b Monotonicity of Z₁ (Stronger Form)

The proof mechanism actually establishes the stronger inclusion:
$$
Z_1(P';\mathbb{Z}) \subseteq Z_1(P;\mathbb{Z})
$$
under subgraph inclusion $P' \subseteq P$, via injectivity of $\mathrm{push}_1$.
Zero-preservation (A.1) is then the special case
$Z_1(P) = 0 \Rightarrow Z_1(P') = 0$.

This stronger form is the direct reason C.2 (dimension inequality) is a natural next target.

---

### A.2 Path-Connected Admissible Region

> **Lean name:** `admissible_region_pathConnected`
> **File:** `lean/src/AqeiBridge/CausalStability.lean`

**Statement:**  
Let `F` be a finite family of AQEI linear functionals.  
If the polyhedron
$$
\mathrm{AQEI\_cone}(F) = \bigl\{\, T \mid \forall f \in F,\; f(T) \ge 0 \,\bigr\}
$$
is **nonempty**, then it is **path-connected**.

**Mechanism:** AQEI cone is convex (proved as `aqei_cone_convex` via halfspace
intersection). A nonempty convex subset of $\mathbb{R}^n$ is path-connected via
`Convex.isPathConnected` from Mathlib.

---

### A.3 Packaged Bridge Statement

> **Lean name:** `DiscreteSpacetime.aqei_bridge_conjecture_discrete`
> **File:** `lean/src/AqeiBridge/DiscreteStabilityBridge.lean`

Packages A.1 with an explicit AQEI cone witness, providing the combined statement
that a discrete causal graph inside an AQEI-admissible parameter region has stable
acyclicity under subgraph perturbations.

---

### A.4 Order-Complex Equivalence

> **Lean name:** `Z1_oc_eq_bot_iff`
> **File:** `lean/src/AqeiBridge/OrderComplexBridge.lean`

**Statement (bidirectional):** For compatible posets,
$$
Z_1^{\mathrm{oc}}(R,P) = \bot \;\iff\; Z_1(P.\mathrm{toCausalPoset}, R) = \bot.
$$

This bridges the order-complex simplicial approach to the chain-complex kernel
approach, confirming both proxies capture the same acyclicity invariant.

---

## B. Quantitative Future Stability (Current Strength)

### B.1 Coverage Bound (Proven)

> **Lean name:** `jplus_discreteHausdorff_coverage`
> **File:** `lean/src/AqeiBridge/DiscreteFutureContinuity.lean`

**Statement (informal):** For finite causal posets `P` and `Q` on `Fin n`,
under pointwise matching hypotheses,
$$
d_H\bigl(J^+(P,p),\; J^+(Q,p)\bigr) \le n
$$
where $d_H$ is the discrete Hausdorff distance under the bounded shortest-path
metric `boundedDist`.

This uses `GraphDistance.lean` (bounded shortest-path proxy on `Fin n`) and
`DiscreteHausdorff.lean` (Hausdorff distance for `Finset`).

**Remark (non-sharp bound).** Since `boundedDist` takes values in `{0, …, n}`,
the bound $\le n$ is a global coverage lemma and is not sharp.
It reflects the diameter of the metric space, not the sensitivity of $J^+$ to
edge changes. The single-edge bound in §B.2 is the intended quantitative strengthening.

### B.2 Tight Single-Edge Bound (Target — Not Yet Proven)

> **Target Lean name:** `jplus_hausdorff_le_one_of_edge_diff`
> **Target file:** `lean/src/AqeiBridge/DiscreteFutureContinuity.lean`

**Goal:**  
If adjacency matrices `P.adj` and `Q.adj` differ on exactly one edge $(u,v)$,
then for all $p$:
$$
d_H\bigl(J^+(P,p),\; J^+(Q,p)\bigr) \le 1.
$$

**Perturbation model:**
$$
|\mathrm{adj}_P - \mathrm{adj}_Q| = 1.
$$

This is the tight Lipschitz upgrade over the coverage bound in B.1. Currently open.

---

## C. Conjectural / Open Directions

### C.1 Continuous AQEI Bridge (Conjectural)

**Goal:** Replace subgraph inclusion by convex perturbations in parameter space
$T \in \mathrm{AQEI\_cone}(F)$, and prove that $H^1$-like invariants are stable
under admissible perturbations in a Lorentzian continuum setting.

This requires:
- a topology on the hyperspace of subsets of $M$ (or a suitable discretization thereof),
- a proof that the map $T \mapsto J^+_T(p)$ is continuous in that topology,
- and a discretization theorem relating $P_T$ to $J^+_T$ formally.

**Status:** Entirely open. The discrete theorems in §A provide combinatorial
scaffolding but do not imply this.

### C.2 Dimension Inequality Under Subgraph Inclusion (Target)

**Goal:**
$$
\dim H_1(P') \le \dim H_1(P) \quad \text{under } P' \subseteq P.
$$

In graph terms: $|E'| - |V| + c(G') \le |E| - |V| + c(G)$.

This would make stability quantitative (not just zero-preservation). Not yet
formalized; follows naturally from A.1 as a strengthening.

### C.3 Acyclicity ↔ Vanishing H¹_oc (Target)

**Goal:**  
$$
\text{acyclic}(P) \;\iff\; H_1^{\mathrm{oc}}(P) = 0.
$$

The direction $\Rightarrow$ is morally in `OrderComplexBridge.lean` via `Z1_oc_eq_bot_iff`
together with A.1, but an explicit acyclicity definition and the $\Leftarrow$ direction
remain to be formalized in `OrderComplexProxy.lean`.

### C.4 Chamber Constancy → Global Constancy (Target)

**Goal:**  
If a map $\Phi : \mathrm{AQEI\_cone}(F) \to \alpha$ satisfies
$$
\Phi|_{C_i} = \text{constant} \quad \text{for each polyhedral chamber } C_i,
$$
and the cone is nonempty (hence path-connected by A.2), then $\Phi$ is globally
constant on the cone.

This provides a bridge tool for lifting discrete chamber stability to
continuous parameter independence.

**Target Lean lemma:**
```lean
theorem chamber_constancy_global
  (C : Set V) (hconv : Convex ℝ C) (hne : C.Nonempty)
  (Φ : V → α)
  (hch : ∀ i, IsChamber i → ∀ T₁ T₂ ∈ i, Φ T₁ = Φ T₂)
  : ∀ T₁ T₂ ∈ C, Φ T₁ = Φ T₂
```

---

## Three Formal Pillars

All work in this library reduces to one of three structural roles:

1. **Convex polyhedral geometry** — AQEI cone is $\bigcap_i \{L_i(T) \ge 0\}$;
   convexity + nonemptiness $\Rightarrow$ path-connectedness.

2. **Functorial homology** — $Z_1 = \ker \partial_1$;
   pushforward $C_1(P') \to C_1(P)$ injective $\Rightarrow$ $Z_1(P') \subseteq Z_1(P)$;
   $H_1(g \circ f) = H_1(f) \circ H_1(g)$.

3. **Metric stability of futures** — $d_H(J^+_P, J^+_Q) \le k$ under $k$-edge
   perturbation.

If a TODO item does not strengthen one of those three pillars, it belongs
in a different repo.
