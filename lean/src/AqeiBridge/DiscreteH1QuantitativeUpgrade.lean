import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.Span
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Combinatorics.SimpleGraph.Acyclic

import AqeiBridge.DiscreteConnectedComponents
import AqeiBridge.H1Stability

/-!
# Quantitative upgrade of the H₁ stability theorem (A.5)

This file upgrades the A.2 rank inequality
(`Module.rank ℤ ↥(Z1 M₁) ≤ Module.rank ℤ ↥(Z1 M₂)` under `M₁ ⊆ M₂`)
to an explicit combinatorial formula:
$$\dim Z_1(M) + |V| = |E(M)| + c(M)$$
where `|E(M)| = numDirEdges M` counts directed edges, `|V| = Fintype.card Pt`,
and `c(M) = numComponents M` counts connected components of the underlying
undirected graph.

Equivalently, the sum `|E(M)| + c(M)` is non-decreasing under edge addition.

## Proof structure

The proof proceeds in three main steps:

1. **Rank-nullity for `boundary1`** (`rank_Z1_add_rank_im_eq_numDirEdges`):
   `rank Z₁ + rank (im ∂₁) = numDirEdges M`
   Uses: `rank_finsupp_self'` + `LinearMap.rank_range_add_rank_ker`.

2. **Upper bound on image rank** (`rank_im_boundary1_add_numComponents_le`):
   `rank (im ∂₁) + numComponents M ≤ Fintype.card Pt`
   Uses: the "component map" `compMap := lmapDomain ℤ ℤ connectedComponentMk`
   is surjective, so by rank-nullity `rank (ker compMap) = |Pt| - c(M)`,
   and `im ∂₁ ≤ ker compMap` (boundary vectors cancel within components).

3. **Lower bound on image rank** (`rank_im_boundary1_add_numComponents_ge`):
   `rank (im ∂₁) + numComponents M ≥ Fintype.card Pt`
   Uses: a spanning forest of `undirGraph M` provides `|V| - c(M)` linearly
   independent boundary vectors, proved by leaf-removal induction on each
   spanning tree.
   **[sorry]**: this is the remaining open step.

## Status

- `rank_im_boundary1_add_numComponents_ge` **[sorry]**: spanning forest lower
  bound. All other lemmas are sorry-free.
- `rank_Z1_formula` **[sorry-free given the above]**: assembles from the three
  steps.
- `h1_quantitative_upgrade` **[sorry-free]**: derives the combinatorial
  inequality from `rank_Z1_formula` and A.2.
-/

namespace AqeiBridge

namespace DiscreteSpacetime

section H1QuantitativeUpgrade

-- Several private helper lemmas use only a subset of the section variables;
-- suppress the resulting lint warnings.
set_option linter.unusedSectionVars false

variable {Pt : Type} [DecidableEq Pt] [Fintype Pt]

/-- Count of directed edges in `M` (as a `ℕ`).

We count elements of the subtype `{e : Pt × Pt // M.edge e.1 e.2}`, which is
finite when `[Fintype Pt]` and `[DecidableRel M.edge]`. -/
noncomputable def numDirEdges (M : DiscreteSpacetime Pt) [DecidableRel M.edge] : ℕ :=
  Fintype.card {e : Pt × Pt // M.edge e.1 e.2}

/-!
## Helper: Edge ≃ subtype of pairs
-/

/-- The type `Edge M` of directed edges is in bijection with
`{e : Pt × Pt // M.edge e.1 e.2}`. -/
private def edgeEquiv (M : DiscreteSpacetime Pt) [DecidableRel M.edge] :
    Edge M ≃ {e : Pt × Pt // M.edge e.1 e.2} where
  toFun e := ⟨(e.src, e.dst), e.ok⟩
  invFun e := ⟨e.1.1, e.1.2, e.2⟩
  left_inv _ := rfl
  right_inv _ := by simp

/-- The ℤ-rank of the free module on edges equals `numDirEdges M`. -/
private lemma rank_C1_eq (M : DiscreteSpacetime Pt) [DecidableRel M.edge] :
    Module.rank ℤ (Edge M →₀ ℤ) = (numDirEdges M : Cardinal) := by
  rw [rank_finsupp_self']
  -- rank_finsupp_self' gives #(Edge M); rewrite via the equivalence to the subtype
  -- #(Edge M) = #{e : Pt×Pt // M.edge e.1 e.2}   (edgeEquiv M)
  -- #{e : Pt×Pt // M.edge e.1 e.2} = Fintype.card {e : Pt×Pt // M.edge e.1 e.2}
  --                                 = numDirEdges M
  rw [Cardinal.mk_congr (edgeEquiv M), Cardinal.mk_fintype, numDirEdges]

/-!
## Step 1: Rank-nullity for boundary1
-/

/-- **Step 1**: Rank-nullity for `∂₁`:
`rank Z₁ + rank (im ∂₁) = numDirEdges M`. -/
private lemma rank_Z1_add_rank_im_eq_numDirEdges
    (M : DiscreteSpacetime Pt) [DecidableRel M.edge] :
    Module.rank ℤ ↥(Z1 (M := M) (R := ℤ)) +
    Module.rank ℤ ↥(LinearMap.range (boundary1 (M := M) (R := ℤ))) =
    (numDirEdges M : Cardinal) := by
  -- rank_range_add_rank_ker : rank(range f) + rank(ker f) = rank(domain)
  -- So: rank(range ∂₁) + rank(ker ∂₁) = rank(Edge M →₀ ℤ) = numDirEdges M
  -- Z1 = ker ∂₁, so: rank(range ∂₁) + rank Z₁ = numDirEdges M
  -- Rearranging with add_comm: rank Z₁ + rank(range ∂₁) = numDirEdges M
  have h := LinearMap.rank_range_add_rank_ker (boundary1 (M := M) (R := ℤ))
  rw [rank_C1_eq M, add_comm] at h
  -- h now has ker on left: rank(ker ∂₁) + rank(range ∂₁) = numDirEdges M
  -- but ker boundary1 = Z1 definitionally
  exact h

/-!
## Step 2: The "component map" and its properties
-/

private noncomputable def compMap (M : DiscreteSpacetime Pt) [DecidableRel M.edge] :
    (Pt →₀ ℤ) →ₗ[ℤ] ((undirGraph M).ConnectedComponent →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (undirGraph M).connectedComponentMk

/-- `compMap` is surjective, since `connectedComponentMk` is surjective. -/
private lemma compMap_surjective (M : DiscreteSpacetime Pt) [DecidableRel M.edge] :
    Function.Surjective (compMap M) := by
  intro x
  simp only [compMap, Finsupp.coe_lmapDomain]
  exact Finsupp.mapDomain_surjective (Quot.mk_surjective) x

/-- The boundary of each directed edge maps to zero under `compMap`:
  `compMap (edgeBoundary e) = 0` for every `e : Edge M`. -/
private lemma compMap_edgeBoundary_eq_zero
    (M : DiscreteSpacetime Pt) [DecidableRel M.edge]
    (e : Edge M) :
    compMap M (edgeBoundary (M := M) (R := ℤ) e) = 0 := by
  simp only [compMap, edgeBoundary, map_sub, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  -- Need: connectedComponentMk e.dst = connectedComponentMk e.src
  -- because M.edge e.src e.dst → (undirGraph M).Adj e.src e.dst → Reachable
  -- Case split: if e.src = e.dst, edgeBoundary e = 0 and the goal holds trivially.
  -- Otherwise e.src ≠ e.dst, so undirGraph M has an edge, giving reachability.
  by_cases heq : e.src = e.dst
  · -- Self-loop: edgeBoundary collapses to zero
    simp [heq]
  · have hadj : (undirGraph M).Adj e.src e.dst := by
      rw [undirGraph_adj]
      exact ⟨heq, Or.inl e.ok⟩
    have hreach : (undirGraph M).Reachable e.src e.dst := hadj.reachable
    have hcomp : (undirGraph M).connectedComponentMk e.src =
                 (undirGraph M).connectedComponentMk e.dst :=
      SimpleGraph.ConnectedComponent.sound hreach
    simp [hcomp]

/-- The image of `boundary1` is contained in the kernel of `compMap`. -/
private lemma im_boundary1_le_ker_compMap
    (M : DiscreteSpacetime Pt) [DecidableRel M.edge] :
    LinearMap.range (boundary1 (M := M) (R := ℤ)) ≤
    LinearMap.ker (compMap M) := by
  rintro x ⟨y, rfl⟩
  simp only [LinearMap.mem_ker]
  induction y using Finsupp.induction_linear with
  | zero => simp
  | single e r =>
      simp only [boundary1_single, map_smul]
      rw [compMap_edgeBoundary_eq_zero]
      simp
  | add f g hf hg =>
      simp only [map_add, hf, hg, add_zero]

/-!
## Step 3: Upper bound on image rank
-/

/-- **Step 3 (upper bound)**:
`rank (im ∂₁) + numComponents M ≤ Fintype.card Pt`. -/
private lemma rank_im_boundary1_add_numComponents_le
    (M : DiscreteSpacetime Pt) [DecidableRel M.edge] :
    Module.rank ℤ ↥(LinearMap.range (boundary1 (M := M) (R := ℤ))) +
    (numComponents M : Cardinal) ≤
    (Fintype.card Pt : Cardinal) := by
  -- rank-nullity for compMap (surjective):
  -- rank (ker compMap) + rank (im compMap) = rank (Pt →₀ ℤ)
  -- = |Pt|, and rank (im compMap) = numComponents M (since compMap is surjective)
  have hC0 : Module.rank ℤ (Pt →₀ ℤ) = (Fintype.card Pt : Cardinal) := by
    rw [rank_finsupp_self', Cardinal.mk_fintype]
  have hCC : Module.rank ℤ ((undirGraph M).ConnectedComponent →₀ ℤ) =
             (numComponents M : Cardinal) := by
    rw [rank_finsupp_self', Cardinal.mk_fintype]
    simp [numComponents]
  -- rank-nullity: rank(Pt →₀ ℤ) = rank(CC →₀ ℤ) + rank(ker compMap)
  have hrn : Module.rank ℤ (Pt →₀ ℤ) =
             Module.rank ℤ ((undirGraph M).ConnectedComponent →₀ ℤ) +
             Module.rank ℤ ↥(LinearMap.ker (compMap M)) :=
    LinearMap.rank_eq_of_surjective (compMap_surjective M)
  -- State: rank(Pt →₀ ℤ) = numComponents M + rank(ker compMap)
  -- i.e.  |Pt| = numComponents M + rank(ker compMap)
  have hrank_sum : (Fintype.card Pt : Cardinal) =
      (numComponents M : Cardinal) + Module.rank ℤ ↥(LinearMap.ker (compMap M)) := by
    rw [← hC0, hrn, hCC]
  -- im(∂₁) ≤ ker(compMap), so rank(im ∂₁) ≤ rank(ker compMap)
  have hle : Module.rank ℤ ↥(LinearMap.range (boundary1 (M := M) (R := ℤ))) ≤
             Module.rank ℤ ↥(LinearMap.ker (compMap M)) :=
    Submodule.rank_mono (im_boundary1_le_ker_compMap M)
  -- Combine: rank(im ∂₁) + numComponents ≤ rank(ker) + numComponents = |Pt|
  calc Module.rank ℤ ↥(LinearMap.range (boundary1 (M := M) (R := ℤ))) +
           (numComponents M : Cardinal)
      ≤ Module.rank ℤ ↥(LinearMap.ker (compMap M)) + (numComponents M : Cardinal) := by
        gcongr
    _ = (numComponents M : Cardinal) + Module.rank ℤ ↥(LinearMap.ker (compMap M)) := by
        ring
    _ = (Fintype.card Pt : Cardinal) := hrank_sum.symm

/-!
## Step 4: Lower bound on image rank (spanning forest)
-/

/-- **Step 4 (lower bound)** [sorry]:
`rank (im ∂₁) + numComponents M ≥ Fintype.card Pt`.

**Proof sketch**: A maximal acyclic subgraph (spanning forest) `F ≤ undirGraph M`
has the same connected components as `undirGraph M`, and its edges can be
oriented using the original directed edges.  The `|V| - c(M)` resulting
boundary vectors are linearly independent (by leaf-removal induction on each
spanning tree component), so `rank (im ∂₁) ≥ |V| - c(M)`. -/
private lemma rank_im_boundary1_add_numComponents_ge
    (M : DiscreteSpacetime Pt) [DecidableRel M.edge] :
    (Fintype.card Pt : Cardinal) ≤
    Module.rank ℤ ↥(LinearMap.range (boundary1 (M := M) (R := ℤ))) +
    (numComponents M : Cardinal) := by
  sorry

/-!
## Step 5: Assembly — the rank formula
-/

/-- The ℤ-rank of the image of `boundary1` satisfies
`rank (im ∂₁) + numComponents M = Fintype.card Pt`. -/
private lemma rank_im_add_numComponents_eq
    (M : DiscreteSpacetime Pt) [DecidableRel M.edge] :
    Module.rank ℤ ↥(LinearMap.range (boundary1 (M := M) (R := ℤ))) +
    (numComponents M : Cardinal) =
    (Fintype.card Pt : Cardinal) :=
  le_antisymm
    (rank_im_boundary1_add_numComponents_le M)
    (rank_im_boundary1_add_numComponents_ge M)

/-!
## The rank formula
-/

/-- **Betti number formula for directed graphs**.

The dimension of the cycle space `Z₁(M)` satisfies the Euler-characteristic
formula over ℤ:
```
Module.rank ℤ ↥(Z1 M) + Fintype.card Pt = numDirEdges M + numComponents M
```
(equivalently, `dim Z₁ = |E| - |V| + c` with natural-number subtraction avoided).

**Proof**: Assembles steps 1–5:
1. Rank-nullity: `rank Z₁ + rank (im ∂₁) = numDirEdges M`
   (`rank_Z1_add_rank_im_eq_numDirEdges`).
2. Image rank formula: `rank (im ∂₁) + numComponents M = |Pt|`
   (`rank_im_add_numComponents_eq`, using upper bound via `compMap` and lower
   bound via spanning forest [**sorry**]).
3. Add the two equations to get the result. -/
theorem rank_Z1_formula (M : DiscreteSpacetime Pt) [DecidableRel M.edge] :
    Module.rank ℤ ↥(Z1 (M := M) (R := ℤ)) + (Fintype.card Pt : Cardinal) =
    (numDirEdges M : Cardinal) + (numComponents M : Cardinal) := by
  -- h1 : rank Z₁ + rank(im ∂₁) = numDirEdges M
  -- h2 : rank(im ∂₁) + numComponents M = |Pt|
  -- Goal: rank Z₁ + |Pt| = numDirEdges M + numComponents M
  -- Proof: rank Z₁ + |Pt|
  --   = rank Z₁ + (rank(im ∂₁) + numComponents M)   [by h2]
  --   = (rank Z₁ + rank(im ∂₁)) + numComponents M   [add_assoc]
  --   = numDirEdges M + numComponents M              [by h1]
  have h1 := rank_Z1_add_rank_im_eq_numDirEdges M
  have h2 := rank_im_add_numComponents_eq M
  -- Cardinals don't support linarith; use explicit equational reasoning
  calc Module.rank ℤ ↥(Z1 (M := M) (R := ℤ)) + (Fintype.card Pt : Cardinal)
      = Module.rank ℤ ↥(Z1 (M := M) (R := ℤ)) +
        (Module.rank ℤ ↥(LinearMap.range (boundary1 (M := M) (R := ℤ))) +
         (numComponents M : Cardinal)) := by rw [h2]
    _ = (Module.rank ℤ ↥(Z1 (M := M) (R := ℤ)) +
         Module.rank ℤ ↥(LinearMap.range (boundary1 (M := M) (R := ℤ)))) +
        (numComponents M : Cardinal) := by ring
    _ = (numDirEdges M : Cardinal) + (numComponents M : Cardinal) := by rw [h1]

/-!
## The quantitative upgrade (A.5)
-/

/-- **A.5 — Quantitative H₁ upgrade.**

Under subgraph inclusion `M₁ ⊆ M₂` (`EdgeHom M₁ M₂ id`), the combined
invariant `numDirEdges M + numComponents M` is non-decreasing:
```
numDirEdges M₁ + numComponents M₁ ≤ numDirEdges M₂ + numComponents M₂
```

This is the quantitative form of the backlog item
`|E'| - |V| + c(G') ≤ |E| - |V| + c(G)` (equivalent after cancelling `|V|`).

**Proof** (given `rank_Z1_formula` and A.2 `h1_dim_le_of_subgraph`):
```
numDirEdges M₁ + c(M₁)
  = rank Z₁(M₁) + |V|   (rank formula)
  ≤ rank Z₁(M₂) + |V|   (A.2: rank is monotone)
  = numDirEdges M₂ + c(M₂).  (rank formula)
```
-/
theorem h1_quantitative_upgrade
    {M₁ M₂ : DiscreteSpacetime Pt}
    [DecidableRel M₁.edge] [DecidableRel M₂.edge]
    (h : EdgeHom M₁ M₂ (id : Pt → Pt)) :
    numDirEdges M₁ + numComponents M₁ ≤ numDirEdges M₂ + numComponents M₂ := by
  -- A.2: rank Z₁(M₁) ≤ rank Z₁(M₂)
  have hrank : Module.rank ℤ ↥(Z1 (M := M₁) (R := ℤ)) ≤
               Module.rank ℤ ↥(Z1 (M := M₂) (R := ℤ)) :=
    h1_dim_le_of_subgraph h
  -- Cardinal inequality via the rank formula
  have hle : (numDirEdges M₁ : Cardinal) + numComponents M₁ ≤
             (numDirEdges M₂ : Cardinal) + numComponents M₂ :=
    calc (numDirEdges M₁ : Cardinal) + numComponents M₁
        = Module.rank ℤ ↥(Z1 (M := M₁) (R := ℤ)) + Fintype.card Pt :=
            (rank_Z1_formula M₁).symm
      _ ≤ Module.rank ℤ ↥(Z1 (M := M₂) (R := ℤ)) + Fintype.card Pt := by
            gcongr
      _ = numDirEdges M₂ + numComponents M₂ := rank_Z1_formula M₂
  -- Cast back to ℕ
  exact_mod_cast hle

end H1QuantitativeUpgrade

end DiscreteSpacetime

end AqeiBridge
