import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.SetTheory.Cardinal.Basic

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

## Status

- `rank_Z1_formula` **[sorry]**: the rank formula for `Z₁`. Proved by
  rank-nullity applied to `boundary1 M ℤ`:
  1. `rank C₁ = numDirEdges M` (free module on directed edges).
  2. `rank (ker ∂₁) + rank (im ∂₁) = rank C₁` (rank-nullity over ℤ).
  3. `rank (im ∂₁) = Fintype.card Pt - numComponents M` — the image of the
     incidence matrix has rank `|V| - c(G)`, proved using a spanning forest
     of the underlying undirected graph.

- `h1_quantitative_upgrade` **[sorry-free given rank_Z1_formula]**: derives the
  combinatorial inequality from `rank_Z1_formula` and A.2.
-/

namespace AqeiBridge

namespace DiscreteSpacetime

section H1QuantitativeUpgrade

variable {Pt : Type} [DecidableEq Pt] [Fintype Pt]

/-- Count of directed edges in `M` (as a `ℕ`).

We count elements of the subtype `{e : Pt × Pt // M.edge e.1 e.2}`, which is
finite when `[Fintype Pt]` and `[DecidableRel M.edge]`. -/
noncomputable def numDirEdges (M : DiscreteSpacetime Pt) [DecidableRel M.edge] : ℕ :=
  Fintype.card {e : Pt × Pt // M.edge e.1 e.2}

/-!
## The rank formula (sorry)
-/

/-- **Betti number formula for directed graphs** [sorry].

The dimension of the cycle space `Z₁(M)` satisfies the Euler-characteristic
formula over ℤ:
```
Module.rank ℤ ↥(Z1 M) + Fintype.card Pt = numDirEdges M + numComponents M
```
(equivalently, `dim Z₁ = |E| - |V| + c` with natural-number subtraction avoided).

**Proof sketch** (not yet formalized):
1. Rank-nullity for `boundary1 M ℤ : (Edge M →₀ ℤ) →ₗ[ℤ] (Pt →₀ ℤ)`:
   ```
   rank (ker ∂₁) + rank (im ∂₁) = rank (Edge M →₀ ℤ) = numDirEdges M
   ```
2. `rank (ker ∂₁) = rank Z₁(M)` by definition.
3. `rank (im ∂₁) = Fintype.card Pt - numComponents M`:
   - The image of the directed incidence matrix spans the same subspace as the
     undirected incidence matrix (both generate `{v_j - v_i : i~j in G}`).
   - By the spanning-forest argument, `rank (im ∂₁) = |V| - c(G_undir)`.

The missing formalization is step 3, which requires connecting the directed
boundary map to the Laplacian of `undirGraph M` and using the null-space
dimension formula `card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`
from `Mathlib.Combinatorics.SimpleGraph.LapMatrix`.  -/
theorem rank_Z1_formula (M : DiscreteSpacetime Pt) [DecidableRel M.edge] :
    Module.rank ℤ ↥(Z1 (M := M) (R := ℤ)) + (Fintype.card Pt : Cardinal) =
    (numDirEdges M : Cardinal) + (numComponents M : Cardinal) := by
  sorry

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
