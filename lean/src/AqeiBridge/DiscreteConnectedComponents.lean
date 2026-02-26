import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Card

import AqeiBridge.DiscreteCausalPoset

/-!
# Connected components of a discrete spacetime

This file defines the underlying undirected graph of a `DiscreteSpacetime` and
provides infrastructure to count connected components.

## Main definitions

- `undirGraph M : SimpleGraph Pt` — symmetrize the directed edge relation and
  drop self-loops, giving the underlying undirected simple graph.
- `numComponents M : ℕ` — the number of connected components of `undirGraph M`.

## Main results

- `undirGraph_adj` — adjacency characterization of `undirGraph`.
- `undirGraph_mono` — `EdgeHom M₁ M₂ id → undirGraph M₁ ≤ undirGraph M₂`.
- `numComponents_antitone` — subgraph inclusion increases component count:
  `EdgeHom M₁ M₂ id → numComponents M₂ ≤ numComponents M₁`.
-/

namespace AqeiBridge

namespace DiscreteSpacetime

section ConnectedComponents

variable {Pt : Type} [DecidableEq Pt] [Fintype Pt]

/-- The underlying undirected simple graph of a `DiscreteSpacetime`:
symmetrize the directed edge relation and enforce irreflexivity.

`(undirGraph M).Adj u v ↔ u ≠ v ∧ (M.edge u v ∨ M.edge v u)`. -/
def undirGraph (M : DiscreteSpacetime Pt) : SimpleGraph Pt :=
  SimpleGraph.fromRel M.edge

set_option linter.unusedSectionVars false in
@[simp]
theorem undirGraph_adj {M : DiscreteSpacetime Pt} (u v : Pt) :
    (undirGraph M).Adj u v ↔ u ≠ v ∧ (M.edge u v ∨ M.edge v u) :=
  SimpleGraph.fromRel_adj M.edge u v

/-- `undirGraph` is monotone under subgraph inclusion: adding directed edges
only merges (or preserves) undirected connected components. -/
theorem undirGraph_mono {M₁ M₂ : DiscreteSpacetime Pt}
    (h : EdgeHom M₁ M₂ (id : Pt → Pt)) :
    undirGraph M₁ ≤ undirGraph M₂ := by
  intro u v hadj
  simp only [undirGraph_adj] at *
  refine ⟨hadj.1, ?_⟩
  rcases hadj.2 with hpq | hqp
  · exact Or.inl (h hpq)
  · exact Or.inr (h hqp)

variable (M : DiscreteSpacetime Pt) [DecidableRel M.edge]

/-- Decidable adjacency for `undirGraph M`, derived from `DecidableEq Pt` and
`DecidableRel M.edge`. -/
instance instDecidableRelUndirAdj : DecidableRel (undirGraph M).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel M.edge).Adj)

/-- The number of connected components of the underlying undirected graph
`undirGraph M`.

Requires `[Fintype Pt]`, `[DecidableEq Pt]`, and `[DecidableRel M.edge]` to
compute the quotient. -/
noncomputable def numComponents : ℕ :=
  Fintype.card (undirGraph M).ConnectedComponent

end ConnectedComponents

/-- **Subgraph inclusion is antitone for connected-component count.**

Adding causal edges can only merge components (or preserve them), so a
subgraph `M₁ ⊆ M₂` always has at least as many connected components:
`numComponents M₂ ≤ numComponents M₁`.

The proof uses the surjection
  `G₁.ConnectedComponent → G₂.ConnectedComponent` (for `G₁ ≤ G₂`)
provided by `SimpleGraph.ConnectedComponent.surjective_map_ofLE`. -/
theorem numComponents_antitone {Pt : Type} [DecidableEq Pt] [Fintype Pt]
    {M₁ M₂ : DiscreteSpacetime Pt}
    [DecidableRel M₁.edge] [DecidableRel M₂.edge]
    (h : EdgeHom M₁ M₂ (id : Pt → Pt)) :
    numComponents M₂ ≤ numComponents M₁ :=
  Fintype.card_le_of_surjective _
    (SimpleGraph.ConnectedComponent.surjective_map_ofLE (undirGraph_mono h))

end DiscreteSpacetime

end AqeiBridge
