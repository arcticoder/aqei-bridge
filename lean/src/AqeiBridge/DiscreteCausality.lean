import Std
import Mathlib.Data.Set.Basic

/-!
# Discrete causality model (formalizable toy)

This file provides a *fully formal* discrete model of causal reachability.

It is intended as a bridge step:
- we can prove stability/path-connectedness facts **in this discrete setting**,
- then later replace the discrete reachability relation with a real Lorentzian
  definition.

Nothing here assumes any PDE physics.
-/

namespace AqeiBridge

/-- A discrete spacetime structure on a fixed type of points `Pt`.

`edge p q` means there is a future-directed causal step from `p` to `q`.
-/
structure DiscreteSpacetime (Pt : Type) where
  edge : Pt → Pt → Prop

/-- Reachability is the transitive closure of the edge relation. -/
def Reachable {Pt : Type} (M : DiscreteSpacetime Pt) (p q : Pt) : Prop :=
  Relation.TransGen M.edge p q

/-- Causal future set `J⁺(p)` in the discrete model. -/
def JplusDiscrete {Pt : Type} (M : DiscreteSpacetime Pt) (p : Pt) : Set Pt := {q | Reachable M p q}

/-- If we add edges (monotone extension), reachability can only increase. -/
def EdgeExtension {Pt : Type} (M₁ M₂ : DiscreteSpacetime Pt) : Prop :=
  ∀ p q, M₁.edge p q → M₂.edge p q

theorem reachable_mono {Pt : Type} {M₁ M₂ : DiscreteSpacetime Pt} (h : EdgeExtension M₁ M₂) :
    ∀ {p q}, Reachable M₁ p q → Reachable M₂ p q := by
  intro p q hr
  induction hr with
  | single hpq =>
      exact Relation.TransGen.single (h _ _ hpq)
    | tail hpb hbq ih =>
      exact Relation.TransGen.tail ih (h _ _ hbq)

theorem jplus_mono {Pt : Type} {M₁ M₂ : DiscreteSpacetime Pt} (h : EdgeExtension M₁ M₂) (p : Pt) :
  JplusDiscrete M₁ p ⊆ JplusDiscrete M₂ p := by
  intro q hq
  exact reachable_mono h hq

end AqeiBridge
