import Std

import AqeiBridge.CausalPoset
import AqeiBridge.CausalContinuity
import AqeiBridge.DiscreteCausality

/-!
# Discrete causal graphs as causal posets (toy bridge)

This file packages a `DiscreteSpacetime` (directed graph) into a `CausalPoset`
by taking the preorder to be reflexive-transitive reachability.

It also provides a small continuity lemma:
- a graph homomorphism (edge-respecting map) induces a continuous map between
  Alexandrov topologies.
-/

namespace AqeiBridge

namespace DiscreteSpacetime

/-- Reflexive-transitive reachability (includes the identity). -/
def ReachableRefl {Pt : Type} (M : DiscreteSpacetime Pt) (p q : Pt) : Prop :=
  Relation.ReflTransGen M.edge p q

/-- `ReachableRefl` makes a discrete spacetime into a `CausalPoset`. -/
def toCausalPoset {Pt : Type} (M : DiscreteSpacetime Pt) : CausalPoset where
  Pt := Pt
  le := ReachableRefl M
  refl := by
    intro p
    exact Relation.ReflTransGen.refl
  trans := by
    intro p q r hpq hqr
    exact Relation.ReflTransGen.trans hpq hqr

/-- A map is an edge-homomorphism if it preserves edges. -/
def EdgeHom {Pt₁ Pt₂ : Type} (M₁ : DiscreteSpacetime Pt₁) (M₂ : DiscreteSpacetime Pt₂)
    (f : Pt₁ → Pt₂) : Prop :=
  ∀ ⦃p q⦄, M₁.edge p q → M₂.edge (f p) (f q)

/-- An edge-homomorphism is order-respecting on reflexive reachability. -/
theorem le_monotone_of_edgeHom {Pt₁ Pt₂ : Type}
    {M₁ : DiscreteSpacetime Pt₁} {M₂ : DiscreteSpacetime Pt₂} {f : Pt₁ → Pt₂}
    (hf : EdgeHom M₁ M₂ f) :
    ∀ ⦃a b⦄, (toCausalPoset M₁).le a b → (toCausalPoset M₂).le (f a) (f b) := by
  intro a b hab
  -- Here `hab` is `ReachableRefl M₁ a b` by definition.
  induction hab with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hab hEdge ih =>
      exact Relation.ReflTransGen.tail ih (hf hEdge)

/-- Edge-homomorphisms are continuous for the induced Alexandrov topologies. -/
theorem continuous_of_edgeHom {Pt₁ Pt₂ : Type}
    {M₁ : DiscreteSpacetime Pt₁} {M₂ : DiscreteSpacetime Pt₂} {f : Pt₁ → Pt₂}
    (hf : EdgeHom M₁ M₂ f) :
    @Continuous _ _
      (CausalPoset.alexandrovTopology (toCausalPoset M₁))
      (CausalPoset.alexandrovTopology (toCausalPoset M₂))
      f := by
  -- Use order-respecting -> continuous for Alexandrov topologies.
  exact
    CausalPoset.continuous_alexandrov_of_le_monotone (C₁ := toCausalPoset M₁) (C₂ := toCausalPoset M₂)
      f (le_monotone_of_edgeHom (M₁ := M₁) (M₂ := M₂) (f := f) hf)

end DiscreteSpacetime

end AqeiBridge
