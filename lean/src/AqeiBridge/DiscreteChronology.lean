import Std

import AqeiBridge.DiscreteCausality
import AqeiBridge.DiscreteCausalPoset

/-!
# Discrete chronology / CTC proxy (toy obstruction)

This file records a minimal “chronology” obstruction in the discrete model.

We treat a nontrivial closed causal curve (CTC proxy) as the existence of two
*distinct* points which are mutually reachable under reflexive-transitive
closure.

This is the exact negation of antisymmetry for the induced reachability preorder,
so it gives a clean Lean-level invariant to bridge to other parts of the repo.
-/

namespace AqeiBridge

namespace DiscreteSpacetime

/-- A discrete “CTC proxy”: distinct points with mutual reachability. -/
def HasNontrivialCycle {Pt : Type} (M : DiscreteSpacetime Pt) : Prop :=
  ∃ p q : Pt, p ≠ q ∧ ReachableRefl M p q ∧ ReachableRefl M q p

/-- A directed-cycle proxy: a nonempty directed path starting and ending at the same point. -/
def HasDirectedCycle {Pt : Type} (M : DiscreteSpacetime Pt) : Prop :=
  ∃ p : Pt, Relation.TransGen M.edge p p

/-- Irreflexive edge relation: no self-edges. -/
def NoSelfEdges {Pt : Type} (M : DiscreteSpacetime Pt) : Prop :=
  ∀ p : Pt, ¬ M.edge p p

/-- Turn a nonempty path (`TransGen`) into a reflexive-transitive path (`ReflTransGen`). -/
theorem reflTransGen_of_transGen {Pt : Type} {M : DiscreteSpacetime Pt} {p q : Pt}
    (h : Relation.TransGen M.edge p q) : ReachableRefl M p q := by
  induction h with
  | single hpq =>
      exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl hpq
  | tail hab hbc ih =>
      exact Relation.ReflTransGen.tail ih hbc

/-- Antisymmetry of `ReachableRefl`: mutual reachability forces equality. -/
def IsAntisymmReachableRefl {Pt : Type} (M : DiscreteSpacetime Pt) : Prop :=
  ∀ p q : Pt, ReachableRefl M p q → ReachableRefl M q p → p = q

theorem hasNontrivialCycle_iff_not_antisymmReachableRefl {Pt : Type} (M : DiscreteSpacetime Pt) :
    HasNontrivialCycle M ↔ ¬ IsAntisymmReachableRefl M := by
  classical
  constructor
  · intro h hanti
    rcases h with ⟨p, q, hpq, hpqR, hqpR⟩
    exact hpq (hanti p q hpqR hqpR)
  · intro h
    have h' : ∃ p q : Pt, ReachableRefl M p q ∧ ReachableRefl M q p ∧ p ≠ q := by
      simpa [IsAntisymmReachableRefl] using h
    rcases h' with ⟨p, q, hpqR, hqpR, hpq⟩
    exact ⟨p, q, hpq, hpqR, hqpR⟩

/-- Any nontrivial cycle yields two distinct points with mutual reachability
in the induced causal poset preorder. -/
theorem exists_mutual_reachability_of_hasNontrivialCycle {Pt : Type} {M : DiscreteSpacetime Pt}
    (h : HasNontrivialCycle M) :
    ∃ p q : Pt, p ≠ q ∧ (toCausalPoset M).le p q ∧ (toCausalPoset M).le q p := by
  rcases h with ⟨p, q, hpq, hpqR, hqpR⟩
  exact ⟨p, q, hpq, hpqR, hqpR⟩

/-- Edge-homomorphisms preserve directed cycles. -/
theorem hasDirectedCycle_of_edgeHom {Pt₁ Pt₂ : Type}
    {M₁ : DiscreteSpacetime Pt₁} {M₂ : DiscreteSpacetime Pt₂} {f : Pt₁ → Pt₂}
    (hf : EdgeHom M₁ M₂ f) :
    HasDirectedCycle M₁ → HasDirectedCycle M₂ := by
  intro h
  rcases h with ⟨p, hp⟩
  have hmap : ∀ {a b : Pt₁}, Relation.TransGen M₁.edge a b → Relation.TransGen M₂.edge (f a) (f b) := by
    intro a b hab
    induction hab with
    | single hab =>
        exact Relation.TransGen.single (hf hab)
    | tail hab hbc ih =>
        exact Relation.TransGen.tail ih (hf hbc)
  exact ⟨f p, hmap hp⟩

/-- If the edge relation has no self-edges, any directed cycle yields a nontrivial mutual-reachability obstruction.

This is the toy discrete analogue of “CTCs imply failure of chronology”.
-/
theorem hasNontrivialCycle_of_noSelfEdges_of_hasDirectedCycle {Pt : Type} {M : DiscreteSpacetime Pt}
    (hNoSelf : NoSelfEdges M) (hCycle : HasDirectedCycle M) :
    HasNontrivialCycle M := by
  rcases hCycle with ⟨p, hp⟩
  -- Peel the first edge off the cycle; no-self-edges ensures it changes the point.
  cases hp with
  | single hpp =>
      exact False.elim (hNoSelf p hpp)
  | tail hab hbc =>
      rename_i b
      -- `hab : TransGen edge p b` and `hbc : edge b p`? Actually in `tail`, the last edge is appended.
      -- Here `hab : TransGen M.edge p b` and `hbc : M.edge b p`.
      have hpb : ReachableRefl M p b := reflTransGen_of_transGen hab
      have hbp : ReachableRefl M b p :=
        Relation.ReflTransGen.tail Relation.ReflTransGen.refl hbc
      have hneq : p ≠ b := by
        intro hEq
        subst hEq
        exact hNoSelf p hbc
      exact ⟨p, b, hneq, hpb, hbp⟩

end DiscreteSpacetime

end AqeiBridge
