import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic

/-!
# Causal posets and an Alexandrov-style topology (toy bridge)

This file adds a minimal *order-theoretic* causality interface.

Motivation:
- The long-term “global causality as a topological obstruction” direction wants
  invariants attached to a causal structure.
- A causal **preorder** is a light-weight formal object we can work with now.

This is intentionally separate from the Lorentzian-manifold development.
-/

namespace AqeiBridge

/-- A causal poset interface: events with a preorder `≤`.

We use a `Preorder` rather than a `PartialOrder` to allow identification
(e.g. distinct points with mutual reachability).
-/
structure CausalPoset where
  Pt : Type
  le : Pt → Pt → Prop
  refl : ∀ p, le p p
  trans : ∀ {p q r}, le p q → le q r → le p r

namespace CausalPoset

instance (C : CausalPoset) : Preorder C.Pt where
  le := C.le
  lt := fun a b => C.le a b ∧ ¬ C.le b a
  le_refl := C.refl
  le_trans := by
    intro a b c hab hbc
    exact C.trans hab hbc

/-- Order-theoretic causal future set $J^+(p) := \{q \mid p \le q\}$. -/
def Jplus (C : CausalPoset) (p : C.Pt) : Set C.Pt := {q | p ≤ q}

/-- A set is an upper set if it is closed upward under `≤`. -/
def IsUpperSet (C : CausalPoset) (s : Set C.Pt) : Prop :=
  ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, a ≤ b → b ∈ s

/-- Alexandrov-style topology for a preorder: opens are upper sets.

This is the standard topology whose specialization preorder is the given `≤`.
-/
noncomputable def alexandrovTopology (C : CausalPoset) : TopologicalSpace C.Pt where
  IsOpen s := IsUpperSet C s
  isOpen_univ := by
    intro a ha b hab
    trivial
  isOpen_inter := by
    intro s t hs ht
    intro a ha b hab
    exact ⟨hs ha.1 hab, ht ha.2 hab⟩
  isOpen_sUnion := by
    intro S hS
    intro a ha b hab
    rcases ha with ⟨s, hsS, has⟩
    refine ⟨s, hsS, ?_⟩
    exact hS s hsS has hab

/-- In the Alexandrov topology, `Jplus p` is open. -/
theorem isOpen_Jplus (C : CausalPoset) (p : C.Pt) :
    @IsOpen _ (alexandrovTopology C) (Jplus C p) := by
  intro a ha b hab
  exact le_trans ha hab

/-- Monotonicity: if `p ≤ q` then `Jplus q ⊆ Jplus p` (future inclusion reverses).

This matches the order-theoretic intuition: later points have smaller futures.
-/
theorem jplus_antitone {C : CausalPoset} {p q : C.Pt} (hpq : p ≤ q) :
    Jplus C q ⊆ Jplus C p := by
  intro r hqr
  exact le_trans hpq hqr

end CausalPoset

end AqeiBridge
