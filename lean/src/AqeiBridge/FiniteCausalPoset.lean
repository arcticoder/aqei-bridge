import Mathlib.Data.Rel
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Basic

import AqeiBridge.CausalPoset

/-!
# Finite causal posets (scaffold)

This file provides a concrete representation of *finite* causal posets with carrier `Fin n`.

Motivation:
- The blocked TODO item “poset homology / order complex in Lean (full)” needs a concrete,
  decidable representation of finite posets so we can enumerate chains/simplices.
- We keep this file lightweight: it exposes (1) a relation + axioms, (2) a decidable chain
  predicate, and (3) an explicit `Finset` enumeration of `k`-chains.

Future work (not done here): connect `Chains` to Mathlib’s simplicial/order-complex homology.
-/

namespace AqeiBridge

/-- A finite causal poset on `Fin n`.

We store `decRel` so `Chains` can be computed by filtering `powerset`.
-/
structure FiniteCausalPoset (n : ℕ) where
  rel : Rel (Fin n) (Fin n)
  decRel : DecidableRel rel
  refl : Reflexive rel
  antisymm : ∀ ⦃a b⦄, rel a b → rel b a → a = b
  trans : Transitive rel

attribute [instance] FiniteCausalPoset.decRel

namespace FiniteCausalPoset

variable {n : ℕ}

/-- The causal future as a `Finset`, computed by filtering `Finset.univ`. -/
def JplusFinset (P : FiniteCausalPoset n) (p : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun q => P.rel p q)

/-- Convert a `FiniteCausalPoset` to the repo’s generic `CausalPoset` interface.

Note: `CausalPoset` is only a preorder; we ignore antisymmetry here.
-/
def toCausalPoset (P : FiniteCausalPoset n) : AqeiBridge.CausalPoset where
  Pt := Fin n
  le := P.rel
  refl := P.refl
  trans := by
    intro p q r hpq hqr
    exact P.trans hpq hqr

/-- A finset is a chain if its elements are pairwise comparable under `P.rel`.

This is the finset version of “totally ordered subset”.
-/
def IsChain (P : FiniteCausalPoset n) (σ : Finset (Fin n)) : Prop :=
  (σ : Set (Fin n)).Pairwise fun a b => P.rel a b ∨ P.rel b a

/-- Enumerate `k`-chains (i.e. subsets of cardinality `k+1` that are chains).

This is an explicit finite enumeration via `powerset`; it is suitable for small `n` and
for toy-model sanity checks.
-/
noncomputable def Chains (P : FiniteCausalPoset n) (k : ℕ) : Finset (Finset (Fin n)) := by
  classical
  exact ((Finset.univ : Finset (Fin n)).powerset).filter fun σ =>
    σ.card = k + 1 ∧ IsChain P σ

end FiniteCausalPoset

end AqeiBridge
