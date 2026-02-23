import AqeiBridge.AlexandrovPresheafMathlib

/-!
# Example: a diamond poset presheaf instantiation

This file is a *typecheck-only* sanity check: we define a small “diamond” causal preorder
and build the Mathlib presheaf of continuous ℝ-valued functions on its Alexandrov opens.

We do not attempt to compute H¹ here; this is just to ensure the sheaf/presheaf interface
is usable in this repo with the pinned Mathlib.
-/

namespace AqeiBridge

open CausalPoset

/-- A 4-point “diamond” preorder, implemented as the product order on `Fin 2 × Fin 2`.

The Hasse diagram has bottom `(0,0)`, incomparable middle points `(1,0)` and `(0,1)`, and top
`(1,1)`.
-/
noncomputable def diamondPoset : AqeiBridge.CausalPoset where
  Pt := Fin 2 × Fin 2
  le := fun a b => a.1 ≤ b.1 ∧ a.2 ≤ b.2
  refl := by
    intro p
    exact ⟨le_rfl, le_rfl⟩
  trans := by
    intro p q r hpq hqr
    exact ⟨le_trans hpq.1 hqr.1, le_trans hpq.2 hqr.2⟩

/-- The Mathlib presheaf of continuous real-valued functions on the diamond Alexandrov space. -/
noncomputable def diamondRealPresheaf : (CausalPoset.alexandrovTopCat diamondPoset).Presheaf CommRingCat :=
  CausalPoset.realContinuousPresheaf diamondPoset

end AqeiBridge
