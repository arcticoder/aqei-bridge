import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Discrete Hausdorff-style distances on finite sets (scaffold)

This module provides a compilation-safe definition of a Hausdorff-style distance
between *finite* subsets, parameterized by an arbitrary distance function.

Motivation:
- The long-term plan is to reason about continuity/stability of future sets
  `J⁺(p)` under small perturbations.
- In this repo, the continuous/Hausdorff topology is blocked on choosing a
  metric/topology for the base space.
- As an unblock step, we define a *finite* Hausdorff-like quantity on `Finset`.

No metric axioms are assumed about `d`; later work can add hypotheses as needed.
-/

namespace AqeiBridge

namespace FinsetMetric

variable {α : Type}

/-- Minimum distance from a point to a finite set, using `0` for the empty set.

This is a purely algebraic helper; no metric axioms are assumed.
-/
noncomputable def minDistToSet (d : α → α → ℝ) (a : α) (B : Finset α) : ℝ :=
  if hB : B.Nonempty then
    B.inf' hB (fun b => d a b)
  else
    0

/-- Maximum over `a ∈ A` of the minimum distance from `a` to `B`.

This is the directed Hausdorff component `sup_{a∈A} inf_{b∈B} d(a,b)`,
implemented for finite sets, using `0` for the empty set.
-/
noncomputable def maxDistToSet (d : α → α → ℝ) (A B : Finset α) : ℝ :=
  if hA : A.Nonempty then
    A.sup' hA (fun a => minDistToSet d a B)
  else
    0

/-- A discrete Hausdorff-style distance between finite sets.

`d_H(A,B) = max( maxDistToSet A B, maxDistToSet B A )`.
-/
noncomputable def discreteHausdorff (d : α → α → ℝ) (A B : Finset α) : ℝ :=
  max (maxDistToSet d A B) (maxDistToSet d B A)

/-! ## Uniform boundedness lemmas -/

lemma minDistToSet_le_of_forall_le (d : α → α → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ x y, d x y ≤ C) (a : α) (B : Finset α) :
    minDistToSet d a B ≤ C := by
  classical
  by_cases hB : B.Nonempty
  ·
    rcases hB with ⟨b, hb⟩
    have hB' : B.Nonempty := ⟨b, hb⟩
    have hinf : B.inf' hB' (fun b' => d a b') ≤ d a b :=
      Finset.inf'_le (s := B) (f := fun b' => d a b') hb
    have hmin : minDistToSet d a B ≤ d a b := by
      simpa [minDistToSet, hB'] using hinf
    exact le_trans hmin (h a b)
  · simpa [minDistToSet, hB] using hC

lemma maxDistToSet_le_of_forall_le (d : α → α → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ x y, d x y ≤ C) (A B : Finset α) :
    maxDistToSet d A B ≤ C := by
  classical
  by_cases hA : A.Nonempty
  ·
    have hsup : (A.sup' hA fun a => minDistToSet d a B) ≤ C := by
      refine Finset.sup'_le (H := hA) (f := fun a => minDistToSet d a B) ?_
      intro a ha
      exact minDistToSet_le_of_forall_le (d := d) (C := C) hC h a B
    simpa [maxDistToSet, hA] using hsup
  · simpa [maxDistToSet, hA] using hC

lemma discreteHausdorff_le_of_forall_le (d : α → α → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ x y, d x y ≤ C) (A B : Finset α) :
    discreteHausdorff d A B ≤ C := by
  exact max_le
    (maxDistToSet_le_of_forall_le (d := d) (C := C) hC h A B)
    (maxDistToSet_le_of_forall_le (d := d) (C := C) hC h B A)

/-! ## Coverage-style bounds (∀∃) -/

lemma minDistToSet_le_of_exists_le (d : α → α → ℝ) (C : ℝ) (a : α)
    (B : Finset α) (hB : B.Nonempty) (hex : ∃ b ∈ B, d a b ≤ C) :
    minDistToSet d a B ≤ C := by
  classical
  rcases hex with ⟨b, hb, hdb⟩
  have hinf : B.inf' hB (fun b' => d a b') ≤ d a b :=
    Finset.inf'_le (s := B) (f := fun b' => d a b') hb
  have hmin : minDistToSet d a B ≤ d a b := by
    simpa [minDistToSet, hB] using hinf
  exact le_trans hmin hdb

lemma maxDistToSet_le_of_forall_exists (d : α → α → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (A B : Finset α)
    (h : ∀ a ∈ A, ∃ b ∈ B, d a b ≤ C) :
    maxDistToSet d A B ≤ C := by
  classical
  by_cases hA : A.Nonempty
  ·
    by_cases hB : B.Nonempty
    ·
      have hsup : (A.sup' hA fun a => minDistToSet d a B) ≤ C := by
        refine Finset.sup'_le (H := hA) (f := fun a => minDistToSet d a B) ?_
        intro a ha
        exact minDistToSet_le_of_exists_le (d := d) (C := C) (a := a) (B := B) hB (h a ha)
      simpa [maxDistToSet, hA] using hsup
    ·
      -- If `B` is empty but `A` is nonempty, the ∀∃ hypothesis is impossible.
      rcases hA with ⟨a0, ha0⟩
      rcases h a0 ha0 with ⟨b, hb, _⟩
      exact (hB ⟨b, hb⟩).elim
  ·
    simpa [maxDistToSet, hA] using hC

lemma discreteHausdorff_le_of_forall_exists (d : α → α → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (A B : Finset α)
    (hAB : ∀ a ∈ A, ∃ b ∈ B, d a b ≤ C)
    (hBA : ∀ b ∈ B, ∃ a ∈ A, d b a ≤ C) :
    discreteHausdorff d A B ≤ C := by
  exact max_le
    (maxDistToSet_le_of_forall_exists (d := d) (C := C) hC A B hAB)
    (maxDistToSet_le_of_forall_exists (d := d) (C := C) hC B A hBA)

/-! ## Triangle inequality for pseudometrics -/

/-- From `minDistToSet d a B ≤ C` and `B.Nonempty`, extract an actual witness `b ∈ B`
with `d a b ≤ C`. (The finite infimum is achieved.) -/
lemma exists_le_of_minDistToSet_le (d : α → α → ℝ) (C : ℝ) (a : α)
    {B : Finset α} (hB : B.Nonempty) (h : minDistToSet d a B ≤ C) :
    ∃ b ∈ B, d a b ≤ C := by
  classical
  rcases Finset.exists_min_image B (fun b => d a b) hB with ⟨b_min, hb_min, hmin⟩
  refine ⟨b_min, hb_min, ?_⟩
  have heq : minDistToSet d a B = d a b_min := by
    unfold minDistToSet
    simp only [dif_pos hB]
    apply le_antisymm
    · exact Finset.inf'_le (f := fun b => d a b) hb_min
    · exact Finset.le_inf' hB (fun b => d a b) (fun b hb => hmin b hb)
  exact heq.symm.le.trans h

/-- `maxDistToSet d A B` bounds `minDistToSet d a B` from above for any `a ∈ A`. -/
lemma minDistToSet_le_maxDistToSet (d : α → α → ℝ) (a : α)
    {A : Finset α} (haA : a ∈ A) (B : Finset α) :
    minDistToSet d a B ≤ maxDistToSet d A B := by
  classical
  have hA : A.Nonempty := ⟨a, haA⟩
  simp only [maxDistToSet, hA, dif_pos]
  exact Finset.le_sup' (s := A) (f := fun a => minDistToSet d a B) haA

/-- `maxDistToSet d A B ≤ discreteHausdorff d A B`. -/
lemma maxDistToSet_le_discreteHausdorff_left (d : α → α → ℝ) (A B : Finset α) :
    maxDistToSet d A B ≤ discreteHausdorff d A B :=
  le_max_left _ _

/-- `maxDistToSet d B A ≤ discreteHausdorff d A B`. -/
lemma maxDistToSet_le_discreteHausdorff_right (d : α → α → ℝ) (A B : Finset α) :
    maxDistToSet d B A ≤ discreteHausdorff d A B :=
  le_max_right _ _

/-- Nonnegativity of `maxDistToSet` when `A` is empty. -/
lemma maxDistToSet_nonneg_of_hA (d : α → α → ℝ) (hd0 : ∀ x y, 0 ≤ d x y)
    (A B : Finset α) : 0 ≤ maxDistToSet d A B := by
  classical
  by_cases hA : A.Nonempty
  · simp only [maxDistToSet, hA, dif_pos]
    rcases hA with ⟨a, ha⟩
    apply le_trans _ (Finset.le_sup' (s := A) (f := fun a => minDistToSet d a B) ha)
    simp only [minDistToSet]
    split_ifs with hB'
    · exact Finset.le_inf' hB' (fun b => d a b) (fun b _ => hd0 a b)
    · exact le_refl _
  · simp only [maxDistToSet, dif_neg hA]
    exact le_refl _

/-- `discreteHausdorff d A B = 0` when `A` is empty. -/
lemma discreteHausdorff_eq_zero_of_left_empty (d : α → α → ℝ) {A : Finset α}
    (hA : ¬A.Nonempty) (B : Finset α) : discreteHausdorff d A B = 0 := by
  classical
  have hmax1 : maxDistToSet d A B = 0 := by simp only [maxDistToSet, dif_neg hA]
  have hmax2 : maxDistToSet d B A = 0 := by
    simp only [maxDistToSet]
    split_ifs with hB
    · have hmin : ∀ b : α, minDistToSet d b A = 0 := fun b => by
        simp only [minDistToSet, dif_neg hA]
      have : (fun b => minDistToSet d b A) = fun _ => (0 : ℝ) := funext hmin
      rw [this]; exact Finset.sup'_const hB 0
    · rfl
  simp only [discreteHausdorff, hmax1, hmax2, max_self]

/-- `discreteHausdorff d A B = 0` when `B` is empty. -/
lemma discreteHausdorff_eq_zero_of_right_empty (d : α → α → ℝ) (A : Finset α)
    {B : Finset α} (hB : ¬B.Nonempty) : discreteHausdorff d A B = 0 := by
  classical
  have hmax1 : maxDistToSet d A B = 0 := by
    simp only [maxDistToSet]
    split_ifs with hA
    · have hmin : ∀ a : α, minDistToSet d a B = 0 := fun a => by
        simp only [minDistToSet, dif_neg hB]
      have : (fun a => minDistToSet d a B) = fun _ => (0 : ℝ) := funext hmin
      rw [this]; exact Finset.sup'_const hA 0
    · rfl
  have hmax2 : maxDistToSet d B A = 0 := by simp only [maxDistToSet, dif_neg hB]
  simp only [discreteHausdorff, hmax1, hmax2, max_self]

/-- **Triangle inequality for `discreteHausdorff`**: if `d` is a pseudometric and `B`
is nonempty, then `dH(A, C) ≤ dH(A, B) + dH(B, C)`. -/
lemma discreteHausdorff_triangle (d : α → α → ℝ)
    (hd : ∀ x y z : α, d x z ≤ d x y + d y z)
    (hd0 : ∀ x y : α, 0 ≤ d x y)
    {B : Finset α} (hB : B.Nonempty) (A C : Finset α) :
    discreteHausdorff d A C ≤ discreteHausdorff d A B + discreteHausdorff d B C := by
  classical
  have hnn : (0:ℝ) ≤ discreteHausdorff d A B + discreteHausdorff d B C := by
    have h1 : (0:ℝ) ≤ maxDistToSet d A B := maxDistToSet_nonneg_of_hA d hd0 A B
    have h2 : (0:ℝ) ≤ maxDistToSet d B C := maxDistToSet_nonneg_of_hA d hd0 B C
    have h3 : maxDistToSet d A B ≤ discreteHausdorff d A B := le_max_left _ _
    have h4 : maxDistToSet d B C ≤ discreteHausdorff d B C := le_max_left _ _
    linarith
  -- Handle empty cases: if A or C is empty, dH(A,C) = 0 ≤ sum.
  by_cases hAne : A.Nonempty
  swap
  · rw [discreteHausdorff_eq_zero_of_left_empty d hAne C]; linarith
  by_cases hCne : C.Nonempty
  swap
  · rw [discreteHausdorff_eq_zero_of_right_empty d A hCne]; linarith
  -- Both A and C are nonempty: use coverage-style bounds.
  apply discreteHausdorff_le_of_forall_exists d
      (discreteHausdorff d A B + discreteHausdorff d B C) hnn
  · -- A → C direction: for a ∈ A, find c ∈ C with d(a,c) ≤ dH(A,B) + dH(B,C)
    intro a ha
    have hmidAB : minDistToSet d a B ≤ discreteHausdorff d A B :=
      le_trans (minDistToSet_le_maxDistToSet d a ha B)
               (maxDistToSet_le_discreteHausdorff_left d A B)
    rcases exists_le_of_minDistToSet_le d _ a hB hmidAB with ⟨b, hbB, hdab⟩
    have hmidBC : minDistToSet d b C ≤ discreteHausdorff d B C :=
      le_trans (minDistToSet_le_maxDistToSet d b hbB C)
               (maxDistToSet_le_discreteHausdorff_left d B C)
    rcases exists_le_of_minDistToSet_le d _ b hCne hmidBC with ⟨c, hcC, hdbc⟩
    exact ⟨c, hcC, le_trans (hd a b c) (by linarith)⟩
  · -- C → A direction: for c ∈ C, find a ∈ A with d(c,a) ≤ dH(A,B) + dH(B,C)
    intro c hcC
    have hmidCB : minDistToSet d c B ≤ discreteHausdorff d B C :=
      le_trans (minDistToSet_le_maxDistToSet d c hcC B)
               (maxDistToSet_le_discreteHausdorff_right d B C)
    rcases exists_le_of_minDistToSet_le d _ c hB hmidCB with ⟨b, hbB, hdcb⟩
    have hmidBA : minDistToSet d b A ≤ discreteHausdorff d A B :=
      le_trans (minDistToSet_le_maxDistToSet d b hbB A)
               (maxDistToSet_le_discreteHausdorff_right d A B)
    rcases exists_le_of_minDistToSet_le d _ b hAne hmidBA with ⟨a, haA, hdba⟩
    exact ⟨a, haA, le_trans (hd c b a) (by linarith)⟩

end FinsetMetric

end AqeiBridge


