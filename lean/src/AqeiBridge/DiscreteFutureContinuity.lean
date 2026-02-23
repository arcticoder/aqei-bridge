import Mathlib.Data.Real.Basic

import AqeiBridge.DiscreteHausdorff
import AqeiBridge.GraphDistance
import AqeiBridge.FiniteCausalPoset

/-!
# Discrete future-set continuity (starter scaffold)

This file adds a minimal, *provable* continuity statement for finite future sets using the
repo’s `FinsetMetric.discreteHausdorff` construction.

Notes:
- The long-term plan (see `docs/TODO-BLOCKED.md`) is to use a graph distance (shortest path length)
  on a finite reachability model.
- As a first unblock step, we choose the 0/1 discrete metric on a finite type. This makes it easy
  to state (and prove) uniform continuity bounds for `discreteHausdorff`.

This is intentionally conservative: it does not attempt to connect AQEI “smallness” to the
underlying causal graph yet.
-/

namespace AqeiBridge

namespace FinsetMetric

variable {α : Type} [DecidableEq α]

/-- The 0/1 discrete metric as an `ℝ`-valued distance function. -/
def disc01 (a b : α) : ℝ :=
  if a = b then 0 else 1

lemma disc01_nonneg (a b : α) : 0 ≤ disc01 a b := by
  by_cases h : a = b <;> simp [disc01, h]

lemma disc01_le_one (a b : α) : disc01 a b ≤ 1 := by
  by_cases h : a = b <;> simp [disc01, h]

lemma minDistToSet_disc01_le_one (a : α) (B : Finset α) :
    minDistToSet disc01 a B ≤ 1 := by
  classical
  by_cases hB : B.Nonempty
  · rcases hB with ⟨b, hb⟩
    have hB' : B.Nonempty := ⟨b, hb⟩
    have hex : ∃ i ∈ B, disc01 a i ≤ (1 : ℝ) := ⟨b, hb, disc01_le_one a b⟩
    simpa [minDistToSet, hB'] using hex
  · simp [minDistToSet, hB]

lemma maxDistToSet_disc01_le_one (A B : Finset α) :
    maxDistToSet disc01 A B ≤ 1 := by
  classical
  by_cases hA : A.Nonempty
  ·
    -- `sup'` is bounded above by a constant bound on all elements.
    have hsup : (A.sup' hA fun a => minDistToSet disc01 a B) ≤ (1 : ℝ) := by
      refine Finset.sup'_le (H := hA) (f := fun a => minDistToSet disc01 a B) ?_
      intro a ha
      exact minDistToSet_disc01_le_one (a := a) (B := B)
    simpa [maxDistToSet, hA] using hsup
  · simp [maxDistToSet, hA]

/-- With the 0/1 discrete metric, `discreteHausdorff` is always `≤ 1`. -/
lemma discreteHausdorff_disc01_le_one (A B : Finset α) :
    discreteHausdorff disc01 A B ≤ 1 := by
  classical
  exact max_le (maxDistToSet_disc01_le_one (A := A) (B := B))
    (maxDistToSet_disc01_le_one (A := B) (B := A))

lemma minDistToSet_disc01_eq_zero_of_mem (a : α) {B : Finset α} (ha : a ∈ B) :
    minDistToSet disc01 a B = 0 := by
  classical
  have hB : B.Nonempty := ⟨a, ha⟩
  -- `≤ 0` by exhibiting `b = a`.
  have hle : minDistToSet disc01 a B ≤ 0 := by
    have hex : ∃ i ∈ B, disc01 a i ≤ (0 : ℝ) := by
      refine ⟨a, ha, ?_⟩
      simp [disc01]
    simpa [minDistToSet, hB] using hex
  -- `≥ 0` since `disc01` is nonnegative and `inf'` preserves lower bounds.
  have hge : 0 ≤ minDistToSet disc01 a B := by
    have hinf : (0 : ℝ) ≤ (B.inf' hB fun b => disc01 a b) := by
      -- `0 ≤ inf'` iff `0 ≤ f b` for all `b ∈ B`.
      refine (Finset.le_inf'_iff (s := B) (H := hB) (f := fun b => disc01 a b)).2 ?_
      intro b hb
      exact disc01_nonneg (a := a) (b := b)
    simpa [minDistToSet, hB] using hinf
  exact le_antisymm (by simpa using hle) (by simpa using hge)

lemma maxDistToSet_disc01_eq_zero_of_subset {A B : Finset α} (hAB : A ⊆ B) :
    maxDistToSet disc01 A B = 0 := by
  classical
  by_cases hA : A.Nonempty
  ·
    have hsup : (A.sup' hA fun a => minDistToSet disc01 a B) ≤ (0 : ℝ) := by
      refine Finset.sup'_le (H := hA) (f := fun a => minDistToSet disc01 a B) ?_
      intro a ha
      have : a ∈ B := hAB ha
      simpa [minDistToSet_disc01_eq_zero_of_mem (a := a) (B := B) this]
    have hge : (0 : ℝ) ≤ (A.sup' hA fun a => minDistToSet disc01 a B) := by
      have hA' : A.Nonempty := hA
      rcases hA with ⟨a0, ha0⟩
      have h0 : (0 : ℝ) ≤ minDistToSet disc01 a0 B := by
        by_cases hB : B.Nonempty
        ·
          have hinf : (0 : ℝ) ≤ (B.inf' hB fun b => disc01 a0 b) := by
            refine (Finset.le_inf'_iff (s := B) (H := hB) (f := fun b => disc01 a0 b)).2 ?_
            intro b hb
            exact disc01_nonneg (a := a0) (b := b)
          simpa [minDistToSet, hB] using hinf
        · simp [minDistToSet, hB]
      have hsupa : minDistToSet disc01 a0 B ≤ (A.sup' hA' fun a => minDistToSet disc01 a B) := by
        exact Finset.le_sup' (s := A) (f := fun a => minDistToSet disc01 a B) ha0
      exact le_trans h0 hsupa
    have : A.sup' hA (fun a => minDistToSet disc01 a B) = 0 :=
      le_antisymm (by simpa using hsup) (by simpa using hge)
    simpa [maxDistToSet, hA, this]
  · simp [maxDistToSet, hA]

lemma maxDistToSet_disc01_eq_zero_of_eq {A B : Finset α} (h : A = B) :
    maxDistToSet disc01 A B = 0 := by
  subst h
  exact maxDistToSet_disc01_eq_zero_of_subset (A := A) (B := A) (by intro a ha; exact ha)

/-! ### Bounded graph distance instantiation -/

open GraphDistance

variable {n : ℕ}

lemma discreteHausdorff_boundedDist_le (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (A B : Finset (Fin n)) :
    FinsetMetric.discreteHausdorff (GraphDistance.boundedDist (n := n) adj) A B ≤ n := by
  have hC : (0 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.zero_le n)
  have h : ∀ x y : Fin n, GraphDistance.boundedDist (n := n) adj x y ≤ n := by
    intro x y
    simpa using GraphDistance.boundedDist_le (n := n) (adj := adj) x y
  simpa using
    FinsetMetric.discreteHausdorff_le_of_forall_le
      (d := GraphDistance.boundedDist (n := n) adj) (C := (n : ℝ)) hC h A B

end FinsetMetric

namespace FiniteCausalPoset

open FinsetMetric

variable {n : ℕ}

/-- A minimal “future-set continuity” statement for finite causal posets.

Using the discrete 0/1 metric, the Hausdorff distance between any two finite futures is bounded
by `1`. This is a placeholder bound that will be strengthened once a graph shortest-path distance
is implemented.
-/
lemma jplus_discreteHausdorff_le_one (P Q : FiniteCausalPoset n) (p : Fin n) :
    FinsetMetric.discreteHausdorff FinsetMetric.disc01 (P.JplusFinset p) (Q.JplusFinset p) ≤ 1 :=
  FinsetMetric.discreteHausdorff_disc01_le_one (A := P.JplusFinset p) (B := Q.JplusFinset p)

/-- If `Q` extends `P` (relation-wise), the future set only grows. -/
lemma jplusFinset_subset_of_relExtension (P Q : FiniteCausalPoset n)
    (h : ∀ ⦃a b⦄, P.rel a b → Q.rel a b) (p : Fin n) :
    P.JplusFinset p ⊆ Q.JplusFinset p := by
  intro q hq
  have : P.rel p q := by
    simpa [FiniteCausalPoset.JplusFinset] using hq
  have : Q.rel p q := h this
  -- unfold membership in the filtered `univ`
  simpa [FiniteCausalPoset.JplusFinset] using this

/-- One-sided Hausdorff distance is 0 when the future set only grows (disc01 metric). -/
lemma jplus_maxDistToSet_disc01_eq_zero_of_relExtension (P Q : FiniteCausalPoset n)
    (h : ∀ ⦃a b⦄, P.rel a b → Q.rel a b) (p : Fin n) :
    FinsetMetric.maxDistToSet FinsetMetric.disc01 (P.JplusFinset p) (Q.JplusFinset p) = 0 := by
  have hsub := jplusFinset_subset_of_relExtension (P := P) (Q := Q) h p
  exact FinsetMetric.maxDistToSet_disc01_eq_zero_of_subset (A := P.JplusFinset p) (B := Q.JplusFinset p) hsub

end FiniteCausalPoset

end AqeiBridge
