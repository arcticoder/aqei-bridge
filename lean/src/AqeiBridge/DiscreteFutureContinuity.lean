import Mathlib.Data.Real.Basic

import AqeiBridge.DiscreteHausdorff
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

end FiniteCausalPoset

end AqeiBridge
