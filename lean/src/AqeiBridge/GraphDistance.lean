import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Graph distance on `Fin n` (bounded shortest-path scaffold)

This module defines a *bounded* shortest-path distance on a finite vertex set `Fin n`.

Design notes:
- We do not assume any graph axioms (symmetry, irreflexivity, connectedness).
- The distance is computed by searching path lengths up to `n` using a BFS-style ball expansion.
- If no path of length `≤ n` exists, we return the fallback value `n`.

This is intended as a base metric for `FinsetMetric.discreteHausdorff` in
`AqeiBridge.DiscreteHausdorff`.
-/

namespace AqeiBridge

namespace GraphDistance

variable {n : ℕ}

/-- One BFS expansion step: vertices reachable in one `adj`-step from some `v ∈ S`. -/
noncomputable def step (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (S : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact (Finset.univ : Finset (Fin n)).filter (fun w => ∃ v ∈ S, adj v w)

/-- A BFS ball of radius `k` around `v` (in the directed sense induced by `adj`). -/
noncomputable def ball (adj : Fin n → Fin n → Prop) [DecidableRel adj] (v : Fin n) : ℕ → Finset (Fin n)
  | 0 => {v}
  | k + 1 => step (n := n) adj (ball adj v k)

/-- The set of candidate radii `k ≤ n` that reach `w` from `v`. -/
noncomputable def candidates (adj : Fin n → Fin n → Prop) [DecidableRel adj] (v w : Fin n) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun k => w ∈ ball (n := n) adj v k)

/--
A bounded shortest-path distance (in `ℕ`) computed up to radius `n`.

If `w` is not reached within radius `n`, the fallback value `n` is returned.
-/
noncomputable def boundedDistNat (adj : Fin n → Fin n → Prop) [DecidableRel adj] (v w : Fin n) : ℕ :=
  let cs := candidates (n := n) adj v w
  if h : cs.Nonempty then cs.inf' h (fun k => k) else n

/-- The bounded graph distance as an `ℝ` value. -/
noncomputable def boundedDist (adj : Fin n → Fin n → Prop) [DecidableRel adj] (v w : Fin n) : ℝ :=
  (boundedDistNat (n := n) adj v w : ℝ)

lemma boundedDistNat_le (adj : Fin n → Fin n → Prop) [DecidableRel adj] (v w : Fin n) :
    boundedDistNat (n := n) adj v w ≤ n := by
  classical
  unfold boundedDistNat
  set cs := candidates (n := n) adj v w
  by_cases h : cs.Nonempty
  ·
    have hcs : cs.Nonempty := h
    rcases h with ⟨k, hk⟩
    have hif : (if h : cs.Nonempty then cs.inf' h (fun t => t) else n) = cs.inf' hcs (fun t => t) := by
      simp [hcs]
    have hinf : cs.inf' hcs (fun t => t) ≤ k :=
      Finset.inf'_le (s := cs) (f := fun t => t) hk
    have hk_range : k < n + 1 := by
      -- unfold `candidates` and use `mem_filter`.
      have : k ∈ Finset.range (n + 1) := by
        simpa [candidates, cs] using (Finset.mem_filter.1 hk).1
      exact Finset.mem_range.1 this
    have hk_le : k ≤ n := Nat.le_of_lt_succ hk_range
    have : cs.inf' hcs (fun t => t) ≤ n := le_trans hinf hk_le
    simpa [cs, hif] using this
  · simp [cs, h]

lemma boundedDist_le (adj : Fin n → Fin n → Prop) [DecidableRel adj] (v w : Fin n) :
    boundedDist (n := n) adj v w ≤ n := by
  -- Unfold, then `exact_mod_cast` handles the coercions `ℕ → ℝ`.
  simp [boundedDist]
  exact_mod_cast (boundedDistNat_le (n := n) adj v w)

lemma boundedDist_nonneg (adj : Fin n → Fin n → Prop) [DecidableRel adj] (v w : Fin n) :
    0 ≤ boundedDist (n := n) adj v w := by
  simp [boundedDist]

/-- The bounded graph distance from a vertex to itself is 0.
Every vertex is in its own 0-ball, so `0 ∈ candidates`, and `inf' ≤ 0`. -/
lemma boundedDistNat_self (adj : Fin n → Fin n → Prop) [DecidableRel adj] (v : Fin n) :
    boundedDistNat (n := n) adj v v = 0 := by
  have hmem0 : v ∈ ball (n := n) adj v 0 := Finset.mem_singleton_self v
  have hmem_cands : 0 ∈ candidates (n := n) adj v v := by
    simp only [candidates, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.succ_pos n, hmem0⟩
  have hne : (candidates (n := n) adj v v).Nonempty := ⟨0, hmem_cands⟩
  unfold boundedDistNat
  simp only [hne, dif_pos]
  have hinf : (candidates (n := n) adj v v).inf' hne (fun k => k) ≤ 0 :=
    Finset.inf'_le (s := candidates (n := n) adj v v) (f := fun k => k) hmem_cands
  omega

/-- The bounded graph distance from a vertex to itself is 0 (ℝ version). -/
lemma boundedDist_self (adj : Fin n → Fin n → Prop) [DecidableRel adj] (v : Fin n) :
    boundedDist (n := n) adj v v = 0 := by
  simp [boundedDist, boundedDistNat_self]

/-- If there is a direct edge `adj v u`, the bounded graph distance from `v` to `u` is ≤ 1. -/
lemma boundedDist_le_one_of_adj (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    {v u : Fin n} (h : adj v u) :
    boundedDist (n := n) adj v u ≤ 1 := by
  -- u is reachable from v in 1 step
  have hmem_ball : u ∈ ball (n := n) adj v 1 := by
    simp only [ball, step, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, Finset.mem_singleton_self v, h⟩
  -- so 1 ∈ candidates (need 1 < n+1, which follows from u : Fin n)
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
  have hmem_cands : 1 ∈ candidates (n := n) adj v u := by
    simp only [candidates, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hmem_ball⟩
  have hne : (candidates (n := n) adj v u).Nonempty := ⟨1, hmem_cands⟩
  have hdist : boundedDistNat (n := n) adj v u ≤ 1 := by
    unfold boundedDistNat
    simp only [hne, dif_pos]
    exact Finset.inf'_le (s := candidates (n := n) adj v u) (f := fun k => k) hmem_cands
  simp only [boundedDist]
  exact_mod_cast hdist

/-! ## Triangle inequality for boundedDist -/

/-- The `step` function is monotone: larger starting sets give larger 1-step
reachable sets. -/
lemma step_mono (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    {S T : Finset (Fin n)} (h : S ⊆ T) : step (n := n) adj S ⊆ step (n := n) adj T := by
  classical
  intro w hw
  simp only [step, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  obtain ⟨v, hv, hadj⟩ := hw
  exact ⟨v, h hv, hadj⟩

/-- If `u ∈ ball adj v k` and `w ∈ ball adj u j`, then `w ∈ ball adj v (k + j)`.
This is the key path-concatenation lemma. -/
lemma ball_concat (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (v u w : Fin n) (k j : ℕ)
    (hvu : u ∈ ball (n := n) adj v k)
    (huw : w ∈ ball (n := n) adj u j) :
    w ∈ ball (n := n) adj v (k + j) := by
  classical
  induction j generalizing w with
  | zero =>
    simp only [ball, Finset.mem_singleton] at huw
    subst huw
    simpa using hvu
  | succ j' ih =>
    simp only [ball, step, Finset.mem_filter, Finset.mem_univ, true_and] at huw
    obtain ⟨w', hw', hadj⟩ := huw
    have hw'_in_v : w' ∈ ball (n := n) adj v (k + j') := ih w' hw'
    rw [show k + (j' + 1) = (k + j') + 1 from by omega]
    simp only [ball, step, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w', hw'_in_v, hadj⟩

/-- If `u` is reachable from `v` within `n` steps
(i.e., `candidates adj v u` is nonempty), then `u ∈ ball adj v (boundedDistNat adj v u)`. -/
lemma mem_ball_of_boundedDistNat_of_nonempty (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (v u : Fin n) (hne : (candidates (n := n) adj v u).Nonempty) :
    u ∈ ball (n := n) adj v (boundedDistNat (n := n) adj v u) := by
  classical
  simp only [boundedDistNat, hne, dif_pos]
  -- The infimum over a nonempty finite set is achieved at some k_min in the set.
  rcases Finset.exists_min_image (candidates (n := n) adj v u) id hne
      with ⟨k_min, hk_min, hmin⟩
  have heq : (candidates (n := n) adj v u).inf' hne (fun k => k) = k_min :=
    le_antisymm (Finset.inf'_le (f := fun k => k) hk_min)
                (Finset.le_inf' hne (fun k => k) (fun b hb => hmin b hb))
  rw [heq]
  simp only [candidates, Finset.mem_filter] at hk_min
  exact hk_min.2

/-- **Triangle inequality for `boundedDistNat`**: the bounded nat-distance satisfies
`boundedDistNat v w ≤ boundedDistNat v u + boundedDistNat u w`. -/
lemma boundedDistNat_triangle (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (v u w : Fin n) :
    boundedDistNat (n := n) adj v w ≤
      boundedDistNat (n := n) adj v u + boundedDistNat (n := n) adj u w := by
  classical
  rcases le_or_gt
      (boundedDistNat (n := n) adj v u + boundedDistNat (n := n) adj u w) n with hle | hgt
  · -- sum ≤ n: look for an actual path of combined length
    by_cases hvune : (candidates (n := n) adj v u).Nonempty
    · by_cases huwne : (candidates (n := n) adj u w).Nonempty
      · -- Both sub-paths are reachable; concatenate them.
        have hvu := mem_ball_of_boundedDistNat_of_nonempty adj v u hvune
        have huw := mem_ball_of_boundedDistNat_of_nonempty adj u w huwne
        have hw := ball_concat adj v u w _ _ hvu huw
        have hkj_cands : boundedDistNat (n := n) adj v u + boundedDistNat (n := n) adj u w
            ∈ candidates (n := n) adj v w := by
          simp only [candidates, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hw⟩
        simp only [boundedDistNat, show (candidates (n := n) adj v w).Nonempty from ⟨_, hkj_cands⟩, dif_pos]
        exact Finset.inf'_le (f := fun k => k) hkj_cands
      · -- v→u path exists but u→w does not (within n steps); dist u w = n
        have hj : boundedDistNat (n := n) adj u w = n := by
          simp only [boundedDistNat, dif_neg huwne]
        linarith [boundedDistNat_le adj v u, boundedDistNat_le adj v w]
    · -- v→u path does not exist within n steps; dist v u = n
      have hk : boundedDistNat (n := n) adj v u = n := by
        simp only [boundedDistNat, dif_neg hvune]
      linarith [boundedDistNat_le adj u w, boundedDistNat_le adj v w]
  · -- sum > n: both ≤ n, so automatically ≥ n ≥ boundedDistNat v w
    linarith [boundedDistNat_le adj v w]

/-- **Triangle inequality for `boundedDist`** (ℝ version). -/
lemma boundedDist_triangle (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (v u w : Fin n) :
    boundedDist (n := n) adj v w ≤
      boundedDist (n := n) adj v u + boundedDist (n := n) adj u w := by
  simp only [boundedDist]
  exact_mod_cast boundedDistNat_triangle adj v u w

end GraphDistance


end AqeiBridge
