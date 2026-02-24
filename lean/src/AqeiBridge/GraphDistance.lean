import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Real.Basic

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

end GraphDistance

end AqeiBridge
