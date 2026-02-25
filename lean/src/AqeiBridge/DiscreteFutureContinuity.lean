import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Prod

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
      simp [minDistToSet_disc01_eq_zero_of_mem (a := a) (B := B) this]
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
          simp [minDistToSet, hB, hinf]
        · simp [minDistToSet, hB]
      have hsupa : minDistToSet disc01 a0 B ≤ (A.sup' hA' fun a => minDistToSet disc01 a B) := by
        exact Finset.le_sup' (s := A) (f := fun a => minDistToSet disc01 a B) ha0
      exact le_trans h0 hsupa
    have : A.sup' hA (fun a => minDistToSet disc01 a B) = 0 :=
      le_antisymm (by simp [hsup]) (by simp [hge])
    simp [maxDistToSet, hA, this]
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


/-- Coverage-based Lipschitz bound for future sets under the bounded graph metric.

Given a background adjacency relation `adj`, if every vertex in `P`'s future-set
has a representative in `Q`'s future-set within `C` `adj`-steps (and vice versa),
then `discreteHausdorff (boundedDist adj)` is bounded by `C`.

This formalizes the perturbation model: two causal structures whose future sets
are mutually `C`-covered (in the graph metric) have Hausdorff distance ≤ C.
-/
lemma jplus_discreteHausdorff_coverage
    (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (P Q : FiniteCausalPoset n) (p : Fin n) (C : ℝ) (hC : 0 ≤ C)
    (hPQ : ∀ a ∈ P.JplusFinset p, ∃ b ∈ Q.JplusFinset p,
        GraphDistance.boundedDist adj a b ≤ C)
    (hQP : ∀ b ∈ Q.JplusFinset p, ∃ a ∈ P.JplusFinset p,
        GraphDistance.boundedDist adj b a ≤ C) :
    FinsetMetric.discreteHausdorff
        (GraphDistance.boundedDist adj) (P.JplusFinset p) (Q.JplusFinset p) ≤ C :=
  FinsetMetric.discreteHausdorff_le_of_forall_exists
    (GraphDistance.boundedDist adj) C hC (P.JplusFinset p) (Q.JplusFinset p) hPQ hQP

/-! ### A.1 Tight Hausdorff ≤ 1 under single-edge perturbation -/

/-- **A.1 Tight bound**: If `P` and `Q` agree on all pairs except `(u, v)` —
where `P.rel u v` holds but `¬ Q.rel u v` — then their J⁺-future Hausdorff
distance under the symmetrized-P graph metric is at most 1.

Proof outline:
- `Q ⊆ P` on every pair except `(u,v)`, so `JplusFinset Q p ⊆ JplusFinset P p`.
- The only extra point in `JplusFinset P p` is `v` (and only when `p = u`).
- We pair `v` with `u ∈ JplusFinset Q u` (reflexivity); `adj v u = True` (via
  `P.rel u v` and the symmetrized adjacency), so `boundedDist adj v u ≤ 1`.
-/
lemma jplus_hausdorff_le_one_of_edge_diff (P Q : FiniteCausalPoset n)
    (u v : Fin n)
    (hPQ : ∀ a b : Fin n, ¬(a = u ∧ b = v) → (P.rel a b ↔ Q.rel a b))
    (hPuv : P.rel u v)
    (hQuv : ¬ Q.rel u v)
    (p : Fin n) :
    FinsetMetric.discreteHausdorff
        (GraphDistance.boundedDist (n := n)
          (fun a b : Fin n => P.rel a b ∨ P.rel b a))
        (P.JplusFinset p) (Q.JplusFinset p) ≤ 1 := by
  classical
  refine FinsetMetric.discreteHausdorff_le_of_forall_exists
      (d := GraphDistance.boundedDist (fun a b : Fin n => P.rel a b ∨ P.rel b a))
      (C := 1) (by norm_num)
      (P.JplusFinset p) (Q.JplusFinset p) ?_ ?_
  · -- Forward: ∀ q ∈ P's future, ∃ q' ∈ Q's future with dist ≤ 1
    intro q hq
    simp only [FiniteCausalPoset.JplusFinset, Finset.mem_filter,
               Finset.mem_univ, true_and] at hq
    by_cases hQpq : Q.rel p q
    · -- q already in Q's future
      exact ⟨q, by simp only [FiniteCausalPoset.JplusFinset,
                               Finset.mem_filter, Finset.mem_univ,
                               true_and, hQpq],
             by simp [GraphDistance.boundedDist_self]⟩
    · -- Only missing point is v when p = u
      have hpq : p = u ∧ q = v := by
        by_contra hne; exact hQpq ((hPQ p q hne).mp hq)
      obtain ⟨rfl, rfl⟩ := hpq
      -- After substitution: p plays role of u, the intro'd q plays role of v
      -- hPuv : P.rel p q (was P.rel u v); goal: ∃ q' ∈ Q.JplusFinset p, dist q q' ≤ 1
      refine ⟨p, ?_, GraphDistance.boundedDist_le_one_of_adj
               (fun a b : Fin n => P.rel a b ∨ P.rel b a) (Or.inr hPuv)⟩
      simp only [FiniteCausalPoset.JplusFinset,
                 Finset.mem_filter, Finset.mem_univ, true_and]
      exact Q.refl p
  · -- Backward: ∀ q ∈ Q's future, ∃ q' ∈ P's future with dist ≤ 1
    intro q hq
    simp only [FiniteCausalPoset.JplusFinset, Finset.mem_filter,
               Finset.mem_univ, true_and] at hq
    have hPpq : P.rel p q := by
      by_cases hpq : p = u ∧ q = v
      · exact hpq.1 ▸ hpq.2 ▸ hPuv
      · exact (hPQ p q hpq).mpr hq
    exact ⟨q, by simp only [FiniteCausalPoset.JplusFinset,
                             Finset.mem_filter, Finset.mem_univ,
                             true_and, hPpq],
           by simp [GraphDistance.boundedDist_self]⟩
end FiniteCausalPoset

/-!
### A.3 Extend tight bound to k-edge perturbations

Combining A.1 with the `discreteHausdorff_triangle` from `DiscreteHausdorff.lean`,
a chain of `k` single-edge perturbations gives Hausdorff distance ≤ k.
-/

namespace FiniteCausalPoset

open FinsetMetric GraphDistance

variable {n : ℕ}

/-- Inner induction lemma for A.3: avoids variable-capture issues. -/
private lemma jplus_hausdorff_le_chain_aux
    (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (p : Fin n) :
    ∀ (m : ℕ) (c : Fin (m + 1) → FiniteCausalPoset n)
      (_ : ∀ i : Fin m,
          FinsetMetric.discreteHausdorff (boundedDist (n := n) adj)
            ((c (Fin.castSucc i)).JplusFinset p)
            ((c i.succ).JplusFinset p) ≤ 1),
      FinsetMetric.discreteHausdorff (boundedDist (n := n) adj)
        ((c ⟨0, Nat.succ_pos m⟩).JplusFinset p)
        ((c ⟨m, Nat.lt_succ_self m⟩).JplusFinset p) ≤ (m : ℝ) := by
  intro m
  induction m with
  | zero =>
    intro c _
    simp only [Nat.cast_zero]
    have heq : c ⟨0, Nat.succ_pos 0⟩ = c ⟨0, Nat.lt_succ_self 0⟩ := by congr 1
    rw [heq]
    -- dH(S, S) = 0 ≤ 0: for each a ∈ S pick b = a — boundedDist_self gives d a a = 0 ≤ 0
    apply FinsetMetric.discreteHausdorff_le_of_forall_exists
    · exact le_refl 0
    · intro a ha
      exact ⟨a, ha, by rw [GraphDistance.boundedDist_self]⟩
    · intro b hb
      exact ⟨b, hb, by rw [GraphDistance.boundedDist_self]⟩
  | succ m' ih =>
    intro c hs
    -- The middle set is nonempty because JplusFinset always contains p (via refl)
    have hmid : ((c ⟨m', Nat.lt_succ_of_lt (Nat.lt_succ_self m')⟩).JplusFinset p).Nonempty :=
      ⟨p, by simp [FiniteCausalPoset.JplusFinset,
        (c ⟨m', Nat.lt_succ_of_lt (Nat.lt_succ_self m')⟩).refl p]⟩
    -- Step bound: dH(c m', c m'+1) ≤ 1
    have hlast : FinsetMetric.discreteHausdorff (boundedDist (n := n) adj)
        ((c ⟨m', Nat.lt_succ_of_lt (Nat.lt_succ_self m')⟩).JplusFinset p)
        ((c ⟨m' + 1, Nat.lt_succ_self (m' + 1)⟩).JplusFinset p) ≤ 1 :=
      hs ⟨m', Nat.lt_succ_self m'⟩
    -- IH bound: dH(c 0, c m') ≤ m'
    have hprev : FinsetMetric.discreteHausdorff (boundedDist (n := n) adj)
        ((c ⟨0, Nat.succ_pos (m' + 1)⟩).JplusFinset p)
        ((c ⟨m', Nat.lt_succ_of_lt (Nat.lt_succ_self m')⟩).JplusFinset p) ≤ (m' : ℝ) := by
      have hstep' : ∀ i : Fin m',
          FinsetMetric.discreteHausdorff (boundedDist (n := n) adj)
            ((c (Fin.castSucc (Fin.castSucc i))).JplusFinset p)
            ((c (Fin.castSucc i).succ).JplusFinset p) ≤ 1 :=
        fun i => hs (Fin.castSucc i)
      have h := ih (fun i => c (Fin.castSucc i)) hstep'
      convert h using 2
    -- Triangle: dH(c 0, c m'+1) ≤ dH(c 0, c m') + dH(c m', c m'+1)
    have htri := FinsetMetric.discreteHausdorff_triangle
        (boundedDist (n := n) adj)
        (fun a b c => GraphDistance.boundedDist_triangle adj a b c)
        (fun a b => GraphDistance.boundedDist_nonneg adj a b)
        hmid
        ((c ⟨0, Nat.succ_pos (m' + 1)⟩).JplusFinset p)
        ((c ⟨m' + 1, Nat.lt_succ_self (m' + 1)⟩).JplusFinset p)
    have hcast : (m' : ℝ) + 1 = ((m' + 1 : ℕ) : ℝ) := by
      simp [Nat.cast_add, Nat.cast_one]
    linarith [hcast]

/-- **A.3**: For a chain of `k+1` finite causal posets each connected to the next
by a single-edge perturbation (Hausdorff distance ≤ 1 under fixed adjacency `adj`),
the total Hausdorff distance from the first to the last future set is ≤ k. -/
lemma jplus_hausdorff_le_chain
    (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (k : ℕ)
    (chain : Fin (k + 1) → FiniteCausalPoset n)
    (p : Fin n)
    (hstep : ∀ i : Fin k,
        FinsetMetric.discreteHausdorff (boundedDist (n := n) adj)
          ((chain (Fin.castSucc i)).JplusFinset p)
          ((chain i.succ).JplusFinset p) ≤ 1) :
    FinsetMetric.discreteHausdorff (boundedDist (n := n) adj)
      ((chain ⟨0, Nat.succ_pos k⟩).JplusFinset p)
      ((chain ⟨k, Nat.lt_succ_self k⟩).JplusFinset p) ≤ (k : ℝ) :=
  jplus_hausdorff_le_chain_aux adj p k chain hstep

/-! ## A.4 — k-edge Hausdorff bound for subgraph pairs -/

/-- Generalized single-step bound for abstract decidable relations.
If `relP` and `relQ` agree on every pair except `(u,v)` — present in `relP`,
absent in `relQ` — and `adj v u`, and `relQ p p` (reflexivity at `p`),
then `dH(adj)(𝒥⁺(relP,p), 𝒥⁺(relQ,p)) ≤ 1`. -/
private lemma jFuture_hausdorff_le_one_of_edge_adj
    (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (relP relQ : Fin n → Fin n → Prop) [DecidableRel relP] [DecidableRel relQ]
    (u v : Fin n)
    (hPQ : ∀ a b : Fin n, ¬(a = u ∧ b = v) → (relP a b ↔ relQ a b))
    (hPuv : relP u v) (hQuv : ¬ relQ u v)
    (hadjvu : adj v u)
    (hreflQ : relQ p p) :
    FinsetMetric.discreteHausdorff
        (GraphDistance.boundedDist (n := n) adj)
        (Finset.univ.filter (relP p ·)) (Finset.univ.filter (relQ p ·)) ≤ 1 := by
  classical
  refine FinsetMetric.discreteHausdorff_le_of_forall_exists
      (d := GraphDistance.boundedDist adj) (C := 1) (by norm_num) _ _ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    by_cases hQpq : relQ p q
    · exact ⟨q, by simp [hQpq], by simp [GraphDistance.boundedDist_self]⟩
    · have hpq : p = u ∧ q = v := by
        by_contra hne; exact hQpq ((hPQ p q hne).mp hq)
      obtain ⟨rfl, rfl⟩ := hpq
      exact ⟨p, by simp [hreflQ], GraphDistance.boundedDist_le_one_of_adj adj hadjvu⟩
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    have hPpq : relP p q := by
      by_cases hpq : p = u ∧ q = v
      · exact hpq.1 ▸ hpq.2 ▸ hPuv
      · exact (hPQ p q hpq).mpr hq
    exact ⟨q, by simp [hPpq], by simp [GraphDistance.boundedDist_self]⟩

/-- Auxiliary induction for A.4. -/
private lemma jFuture_hausdorff_diff_le_aux
    (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (Q : FiniteCausalPoset n) (p : Fin n) :
    ∀ (k : ℕ) (relP : Fin n → Fin n → Prop) [DecidableRel relP],
      relP p p →
      (∀ a b, Q.rel a b → relP a b) →
      (∀ a b, relP a b → adj b a) →
      ((Finset.univ : Finset (Fin n × Fin n)).filter
          (fun e : Fin n × Fin n => relP e.1 e.2 ∧ ¬ Q.rel e.1 e.2)).card ≤ k →
      FinsetMetric.discreteHausdorff (GraphDistance.boundedDist (n := n) adj)
          (Finset.univ.filter (relP p ·)) (Finset.univ.filter (Q.rel p ·)) ≤ (k : ℝ) := by
  intro k
  induction k with
  | zero =>
    intro relP _ hreflP hQP hadjP hcard
    simp only [Nat.cast_zero]
    have hempty : (Finset.univ : Finset (Fin n × Fin n)).filter
        (fun e : Fin n × Fin n => relP e.1 e.2 ∧ ¬ Q.rel e.1 e.2) = ∅ :=
      Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    have heq : ∀ a b, relP a b ↔ Q.rel a b := fun a b =>
      ⟨fun h => by
          by_contra hq
          have hmem : (a, b) ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
              (fun e : Fin n × Fin n => relP e.1 e.2 ∧ ¬ Q.rel e.1 e.2) :=
            Finset.mem_filter.mpr ⟨by simp, h, hq⟩
          rw [hempty] at hmem
          exact absurd hmem (by simp),
       hQP a b⟩
    have hJeq : Finset.univ.filter (relP p ·) = Finset.univ.filter (Q.rel p ·) := by
      ext q; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact heq p q
    rw [hJeq]
    apply FinsetMetric.discreteHausdorff_le_of_forall_exists (hC := le_refl 0)
    · intro a ha; exact ⟨a, ha, by simp [GraphDistance.boundedDist_self]⟩
    · intro b hb; exact ⟨b, hb, by simp [GraphDistance.boundedDist_self]⟩
  | succ k' ih =>
    intro relP _ hreflP hQP hadjP hcard
    set diff := (Finset.univ : Finset (Fin n × Fin n)).filter
        (fun e : Fin n × Fin n => relP e.1 e.2 ∧ ¬ Q.rel e.1 e.2) with hdiff_def
    by_cases hempty : diff.card = 0
    · have h0 := ih relP hreflP hQP hadjP
            (le_trans (hdiff_def ▸ Nat.le_zero.mpr hempty) (Nat.zero_le k'))
      exact le_trans h0 (by exact_mod_cast Nat.le_succ k')
    · obtain ⟨⟨u, v⟩, hmem⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hempty)
      simp only [hdiff_def, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      have hPuv : relP u v := hmem.1
      have hQuv : ¬ Q.rel u v := hmem.2
      have huv : u ≠ v := fun heq => hQuv (heq ▸ Q.refl v)
      let relP' : Fin n → Fin n → Prop := fun a b =>
        if a = u ∧ b = v then False else relP a b
      haveI : DecidableRel relP' := fun a b =>
        if h : a = u ∧ b = v then
          isFalse (by simp only [relP', h, and_self, ↓reduceIte]; exact fun hf => hf)
        else decidable_of_iff (relP a b) (by simp only [relP', if_neg h])
      have hreflP' : relP' p p := by
        have hne : ¬(p = u ∧ p = v) := fun ⟨ha, hb⟩ => huv (ha.symm.trans hb)
        simp only [relP', if_neg hne]
        exact hreflP
      have hQP' : ∀ a b, Q.rel a b → relP' a b := fun a b hq => by
        simp only [relP']
        by_cases h1 : a = u ∧ b = v
        · exact absurd (h1.1 ▸ h1.2 ▸ hq) hQuv
        · simp only [if_neg h1]; exact hQP a b hq
      have hadjP' : ∀ a b, relP' a b → adj b a := fun a b h => by
        have hPab : relP a b := by
          by_cases h1 : a = u ∧ b = v
          · simp only [relP', if_pos h1] at h
          · simp only [relP', if_neg h1] at h; exact h
        exact hadjP a b hPab
      have hmem_uv : (u, v) ∈ diff := by
        simp only [hdiff_def, Finset.mem_filter, Finset.mem_univ, true_and, hPuv, hQuv,
          not_false_eq_true, and_self]
      have hdiff' :
          ((Finset.univ : Finset (Fin n × Fin n)).filter
              (fun e : Fin n × Fin n => relP' e.1 e.2 ∧ ¬ Q.rel e.1 e.2)).card ≤ k' := by
        set diff' := (Finset.univ : Finset (Fin n × Fin n)).filter
            (fun e : Fin n × Fin n => relP' e.1 e.2 ∧ ¬ Q.rel e.1 e.2) with hdiff'_def
        have hsub : diff' ⊆ diff.erase (u, v) := by
          intro ⟨a, b⟩ hmem'
          simp only [hdiff'_def, Finset.mem_filter, Finset.mem_univ, true_and] at hmem'
          obtain ⟨hP'ab, hQab⟩ := hmem'
          rw [Finset.mem_erase]
          constructor
          · intro heq
            obtain ⟨ha, hb⟩ := Prod.mk.inj heq; subst ha; subst hb
            simp only [relP', and_self, ↓reduceIte] at hP'ab
          · simp only [hdiff_def, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨?_, hQab⟩
            by_cases h1 : a = u ∧ b = v
            · simp only [relP', if_pos h1] at hP'ab
            · simp only [relP', if_neg h1] at hP'ab; exact hP'ab
        have hle := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hmem_uv] at hle
        omega
      have hIH := ih relP' hreflP' hQP' hadjP' hdiff'
      have hstep : FinsetMetric.discreteHausdorff (GraphDistance.boundedDist (n := n) adj)
          (Finset.univ.filter (relP p ·)) (Finset.univ.filter (relP' p ·)) ≤ 1 :=
        jFuture_hausdorff_le_one_of_edge_adj adj relP relP' u v
          (fun a b hne => by simp only [relP', if_neg hne])
          hPuv
          (by show ¬ relP' u v; simp [relP'])
          (hadjP u v hPuv)
          hreflP'
      have hmid : (Finset.univ.filter (relP' p ·)).Nonempty :=
        ⟨p, by simp [hreflP']⟩
      have htri := FinsetMetric.discreteHausdorff_triangle
          (GraphDistance.boundedDist (n := n) adj)
          (fun a b c => GraphDistance.boundedDist_triangle adj a b c)
          (fun a b => GraphDistance.boundedDist_nonneg adj a b)
          hmid
          (Finset.univ.filter (relP p ·)) (Finset.univ.filter (Q.rel p ·))
      have hcast : (k' : ℝ) + 1 = ((k' + 1 : ℕ) : ℝ) := by
        simp [Nat.cast_add, Nat.cast_one]
      linarith [htri, hstep, hIH, hcast]

/-- **A.4 — k-edge Hausdorff bound**: If `Q ⊆ P` (as FiniteCausalPosets) and
`adj` contains all reversed edges of `P` (`P.rel a b → adj b a`), then

  `dH(adj)(J⁺(P, p), J⁺(Q, p)) ≤ |{(a,b) : P.rel a b ∧ ¬Q.rel a b}|`.

Corollary with `adj a b := P.rel a b ∨ P.rel b a`: removing k edges from P
moves the causal future by at most k steps in the Hausdorff sense. -/
theorem jplus_hausdorff_le_card_diff_of_subgraph
    (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (P Q : FiniteCausalPoset n)
    (hQP : ∀ a b, Q.rel a b → P.rel a b)
    (hadjP : ∀ a b, P.rel a b → adj b a)
    (p : Fin n) :
    FinsetMetric.discreteHausdorff (GraphDistance.boundedDist (n := n) adj)
        (P.JplusFinset p) (Q.JplusFinset p) ≤
    ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun e : Fin n × Fin n => P.rel e.1 e.2 ∧ ¬ Q.rel e.1 e.2)).card := by
  simp only [FiniteCausalPoset.JplusFinset]
  exact_mod_cast jFuture_hausdorff_diff_le_aux adj Q p _ P.rel (P.refl p) hQP hadjP le_rfl

end FiniteCausalPoset

end AqeiBridge
