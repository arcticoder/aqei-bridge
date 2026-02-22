import Mathlib.Data.Finsupp.Basic

import AqeiBridge.DiscreteHomologyProxy

/-!
# H₁ = 0 stability under edge removal

This file proves that the trivial 1-cycle space (`Z₁ = 0`, i.e., `dimH₁ = 0`)
is preserved under subgraph inclusion (edge removal). Concretely, if `M₂` has no
1-cycles and `M₁ ⊆ M₂` (every edge of `M₁` is also in `M₂`), then `M₁` also
has no 1-cycles.

This formalizes `h1_stable_small_pert` from the aqei-bridge TODO list. The
empirically-observed 100% H₁ = 0 invariance (aqei-numerical-validation, 100
trials, ε ≤ 0.3) is captured precisely: AQEI-admissible perturbations in the
discrete causal graph model correspond to *removing* causal edges (restricting
the set of admissible causal connections), so the subgraph condition applies.

## Main results

- `Edge.ext'`: two edges are equal iff they have the same source and destination.
- `mapEdge_injective`: `mapEdge f hf` is injective when `f : Pt → Pt` is.
- `push1_apply_mapEdge`: evaluating `push1 f hf x` at `mapEdge f hf e` recovers
  the `e`-coefficient of `x` (coefficient extraction identity).
- `push1_injective`: `push1 f hf` is injective when `f` is injective.
- `Z1_eq_bot_of_subgraph`: `Z₁(M₁) = ⊥` follows from `Z₁(M₂) = ⊥` when `M₁ ⊆ M₂`.
- `h1_stable_small_pert`: the formal `h1_stable_small_pert` statement.
-/

namespace AqeiBridge

namespace DiscreteSpacetime

variable {Pt : Type} [DecidableEq Pt]
variable {R : Type} [CommRing R]
variable {M M₁ M₂ : DiscreteSpacetime Pt}

/-!
## Edge extensionality
-/

/-- Two edges are equal if and only if they have the same source and destination.
The proof field `ok` is in `Prop` and is equal by proof irrelevance. -/
theorem Edge.ext_iff {e e' : Edge M} :
    e = e' ↔ e.src = e'.src ∧ e.dst = e'.dst := by
  constructor
  · intro h; exact ⟨congrArg Edge.src h, congrArg Edge.dst h⟩
  · intro ⟨hs, hd⟩
    obtain ⟨s, d, ok⟩ := e
    obtain ⟨s', d', ok'⟩ := e'
    simp only at hs hd
    subst hs; subst hd
    rfl

/-- Two edges are equal when they have the same source and destination. -/
theorem Edge.ext' {e e' : Edge M}
    (hs : e.src = e'.src) (hd : e.dst = e'.dst) : e = e' :=
  Edge.ext_iff.mpr ⟨hs, hd⟩

/-!
## Injectivity of `mapEdge`
-/

/-- `mapEdge f hf` is injective when the vertex map `f` is injective. -/
theorem mapEdge_injective {f : Pt → Pt} (hf : EdgeHom M₁ M₂ f)
    (hfinj : Function.Injective f) :
    Function.Injective (mapEdge (M₁ := M₁) (M₂ := M₂) f hf) := by
  intro e e' heq
  exact Edge.ext'
    (hfinj (congrArg Edge.src heq))
    (hfinj (congrArg Edge.dst heq))

/-!
## Coefficient extraction for `push1`
-/

/-- Evaluating `push1 f hf x` at `mapEdge f hf e` recovers the `e`-coefficient
of `x`. This is the key identity for proving injectivity of `push1`. -/
theorem push1_apply_mapEdge {f : Pt → Pt} (hf : EdgeHom M₁ M₂ f)
    (hfinj : Function.Injective f) (x : Edge M₁ →₀ R) (e : Edge M₁) :
    (push1 (M₁ := M₁) (M₂ := M₂) (R := R) f hf x)
        (mapEdge (M₁ := M₁) (M₂ := M₂) f hf e) = x e := by
  refine Finsupp.induction x ?_ ?_
  · simp
  · intro e' r y _ _ ihy
    -- Key: mapEdge injectivity means the condition `mapEdge e' = mapEdge e` ↔ `e' = e`
    have hmapedge_eq :
        (mapEdge (M₁ := M₁) (M₂ := M₂) f hf e' =
          mapEdge (M₁ := M₁) (M₂ := M₂) f hf e) = (e' = e) :=
      propext (mapEdge_injective hf hfinj).eq_iff
    -- Expand push1 and simplify using the rewrite
    simp only [map_add, push1_single, Finsupp.add_apply, Finsupp.single_apply,
      hmapedge_eq, ihy]

/-!
## Injectivity of `push1`
-/

/-- `push1 f hf` is injective when the vertex map `f` is injective.

**Proof:** Use `push1_apply_mapEdge` to extract each coefficient: for any `e`,
`(push1 f hf x)(mapEdge f hf e) = x e`. If `push1 f hf x = push1 f hf y`,
evaluating at `mapEdge f hf e` gives `x e = y e` for all `e`, hence `x = y`. -/
theorem push1_injective {f : Pt → Pt} (hf : EdgeHom M₁ M₂ f)
    (hfinj : Function.Injective f) :
    Function.Injective (push1 (M₁ := M₁) (M₂ := M₂) (R := R) f hf) := by
  intro x y hxy
  apply Finsupp.ext
  intro e'
  have h := congr_arg
    (fun (φ : Edge M₂ →₀ R) => φ (mapEdge (M₁ := M₁) (M₂ := M₂) f hf e')) hxy
  simp only [push1_apply_mapEdge hf hfinj] at h
  exact h

/-!
## H₁ = 0 stability under subgraph inclusion
-/

/-- `Z₁ = 0` is monotone under subgraph inclusion.

If `M₁ ⊆ M₂` (every edge of `M₁` is also in `M₂`, witnessed by
`hsub : EdgeHom M₁ M₂ id`) and `Z₁(M₂, R) = 0` (no 1-cycles in `M₂`), then
`Z₁(M₁, R) = 0` (no 1-cycles in `M₁`).

**Proof sketch:** Any cycle `z` in `M₁` can be pushed forward via the identity
map to a chain in `M₂` that is still a cycle (by `push1_mem_Z1`). Since
`Z₁(M₂) = 0`, the push is zero. By injectivity of `push1 id` (the identity
is injective), `z = 0`. -/
theorem Z1_eq_bot_of_subgraph (hsub : EdgeHom M₁ M₂ id)
    (h0 : Z1 (M := M₂) (R := R) = ⊥) :
    Z1 (M := M₁) (R := R) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Submodule.mem_bot]
  -- push1 id hsub z is in Z1 M₂
  have hpush := push1_mem_Z1 (M₁ := M₁) (M₂ := M₂) (R := R) id hsub hz
  -- Z1 M₂ = ⊥ so push1 id hsub z = 0
  rw [h0, Submodule.mem_bot] at hpush
  -- Rewrite: 0 = push1 id hsub 0 (by linearity)
  rw [← map_zero (push1 (M₁ := M₁) (M₂ := M₂) (R := R) id hsub)] at hpush
  -- Apply injectivity of push1 id (since id is injective)
  exact push1_injective (R := R) hsub Function.injective_id hpush

/-!
## Formal analogue of `h1_stable_small_pert`
-/

/-- The first homology is trivial: `dimH₁ = 0` (stated over ℤ).

In the discrete causal graph model, this means the graph is acyclic (a forest). -/
def dimH1IsZero (M : DiscreteSpacetime Pt) : Prop :=
  Z1 (M := M) (R := ℤ) = ⊥

/-- **H₁ = 0 is stable under edge removal.**

If `P` has no 1-cycles (`dimH1IsZero P`) and `P'` is a subgraph of `P`
(`EdgeHom P' P id`), then `P'` also has no 1-cycles (`dimH1IsZero P'`).

**Connection to `aqei-numerical-validation`:** In 100 random Erdős-Rényi graph
trials with ε ≤ 0.3, H₁ = 0 invariance was observed 100% of the time. This
theorem provides the exact formal reason: removing edges from an acyclic graph
(forest) yields a forest.

The `ε`-ball condition from the empirical formulation is subsumed by `hsub`:
for any fraction of edges removed, as long as the result is a subgraph of the
original, acyclicity is preserved. -/
theorem h1_stable_small_pert
    (P : DiscreteSpacetime Pt) (h0 : dimH1IsZero P)
    (P' : DiscreteSpacetime Pt) (hsub : EdgeHom P' P id) :
    dimH1IsZero P' :=
  Z1_eq_bot_of_subgraph (R := ℤ) hsub h0

end DiscreteSpacetime

end AqeiBridge
