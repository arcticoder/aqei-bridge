import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum

import AqeiBridge.OrderComplexProxy
import AqeiBridge.PosetHomologyProxy
import AqeiBridge.FiniteCausalPoset

/-!
# Bridge: OrderComplexProxy Z₁ ↪ PosetHomologyProxy Z₁

For a `FiniteCausalPoset n P`, the order-complex 1-cycle space `Z1_oc` embeds into the
PosetHomologyProxy 1-cycle space `Z1 (P.toCausalPoset)`.

## Main result

`Z1_oc_eq_bot_of_posethom` — if `Z1 (P.toCausalPoset) R = ⊥` (the PosetHomologyProxy
cycle space is trivial, i.e. no non-boundary 1-cycles), then `Z1_oc R P = ⊥` as well.

## Proof strategy

1. **Canonical injection** `OC1_to_edge : OC1 P → Edge (P.toCausalPoset)`:
   every element of `OC1 P` (a pair `(a, b)` with `a < b` in `Fin n` and `P.rel a b`)
   gives a strict edge `a < b` in the preorder `P.toCausalPoset` (using antisymmetry to
   discharge `¬ P.rel b a`).

2. **Boundary commutativity** `bdy1_eq_boundary1_mapDomain`:
   `boundary1 (mapDomain ι x) = bdy1 x`, so cycles in `Z1_oc` map to cycles in `Z1`.

3. **Injectivity transfer**: `mapDomain ι` is injective (since `ι` is), so a cycle in
   `Z1_oc` that maps to `0` in `Z1` must itself be `0`.

This ties the two cycle proxies together and shows that the PosetHomologyProxy invariant
is "at least as sensitive" as the OC invariant.
-/

namespace AqeiBridge
namespace OrderComplexBridge

open OrderComplexProxy

variable {n : ℕ} (P : FiniteCausalPoset n)

/-! ## Canonical injection OC1 → Edge (toCausalPoset) -/

/-- Every canonically-oriented OC1 edge is a strict edge in `P.toCausalPoset`.

  An element of `OC1 P` is a pair `(a, b)` with `a < b` in `Fin n` (natural order)
  and `P.rel a b`. By antisymmetry of `P`, if `P.rel b a` too then `a = b`,
  contradicting `a < b`. Hence `a < b` in the preorder `P.toCausalPoset`. -/
def OC1_to_edge (e : OC1 P) : CausalPoset.Edge (P.toCausalPoset) where
  src := e.1.1
  dst := e.1.2
  ok  := ⟨e.2.2, fun h => absurd (P.antisymm e.2.2 h) (Fin.ne_of_lt e.2.1)⟩

@[simp] lemma OC1_to_edge_src (e : OC1 P) : (OC1_to_edge P e).src = e.1.1 := rfl
@[simp] lemma OC1_to_edge_dst (e : OC1 P) : (OC1_to_edge P e).dst = e.1.2 := rfl

/-- The injection `OC1_to_edge` is injective: two OC1 edges are equal iff they have
the same source and destination. -/
lemma OC1_to_edge_injective : Function.Injective (OC1_to_edge P) := by
  intro e1 e2 h
  have ha : e1.1.1 = e2.1.1 := by
    have := congr_arg CausalPoset.Edge.src h; simp only [OC1_to_edge] at this; exact this
  have hb : e1.1.2 = e2.1.2 := by
    have := congr_arg CausalPoset.Edge.dst h; simp only [OC1_to_edge] at this; exact this
  exact Subtype.ext (Prod.ext ha hb)

variable (R : Type) [CommRing R]

/-! ## Boundary maps commute with the injection -/

/-- The boundary maps of the two proxies are compatible: applying `boundary1` to the
`Finsupp.mapDomain` of the injection equals `bdy1` evaluated directly.

  `boundary1 (mapDomain ι x) = bdy1 x`

Proof: reduce via `Finsupp.mapDomain_sum` to checking on single basis elements. -/
lemma bdy1_eq_boundary1_mapDomain (x : OC1 P →₀ R) :
    CausalPoset.boundary1 (P := P.toCausalPoset) (R := R)
      (Finsupp.mapDomain (OC1_to_edge P) x) =
    bdy1 R P x := by
  classical
  -- Induct on support of x; base 0 is trivial, step reduces to the singleton formula.
  refine Finsupp.induction x ?_ ?_
  · simp
  · intro e r y _ _ ih
    simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single, map_add, ih,
               CausalPoset.boundary1_single, CausalPoset.edgeBoundary,
               OC1_to_edge_src, OC1_to_edge_dst, bdy1_single]

/-! ## Main bridge theorem -/

/-- **Key bridge theorem**: if the PosetHomologyProxy 1-cycle space of `P.toCausalPoset`
is trivial (`Z1 = ⊥`), then the order-complex 1-cycle space `Z1_oc` of `P` is also
trivial.

This ties the two cycle proxies together: PosetHomologyProxy acyclicity implies OC
acyclicity. -/
theorem Z1_oc_eq_bot_of_posethom
    (hZ : CausalPoset.Z1 (P.toCausalPoset) R = ⊥) :
    Z1_oc R P = ⊥ := by
  classical
  rw [Submodule.eq_bot_iff]
  intro x hx
  -- hx : bdy1 R P x = 0  (i.e. x is a 1-cycle in OC proxy)
  rw [Z1_oc, LinearMap.mem_ker] at hx
  -- Map x into the PosetHomologyProxy cycle space
  have hmapZ : Finsupp.mapDomain (OC1_to_edge P) x ∈
      CausalPoset.Z1 (P.toCausalPoset) R := by
    rw [CausalPoset.Z1, LinearMap.mem_ker, bdy1_eq_boundary1_mapDomain]
    exact hx
  -- Z1 = ⊥, so the image is 0
  rw [hZ, Submodule.mem_bot] at hmapZ
  -- OC1_to_edge is injective, so mapDomain is injective, hence x = 0
  exact Finsupp.mapDomain_injective (OC1_to_edge_injective P)
    (hmapZ.trans (Finsupp.mapDomain_zero (f := OC1_to_edge P)).symm)

end OrderComplexBridge
end AqeiBridge
