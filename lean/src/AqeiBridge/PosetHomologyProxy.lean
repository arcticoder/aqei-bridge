import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.Ker

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.LeftHomology

import AqeiBridge.CausalPoset

open CategoryTheory Limits

/-!
# Poset homology proxy (via Mathlib chain complexes)

This file packages the existing “1-cycle boundary” idea into a genuine
`ChainComplex (ModuleCat R) ℕ` so that Mathlib’s `homology` API can be used.

It is intentionally *low-degree*: we only build `C₀` and `C₁` and set `Cₙ = 0`
for `n ≥ 2`. This keeps the development CI-safe while providing a stable
interface for future refinements (e.g. the full order complex).

For a `CausalPoset P`:
- `C₀`: formal `R`-linear combinations of points
- `C₁`: formal `R`-linear combinations of strict edges `p < q`
- `∂₁(p<q) = q - p`

Then `H₁` is available as `posetChainComplex.homology 1`.
-/

namespace AqeiBridge

namespace CausalPoset

/-- A strict edge in a causal preorder (using the `lt` from the `Preorder` instance). -/
structure Edge (P : AqeiBridge.CausalPoset) where
  src : P.Pt
  dst : P.Pt
  ok : src < dst

section Boundary

variable (P : AqeiBridge.CausalPoset)
variable (R : Type) [CommRing R]
variable [DecidableEq P.Pt]

/-- Boundary of a single strict edge: `∂(p<q) = q - p`. -/
noncomputable def edgeBoundary (e : Edge P) : P.Pt →₀ R :=
  Finsupp.single e.dst (1 : R) - Finsupp.single e.src (1 : R)

/-- The `R`-linear map sending `r` to `r • ∂(e)`. -/
noncomputable def edgeBoundaryMap (e : Edge P) : R →ₗ[R] (P.Pt →₀ R) where
  toFun r := r • edgeBoundary (P := P) (R := R) e
  map_add' a b := by simp [add_smul]
  map_smul' a b := by simp [mul_smul]

/-- Incidence boundary `∂₁ : C₁ → C₀`. -/
noncomputable def boundary1 : (Edge P →₀ R) →ₗ[R] (P.Pt →₀ R) :=
  Finsupp.lsum R (fun e => edgeBoundaryMap (P := P) (R := R) e)

/-- The space of 1-cycles `Z₁ := ker ∂₁`. -/
noncomputable def Z1 : Submodule R (Edge P →₀ R) :=
  LinearMap.ker (boundary1 (P := P) (R := R))

end Boundary

section Functorial

variable {P Q : AqeiBridge.CausalPoset}
variable (R : Type) [CommRing R]

/-- A map of causal posets that preserves strict edges (`<`) and hence sends strict edges to strict
edges.

We use `<` from the `Preorder` instance on `CausalPoset.Pt`. -/
def EdgeHom (P Q : AqeiBridge.CausalPoset) (f : P.Pt → Q.Pt) : Prop :=
  ∀ ⦃p q : P.Pt⦄, p < q → f p < f q

noncomputable def mapEdge (P Q : AqeiBridge.CausalPoset) (f : P.Pt → Q.Pt) (hf : EdgeHom P Q f) :
    Edge P → Edge Q :=
  fun e => ⟨f e.src, f e.dst, hf e.ok⟩

/-- Pushforward of `0`-chains along a point-map. -/
noncomputable def push0 (P Q : AqeiBridge.CausalPoset) (f : P.Pt → Q.Pt) :
    (P.Pt →₀ R) →ₗ[R] (Q.Pt →₀ R) := by
  classical
  refine Finsupp.lsum R (fun p => ?_)
  refine
    { toFun := fun r => Finsupp.single (f p) r
      map_add' := by intro a b; simp
      map_smul' := by intro a b; simp }

@[simp]
theorem push0_single (P Q : AqeiBridge.CausalPoset) (f : P.Pt → Q.Pt) (p : P.Pt) (r : R) :
    push0 (P := P) (Q := Q) (R := R) f (Finsupp.single p r) = Finsupp.single (f p) r := by
  classical
  simp [push0]

/-- Pushforward of `1`-chains along an edge-homomorphism. -/
noncomputable def push1 (P Q : AqeiBridge.CausalPoset) (f : P.Pt → Q.Pt) (hf : EdgeHom P Q f) :
    (Edge P →₀ R) →ₗ[R] (Edge Q →₀ R) := by
  classical
  refine Finsupp.lsum R (fun e => ?_)
  refine
    { toFun := fun r => Finsupp.single (mapEdge (P := P) (Q := Q) f hf e) r
      map_add' := by intro a b; simp
      map_smul' := by intro a b; simp }

@[simp]
theorem push1_single (P Q : AqeiBridge.CausalPoset) (f : P.Pt → Q.Pt) (hf : EdgeHom P Q f)
    (e : Edge P) (r : R) :
    push1 (P := P) (Q := Q) (R := R) f hf (Finsupp.single e r)
      = Finsupp.single (mapEdge (P := P) (Q := Q) f hf e) r := by
  classical
  simp [push1]

@[simp]
theorem boundary1_single (P : AqeiBridge.CausalPoset) [DecidableEq P.Pt] (e : Edge P) (r : R) :
    boundary1 (P := P) (R := R) (Finsupp.single e r) = r • edgeBoundary (P := P) (R := R) e := by
  classical
  simp [boundary1, edgeBoundaryMap]

@[simp]
theorem push0_edgeBoundary (P Q : AqeiBridge.CausalPoset) [DecidableEq P.Pt] [DecidableEq Q.Pt]
    (f : P.Pt → Q.Pt) (hf : EdgeHom P Q f) (e : Edge P) :
    push0 (P := P) (Q := Q) (R := R) f (edgeBoundary (P := P) (R := R) e)
      = edgeBoundary (P := Q) (R := R) (mapEdge (P := P) (Q := Q) f hf e) := by
  classical
  simp [edgeBoundary, mapEdge, push0_single, sub_eq_add_neg]

/-- Naturality of the degree-1 boundary under strict-edge-preserving maps. -/
theorem boundary1_natural (P Q : AqeiBridge.CausalPoset) [DecidableEq P.Pt] [DecidableEq Q.Pt]
    (f : P.Pt → Q.Pt) (hf : EdgeHom P Q f) :
    (push0 (P := P) (Q := Q) (R := R) f).comp (boundary1 (P := P) (R := R))
      = (boundary1 (P := Q) (R := R)).comp (push1 (P := P) (Q := Q) (R := R) f hf) := by
  classical
  -- Prove by extensionality on `1`-chains, then induction on finite support.
  apply LinearMap.ext
  intro x
  refine Finsupp.induction x ?_ ?_
  · simp [LinearMap.comp_apply]
  · intro e r x he hr0 hx
    have hsingle :
        push0 (P := P) (Q := Q) (R := R) f (boundary1 (P := P) (R := R) (Finsupp.single e r))
          = boundary1 (P := Q) (R := R)
              (push1 (P := P) (Q := Q) (R := R) f hf (Finsupp.single e r)) := by
      -- Compute both sides on a generator using the boundary formula.
      simp [boundary1_single, push0_edgeBoundary (P := P) (Q := Q) (R := R) f hf,
        push1_single]
    -- Extend from generators using additivity.
    simpa [LinearMap.comp_apply, map_add, hx, hsingle,
      push0_edgeBoundary (P := P) (Q := Q) (R := R) f hf]

/-- Pushforward of `1`-cycles: strict-edge-preserving maps send `Z₁` to `Z₁`. -/
theorem push1_mem_Z1 (P Q : AqeiBridge.CausalPoset) [DecidableEq P.Pt] [DecidableEq Q.Pt]
    (f : P.Pt → Q.Pt) (hf : EdgeHom P Q f) (x : Edge P →₀ R)
    (hx : x ∈ Z1 (P := P) (R := R)) :
    push1 (P := P) (Q := Q) (R := R) f hf x ∈ Z1 (P := Q) (R := R) := by
  classical
  -- Unfold membership in the kernel and use boundary naturality.
  have hx0 : boundary1 (P := P) (R := R) x = 0 := hx
  show boundary1 (P := Q) (R := R) (push1 (P := P) (Q := Q) (R := R) f hf x) = 0
  have hNat := congrArg (fun g => g x) (boundary1_natural (P := P) (Q := Q) (R := R) f hf)
  -- `hNat` is an equality in `C₀`; rewrite with `hx0`.
  simpa [LinearMap.comp_apply, hx0] using hNat.symm

/-- The induced map on 1-cycles `Z₁` from an edge-preserving map. -/
noncomputable def pushZ1 (P Q : AqeiBridge.CausalPoset) [DecidableEq P.Pt] [DecidableEq Q.Pt]
    (f : P.Pt → Q.Pt) (hf : EdgeHom P Q f) :
    Z1 (P := P) (R := R) →ₗ[R] Z1 (P := Q) (R := R) where
  toFun x :=
    ⟨push1 (P := P) (Q := Q) (R := R) f hf x.1,
      push1_mem_Z1 (P := P) (Q := Q) (R := R) f hf x.1 x.2⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' a x := by
    apply Subtype.ext
    simp

/-- An isomorphism of causal posets at the level of strict edges.

This is intentionally minimal: we only assume the point-equivalence preserves strict edges in
both directions. -/
structure EdgeIso (P Q : AqeiBridge.CausalPoset) where
  toEquiv : P.Pt ≃ Q.Pt
  map_lt' : EdgeHom P Q toEquiv
  inv_map_lt' : EdgeHom Q P toEquiv.symm

attribute [simp] EdgeIso.toEquiv

@[simp]
theorem mapEdge_left_inv {P Q : AqeiBridge.CausalPoset} (e : Edge P) (f : P.Pt ≃ Q.Pt)
    (hf : EdgeHom P Q f) (hg : EdgeHom Q P f.symm) :
  mapEdge (P := Q) (Q := P) f.symm hg (mapEdge (P := P) (Q := Q) f hf e) = e := by
  cases e with
  | mk src dst ok =>
  -- Reduce to equality of records with identical data fields (proof fields are in `Prop`).
  simp [mapEdge]

@[simp]
theorem mapEdge_right_inv {P Q : AqeiBridge.CausalPoset} (e : Edge Q) (f : P.Pt ≃ Q.Pt)
    (hf : EdgeHom P Q f) (hg : EdgeHom Q P f.symm) :
  mapEdge (P := P) (Q := Q) f hf (mapEdge (P := Q) (Q := P) f.symm hg e) = e := by
  cases e with
  | mk src dst ok =>
  simp [mapEdge]

theorem push1_left_inv {P Q : AqeiBridge.CausalPoset} (f : P.Pt ≃ Q.Pt)
    (hf : EdgeHom P Q f) (hg : EdgeHom Q P f.symm) (x : Edge P →₀ R) :
    push1 (P := Q) (Q := P) (R := R) f.symm hg
        (push1 (P := P) (Q := Q) (R := R) f hf x) = x := by
  classical
  refine Finsupp.induction x ?_ ?_
  · simp
  · intro e r x he hr0 hx
    -- Pushforward respects addition, and on generators reduces via `mapEdge_left_inv`.
    simp [hx, push1_single, mapEdge_left_inv (e := e) (f := f) (hf := hf) (hg := hg),
      he, add_assoc, add_left_comm, add_comm]

theorem push1_right_inv {P Q : AqeiBridge.CausalPoset} (f : P.Pt ≃ Q.Pt)
    (hf : EdgeHom P Q f) (hg : EdgeHom Q P f.symm) (x : Edge Q →₀ R) :
    push1 (P := P) (Q := Q) (R := R) f hf
        (push1 (P := Q) (Q := P) (R := R) f.symm hg x) = x := by
  classical
  refine Finsupp.induction x ?_ ?_
  · simp
  · intro e r x he hr0 hx
    simp [hx, push1_single, mapEdge_right_inv (e := e) (f := f) (hf := hf) (hg := hg),
      he, add_assoc, add_left_comm, add_comm]

/-- `Z₁` is invariant under strict-edge isomorphisms. -/
noncomputable def pushZ1Equiv (P Q : AqeiBridge.CausalPoset) [DecidableEq P.Pt] [DecidableEq Q.Pt]
    (e : EdgeIso P Q) :
    Z1 (P := P) (R := R) ≃ₗ[R] Z1 (P := Q) (R := R) where
  toLinearMap := pushZ1 (P := P) (Q := Q) (R := R) e.toEquiv e.map_lt'
  invFun := (pushZ1 (P := Q) (Q := P) (R := R) e.toEquiv.symm e.inv_map_lt')
  left_inv x := by
    apply Subtype.ext
    simpa [pushZ1] using
      (push1_left_inv (R := R) (P := P) (Q := Q) e.toEquiv e.map_lt' e.inv_map_lt' x.1)
  right_inv x := by
    apply Subtype.ext
    simpa [pushZ1] using
      (push1_right_inv (R := R) (P := P) (Q := Q) e.toEquiv e.map_lt' e.inv_map_lt' x.1)

/-- The corresponding `ModuleCat` isomorphism between cycle modules. -/
noncomputable def Z1ModuleIso (P Q : AqeiBridge.CausalPoset) [DecidableEq P.Pt] [DecidableEq Q.Pt]
    (e : EdgeIso P Q) :
    ModuleCat.of R (Z1 (P := P) (R := R)) ≅ ModuleCat.of R (Z1 (P := Q) (R := R)) := by
  classical
  let eZ : Z1 (P := P) (R := R) ≃ₗ[R] Z1 (P := Q) (R := R) :=
    pushZ1Equiv (P := P) (Q := Q) (R := R) e
  refine
    { hom := ModuleCat.ofHom eZ.toLinearMap
      inv := ModuleCat.ofHom eZ.symm.toLinearMap
      hom_inv_id := by
        ext x
        simp [eZ]
      inv_hom_id := by
        ext x
        simp [eZ] }

end Functorial

section ChainComplex

variable (P : AqeiBridge.CausalPoset)
variable (R : Type) [CommRing R]
variable [DecidableEq P.Pt]

/-- The object part of the low-degree chain complex: `C₀`, `C₁`, and `0` above. -/
noncomputable def chainObj : ℕ → ModuleCat R
  | 0 => ModuleCat.of R (P.Pt →₀ R)
  | 1 => ModuleCat.of R (Edge P →₀ R)
  | _ + 2 => ModuleCat.of R PUnit

/-- The differentials of the low-degree chain complex. -/
noncomputable def chainD : ∀ n : ℕ, chainObj (P := P) (R := R) (n + 1) ⟶ chainObj (P := P) (R := R) n
  | 0 => ModuleCat.ofHom (boundary1 (P := P) (R := R))
  | 1 => 0
  | _ + 2 => 0

theorem chainD_squared (n : ℕ) :
  chainD (P := P) (R := R) (n + 1) ≫ chainD (P := P) (R := R) n = 0 := by
  cases n <;> simp [chainD, chainObj]

/-- A `ChainComplex` whose degree-1 cycles implement the poset 1-cycle proxy. -/
noncomputable abbrev posetChainComplex : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (chainObj (P := P) (R := R)) (chainD (P := P) (R := R))
    (by
      intro n
      simpa using (chainD_squared (P := P) (R := R) n))

@[simp]
theorem posetChainComplex_d_1_0 :
    (posetChainComplex (P := P) (R := R)).d 1 0 =
      ModuleCat.ofHom (boundary1 (P := P) (R := R)) := by
  -- `posetChainComplex` is built using `ChainComplex.of`, so `d 1 0` is definitional `chainD 0`.
  dsimp [posetChainComplex]
  simpa [chainD] using
    (ChainComplex.of_d (X := chainObj (P := P) (R := R)) (d := chainD (P := P) (R := R))
        (sq := by
          intro n
          simpa using (chainD_squared (P := P) (R := R) n))
        0)

@[simp]
theorem posetChainComplex_d_1_0_hom :
    ((posetChainComplex (P := P) (R := R)).d 1 0).hom =
      boundary1 (P := P) (R := R) := by
  simp [posetChainComplex_d_1_0 (P := P) (R := R)]

@[simp]
theorem posetChainComplex_d_2_1 :
    (posetChainComplex (P := P) (R := R)).d 2 1 = 0 := by
  dsimp [posetChainComplex]
  simpa [chainD] using
    (ChainComplex.of_d (X := chainObj (P := P) (R := R)) (d := chainD (P := P) (R := R))
        (sq := by
          intro n
          simpa using (chainD_squared (P := P) (R := R) n))
        1)

/-- The first homology object `H₁` of the low-degree proxy chain complex. -/
noncomputable abbrev H1 : ModuleCat R := (posetChainComplex (P := P) (R := R)).homology 1

section Bridge

/-- In the low-degree proxy chain complex, the degree-1 cycles coincide with the kernel-based
definition `Z1 := ker ∂₁`.

This is the formal bridge between the earlier `LinearMap.ker boundary1` proxy and Mathlib’s
`HomologicalComplex.cycles` API. -/
noncomputable def cycles1IsoZ1 :
    (posetChainComplex (P := P) (R := R)).cycles 1 ≅
      ModuleCat.of R (Z1 (P := P) (R := R)) := by
  let K : ChainComplex (ModuleCat R) ℕ := posetChainComplex (P := P) (R := R)

  -- Work with an explicit choice of predecessor/successor indices for degree `1`.
  have hrelPrev : (ComplexShape.down ℕ).Rel 2 1 :=
    ComplexShape.down_mk (α := ℕ) 2 1 (by simp)
  have hi : (ComplexShape.down ℕ).prev 1 = 2 :=
    (ComplexShape.down ℕ).prev_eq' hrelPrev
  have hrelNext : (ComplexShape.down ℕ).Rel 1 0 :=
    ComplexShape.down_mk (α := ℕ) 1 0 (by simp)
  have hk : (ComplexShape.down ℕ).next 1 = 0 :=
    (ComplexShape.down ℕ).next_eq' hrelNext

  -- `K.cycles 1` can be computed using the explicit short complex `K.sc' 2 1 0`.
  -- Then cycles are the kernel of the right map, i.e. `K.d 1 0`.
  refine
      (HomologicalComplex.cyclesIsoSc' (K := K) (i := 2) (j := 1) (k := 0) hi hk)
        ≪≫
        (by
          simpa using (ShortComplex.cyclesIsoKernel (S := K.sc' 2 1 0)))
        ≪≫
        ?_

  -- Translate categorical kernel ↔ linear-map kernel and rewrite to `Z1`.
  simpa [Z1, K, posetChainComplex_d_1_0_hom (P := P) (R := R)] using
    (ModuleCat.kernelIsoKer (K.d 1 0))

/-- In the low-degree proxy chain complex, the map `toCycles 2 1` is zero.

This is the core input for reducing `H₁` to `cycles 1`. -/
theorem toCycles_2_1_eq_zero :
    (posetChainComplex (P := P) (R := R)).toCycles 2 1 = 0 := by
  classical
  let K : ChainComplex (ModuleCat R) ℕ := posetChainComplex (P := P) (R := R)
  haveI : K.HasHomology 1 := by infer_instance
  -- Cancel against the mono `iCycles` and use the simp lemma `toCycles_i`.
  apply (cancel_mono (K.iCycles 1)).1
  simp [K, posetChainComplex_d_2_1 (P := P) (R := R)]

/-- In the low-degree proxy chain complex, `H₁` is isomorphic to the degree-1 cycles.

This uses the cokernel description of homology and the fact that `toCycles 2 1 = 0`. -/
noncomputable def H1IsoCycles1 :
    H1 (P := P) (R := R) ≅ (posetChainComplex (P := P) (R := R)).cycles 1 := by
  classical
  let K : ChainComplex (ModuleCat R) ℕ := posetChainComplex (P := P) (R := R)

  have hrelPrev : (ComplexShape.down ℕ).Rel 2 1 :=
    ComplexShape.down_mk (α := ℕ) 2 1 (by simp)
  have hi : (ComplexShape.down ℕ).prev 1 = 2 :=
    (ComplexShape.down ℕ).prev_eq' hrelPrev

  haveI : K.HasHomology 1 := by infer_instance
  have hToCycles : K.toCycles 2 1 = 0 := by
    simpa [K] using (toCycles_2_1_eq_zero (P := P) (R := R))

  haveI : HasCokernel (K.toCycles 2 1) := by infer_instance

  let ccHom : CokernelCofork (K.toCycles 2 1) :=
    CokernelCofork.ofπ (K.homologyπ 1) (K.toCycles_comp_homologyπ (i := 2) (j := 1))
  have hcHom : IsColimit ccHom := by
    simpa [ccHom] using (K.homologyIsCokernel (i := 2) (j := 1) hi)

  let ccCok : CokernelCofork (K.toCycles 2 1) :=
    Cofork.ofπ (cokernel.π (K.toCycles 2 1))
      ((cokernel.condition (K.toCycles 2 1)).trans zero_comp.symm)
  have hcCok : IsColimit ccCok := by
    simpa [ccCok] using (cokernelIsCokernel (K.toCycles 2 1))

  let isoHomCok : K.homology 1 ≅ cokernel (K.toCycles 2 1) := by
    simpa [ccHom, ccCok] using
      (CokernelCofork.mapIsoOfIsColimit (hf := hcHom) (hf' := hcCok)
        (Iso.refl (Arrow.mk (K.toCycles 2 1))))

  have isoCokCycles : cokernel (K.toCycles 2 1) ≅ K.cycles 1 := by
    simpa [hToCycles] using (cokernelZeroIsoTarget (X := K.X 2) (Y := K.cycles 1))

  simpa [H1, K] using (isoHomCok ≪≫ isoCokCycles)

/-- In the low-degree proxy chain complex, the incoming differential to degree `1` is zero.

As a result, `H₁` is (canonically) isomorphic to the degree-1 cycles, hence to `Z₁`.
-/
noncomputable def H1IsoZ1 :
    H1 (P := P) (R := R) ≅ ModuleCat.of R (Z1 (P := P) (R := R)) := by
  simpa using
    (H1IsoCycles1 (P := P) (R := R) ≪≫ cycles1IsoZ1 (P := P) (R := R))

end Bridge

end ChainComplex

section Invariance

variable {P Q : AqeiBridge.CausalPoset}
variable (R : Type) [CommRing R]
variable [DecidableEq P.Pt] [DecidableEq Q.Pt]

/-- Invariance of the proxy `H₁` under strict-edge isomorphisms.

This uses the bridge `H₁ ≅ Z₁` for the low-degree proxy chain complex. -/
noncomputable def H1IsoOfEdgeIso (e : EdgeIso P Q) :
    H1 (P := P) (R := R) ≅ H1 (P := Q) (R := R) := by
  -- `H1IsoZ1` is the proxy result for each poset; transport along `Z₁`.
  refine
    H1IsoZ1 (P := P) (R := R)
      ≪≫ Z1ModuleIso (P := P) (Q := Q) (R := R) e
      ≪≫ (H1IsoZ1 (P := Q) (R := R)).symm

end Invariance

end CausalPoset

end AqeiBridge
