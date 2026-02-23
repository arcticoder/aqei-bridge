import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Tactic

import AqeiBridge.FiniteCausalPoset

/-!
# Order complex chain complex (degrees 0-2)

  C2Oc --bdy2--> C1Oc --bdy1--> C0Oc

Boundary maps:
- bdy1 (a,b) = single b 1 - single a 1
- bdy2 (a,b,c) = single(b,c) 1 - single(a,c) 1 + single(a,b) 1

Key result: bdy1 . bdy2 = 0.
-/

namespace AqeiBridge
namespace OrderComplexProxy

variable {n : ℕ}

def OC1 (P : FiniteCausalPoset n) : Type :=
  {ab : Fin n × Fin n // ab.1 < ab.2 ∧ P.rel ab.1 ab.2}

instance (P : FiniteCausalPoset n) : DecidableEq (OC1 P) := Subtype.instDecidableEq

def OC2 (P : FiniteCausalPoset n) : Type :=
  {abc : Fin n × Fin n × Fin n //
    abc.1 < abc.2.1 ∧ abc.2.1 < abc.2.2 ∧
    P.rel abc.1 abc.2.1 ∧ P.rel abc.2.1 abc.2.2}

instance (P : FiniteCausalPoset n) : DecidableEq (OC2 P) := Subtype.instDecidableEq

-- t.2.1   : a < b
-- t.2.2.1 : b < c
-- t.2.2.2.1 : P.rel a b
-- t.2.2.2.2 : P.rel b c

def face01 (P : FiniteCausalPoset n) (t : OC2 P) : OC1 P :=
  ⟨(t.1.1, t.1.2.1), t.2.1, t.2.2.2.1⟩

def face12 (P : FiniteCausalPoset n) (t : OC2 P) : OC1 P :=
  ⟨(t.1.2.1, t.1.2.2), t.2.2.1, t.2.2.2.2⟩

def face02 (P : FiniteCausalPoset n) (t : OC2 P) : OC1 P :=
  ⟨(t.1.1, t.1.2.2), lt_trans t.2.1 t.2.2.1, P.trans t.2.2.2.1 t.2.2.2.2⟩

variable (R : Type) [CommRing R]

noncomputable def bdy1 (P : FiniteCausalPoset n) :
    (OC1 P →₀ R) →ₗ[R] (Fin n →₀ R) :=
  Finsupp.lsum R fun (e : OC1 P) =>
    { toFun    := fun r => r • (Finsupp.single e.1.2 1 - Finsupp.single e.1.1 1)
      map_add' := fun a b => by simp [add_smul]
      map_smul' := fun a b => by simp [mul_smul] }

@[simp]
theorem bdy1_single (P : FiniteCausalPoset n) (e : OC1 P) (r : R) :
    bdy1 R P (Finsupp.single e r) =
    r • (Finsupp.single e.1.2 1 - Finsupp.single e.1.1 1) := by
  simp [bdy1]

noncomputable def bdy2 (P : FiniteCausalPoset n) :
    (OC2 P →₀ R) →ₗ[R] (OC1 P →₀ R) :=
  Finsupp.lsum R fun (t : OC2 P) =>
    { toFun    := fun r => r •
         (Finsupp.single (face12 P t) 1 -
          Finsupp.single (face02 P t) 1 +
          Finsupp.single (face01 P t) 1)
      map_add' := fun a b => by rw [add_smul]
      map_smul' := fun a b => by simp [mul_smul] }

@[simp]
theorem bdy2_single (P : FiniteCausalPoset n) (t : OC2 P) (r : R) :
    bdy2 R P (Finsupp.single t r) = r •
       (Finsupp.single (face12 P t) 1 -
        Finsupp.single (face02 P t) 1 +
        Finsupp.single (face01 P t) 1) := by
  simp [bdy2]

lemma bdy1_comp_bdy2 (P : FiniteCausalPoset n) :
    (bdy1 R P).comp (bdy2 R P) = 0 := by
  apply Finsupp.lhom_ext
  intro (t : OC2 P) (r : R)
  simp only [LinearMap.comp_apply, bdy2_single, LinearMap.zero_apply]
  rw [map_smul (bdy1 R P)]
  suffices h : bdy1 R P
      (Finsupp.single (face12 P t) 1 -
       Finsupp.single (face02 P t) 1 +
       Finsupp.single (face01 P t) 1) = 0 by
    rw [h, smul_zero]
  rw [map_add, map_sub, bdy1_single, bdy1_single, bdy1_single]
  -- now: 1•(single c 1 - single b 1) - 1•(single c 1 - single a 1) + 1•(single b 1 - single a 1) = 0
  ext (i : Fin n)
  simp only [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.zero_apply,
             one_smul, Finsupp.single_apply, face01, face12, face02]
  split_ifs <;> ring

noncomputable def Z1_oc (P : FiniteCausalPoset n) : Submodule R (OC1 P →₀ R) :=
  LinearMap.ker (bdy1 R P)

noncomputable def B1_oc (P : FiniteCausalPoset n) : Submodule R (OC1 P →₀ R) :=
  LinearMap.range (bdy2 R P)

lemma B1_le_Z1 (P : FiniteCausalPoset n) : B1_oc R P ≤ Z1_oc R P := by
  intro x hx
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hx
  rw [← hc, Z1_oc, LinearMap.mem_ker, ← LinearMap.comp_apply]
  exact LinearMap.congr_fun (bdy1_comp_bdy2 R P) c

noncomputable abbrev H1_oc (P : FiniteCausalPoset n) : Type _ :=
  Z1_oc R P ⧸ (B1_oc R P).comap (Z1_oc R P).subtype

end OrderComplexProxy
end AqeiBridge
