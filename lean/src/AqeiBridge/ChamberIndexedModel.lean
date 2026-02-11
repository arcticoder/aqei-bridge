import Mathlib.Data.Set.Basic

import AqeiBridge.AQEI_Cone
import AqeiBridge.DiscreteCausality
import AqeiBridge.DiscreteChamberStability

/-!
# Chamber-indexed discrete model

This file removes the *assumption* “`J` is constant on each chamber” by giving a
construction where it holds by definition.

We define a chamber index induced by the sign pattern of a finite family of
affine halfspace constraints `(F i).L T ≥ -(F i).B`:

- `chamberIndex F T : Set ι` records which constraints lie on the `≤` side of the
  corresponding hyperplane.
- A “chamber” is then the preimage of a fixed index `σ`.

Given any lookup table `model : Set ι → DiscreteSpacetime Pt`, we obtain

`J T := model (chamberIndex F T)`,

which **factors through the chamber index** and is therefore constant on each
chamber.

This is a deliberate toy construction used in the “toward proof” roadmap.
-/

namespace AqeiBridge

variable {n : ℕ}

section Index

variable {ι : Type}

/-- Chamber index induced by the sign of the affine functionals
`T ↦ (F i).L T + (F i).B`.

We record the `≤ 0` side, i.e. the predicate `(F i).L T ≤ -(F i).B`.

Note: the induced chamber sets `Chamber F σ := {T | chamberIndex F T = σ}` are
*exact* (they use strict inequality on the complement because equality of sets
forces a decision for each `i`).
-/
def chamberIndex (F : ι → AQEIFunctional n) (T : StressEnergy n) : Set ι :=
  {i | (F i).L T ≤ -(F i).B}

/-- The chamber corresponding to a fixed index/signature `σ`. -/
def Chamber (F : ι → AQEIFunctional n) (σ : Set ι) : Set (StressEnergy n) :=
  {T | chamberIndex (n := n) F T = σ}

theorem chamberIndex_eq_of_mem_chamber {F : ι → AQEIFunctional n} {σ : Set ι}
    {T : StressEnergy n} (hT : T ∈ Chamber (n := n) F σ) : chamberIndex (n := n) F T = σ :=
  hT

end Index

section Model

variable {ι : Type}
variable {Pt : Type}

/-- A discrete spacetime model indexed by chamber signatures.

This is the “per-chamber lookup table”. -/
abbrev ChamberModel (ι : Type) (Pt : Type) : Type := Set ι → DiscreteSpacetime Pt

/-- The chamber-indexed discrete model `J` induced by a family of constraints `F`
and a chamber lookup table `model`.

This is the requested `J : StressEnergy n → DiscreteSpacetime Pt` which provably
factors through the chamber index.
-/
def chamberIndexedJ (F : ι → AQEIFunctional n) (model : ChamberModel ι Pt) :
    StressEnergy n → DiscreteSpacetime Pt :=
  fun T => model (chamberIndex (n := n) F T)

theorem chamberIndexedJ_factors (F : ι → AQEIFunctional n) (model : ChamberModel ι Pt) :
    chamberIndexedJ (n := n) F model = fun T => model (chamberIndex (n := n) F T) :=
  rfl

theorem chamberIndexedJ_constantOn_chamber (F : ι → AQEIFunctional n) (model : ChamberModel ι Pt)
    (σ : Set ι) :
    ConstantOn (Chamber (n := n) F σ) (chamberIndexedJ (n := n) F model) := by
  intro x hx y hy
  -- Both points have the same chamber index, namely `σ`.
  have hx' : chamberIndex (n := n) F x = σ := hx
  have hy' : chamberIndex (n := n) F y = σ := hy
  have hxy : chamberIndex (n := n) F x = chamberIndex (n := n) F y := by
    calc
      chamberIndex (n := n) F x = σ := hx'
      _ = chamberIndex (n := n) F y := hy'.symm
  exact congrArg model hxy

theorem discreteFuture_image_singleton_of_chamberIndexedJ
    (F : ι → AQEIFunctional n) (model : ChamberModel ι Pt) (p : Pt) (σ : Set ι)
    (hne : (Chamber (n := n) F σ).Nonempty) :
    (DiscreteFuture (n := n) (chamberIndexedJ (n := n) F model) p) '' (Chamber (n := n) F σ)
      = ({DiscreteFuture (n := n) (chamberIndexedJ (n := n) F model) p hne.choose} : Set (Set Pt)) := by
  classical
  -- `J` is constant on each chamber by construction.
  have hJ : ConstantOn (Chamber (n := n) F σ) (chamberIndexedJ (n := n) F model) :=
    chamberIndexedJ_constantOn_chamber (n := n) F model σ
  -- Therefore the induced discrete future-map is constant on the same chamber.
  have hF : ConstantOn (Chamber (n := n) F σ)
      (DiscreteFuture (n := n) (chamberIndexedJ (n := n) F model) p) := by
    intro x hx y hy
    exact discreteFuture_eq_of_J_eq (n := n)
      (chamberIndexedJ (n := n) F model) p (hJ hx hy)
  exact image_eq_singleton_of_constantOn (hne := hne) hF

end Model

end AqeiBridge
