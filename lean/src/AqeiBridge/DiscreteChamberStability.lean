import Mathlib.Data.Set.Basic

import AqeiBridge.Chambers
import AqeiBridge.DiscreteCausality

/-!
# Discrete chamber stability (toy implication)

This file connects the “chamber picture” to the discrete reachability model.

Idea (toy): if a parameter-to-discrete-spacetime map is **constant** on a chamber
(a convex region cut out by (in)active constraints), then the induced discrete
causal future `J⁺(p)` is also constant on that chamber.

This is a small but useful proof step for the “toward proof” roadmap:
- chamber convexity gives path-connectedness of parameter regions,
- local constancy on chambers removes “jump discontinuities” of the induced futures.

No topology/continuity is assumed here; we encode local constancy as an explicit hypothesis.
-/

namespace AqeiBridge

variable {n : ℕ}
variable {Pt : Type}

def ConstantOn {α β : Type} (S : Set α) (f : α → β) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → f x = f y

def DiscreteFuture (J : StressEnergy n → DiscreteSpacetime Pt) (p : Pt) : StressEnergy n → Set Pt :=
  fun T => JplusDiscrete (J T) p

theorem discreteFuture_eq_of_J_eq (J : StressEnergy n → DiscreteSpacetime Pt) (p : Pt)
    {T₁ T₂ : StressEnergy n} (h : J T₁ = J T₂) :
    DiscreteFuture (n := n) J p T₁ = DiscreteFuture (n := n) J p T₂ := by
  simpa [DiscreteFuture] using congrArg (fun M => JplusDiscrete M p) h

theorem image_eq_singleton_of_constantOn {α β : Type} {S : Set α} {f : α → β}
    (hne : S.Nonempty) (hconst : ConstantOn S f) : f '' S = ({f hne.choose} : Set β) := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx0 : hne.choose ∈ S := hne.choose_spec
    have : f x = f hne.choose := hconst hx hx0
    simpa [Set.mem_singleton_iff, this]
  · intro hy
    have hy' : y = f hne.choose := by
      simpa [Set.mem_singleton_iff] using hy
    refine ⟨hne.choose, hne.choose_spec, hy'.symm⟩

theorem discreteFuture_image_singleton_of_J_constantOn
    (J : StressEnergy n → DiscreteSpacetime Pt) (p : Pt)
    {ι : Type} (F : ι → AQEIFunctional n) (active : Set ι)
    (hne : (ClosedChamber (n := n) F active).Nonempty)
    (hJ : ConstantOn (ClosedChamber (n := n) F active) J) :
    (DiscreteFuture (n := n) J p) '' (ClosedChamber (n := n) F active)
      = ({DiscreteFuture (n := n) J p hne.choose} : Set (Set Pt)) := by
  classical
  -- First show the future-map is constant on the chamber.
  have hF : ConstantOn (ClosedChamber (n := n) F active) (DiscreteFuture (n := n) J p) := by
    intro x hx y hy
    exact discreteFuture_eq_of_J_eq (n := n) J p (hJ hx hy)
  exact image_eq_singleton_of_constantOn (hne := hne) hF

end AqeiBridge
