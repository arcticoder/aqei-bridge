import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.LocallyConstant.Basic

import AqeiBridge.AQEI_Cone
import AqeiBridge.Chambers

/-!
# C.1 — Global chamber constancy on path-connected convex sets

**Main theorem**: A locally constant function on a path-connected set is globally
constant.

In the AQEI setting: since `AQEI_cone F` is convex and nonempty, it is
path-connected.  Any function `Φ : StressEnergy n → α` that is locally constant
(e.g. because it factors through a discrete chamber index) is therefore globally
constant on the cone.

This supplies the abstract backing for the claim that the chamber-indexed discrete
model `J = chamberIndexedJ F model` cannot "jump" across different values within
a single connected component of the parameter space.
-/

namespace AqeiBridge

/-! ## Abstract version -/

/-- **C.1 (abstract)**: A locally constant function on a path-connected set is
globally constant.

Proof: `IsPathConnected.isConnected` + `IsConnected.isPreconnected` plus
`IsLocallyConstant.apply_eq_of_isPreconnected` from Mathlib. -/
theorem chamber_constancy_global
    {X Y : Type*} [TopologicalSpace X]
    {C : Set X} (hconn : IsPathConnected C)
    {Φ : X → Y} (hΦ : IsLocallyConstant Φ)
    {T₁ T₂ : X} (h₁ : T₁ ∈ C) (h₂ : T₂ ∈ C) :
    Φ T₁ = Φ T₂ :=
  hΦ.apply_eq_of_isPreconnected hconn.isConnected.isPreconnected h₁ h₂

/-! ## Convex-set corollary -/

/-- **C.1 (convex corollary)**: A locally constant function on a nonempty convex
subset of a real topological vector space is globally constant. -/
theorem chamber_constancy_of_convex
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    [ContinuousAdd V] [ContinuousSMul ℝ V]
    {C : Set V} (hconv : Convex ℝ C)
    {Y : Type*} {Φ : V → Y} (hΦ : IsLocallyConstant Φ)
    {T₁ T₂ : V} (h₁ : T₁ ∈ C) (h₂ : T₂ ∈ C) :
    Φ T₁ = Φ T₂ :=
  hΦ.apply_eq_of_isPreconnected hconv.isPreconnected h₁ h₂

/-! ## AQEI cone instantiation -/

/-- **C.1 (AQEI cone)**: Any locally constant function on the AQEI parameter cone
is globally constant, provided the cone is nonempty.

This is the key invariance property for chamber-indexed discrete models:
a model `J = chamberIndexedJ F model` which happens to be locally constant
(e.g. if all constraints are non-degenerate) takes a single value throughout
the feasible parameter region. -/
theorem AQEI_chamber_constancy {n : ℕ} (F : List (AQEIFunctional n))
    {Y : Type*} (Φ : StressEnergy n → Y) (hΦ : IsLocallyConstant Φ)
    {T₁ T₂ : StressEnergy n}
    (h₁ : T₁ ∈ AQEI_cone (n := n) F) (h₂ : T₂ ∈ AQEI_cone (n := n) F) :
    Φ T₁ = Φ T₂ :=
  hΦ.apply_eq_of_isPreconnected (AQEI_cone_convex (n := n) F).isPreconnected h₁ h₂

/-- Variant: the `hB` condition is vacuous (AQEI_chamber_constancy is
unconditional on bounds), but this alias is kept for API compatibility. -/
-- @[unused_variable_suppress] -- hB is intentionally unused
theorem AQEI_chamber_constancy_of_bounds_nonneg {n : ℕ} (F : List (AQEIFunctional n))
    (_hB : ∀ f ∈ F, 0 ≤ f.B)
    {Y : Type*} (Φ : StressEnergy n → Y) (hΦ : IsLocallyConstant Φ)
    {T₁ T₂ : StressEnergy n}
    (h₁ : T₁ ∈ AQEI_cone (n := n) F) (h₂ : T₂ ∈ AQEI_cone (n := n) F) :
    Φ T₁ = Φ T₂ :=
  AQEI_chamber_constancy F Φ hΦ h₁ h₂

end AqeiBridge
