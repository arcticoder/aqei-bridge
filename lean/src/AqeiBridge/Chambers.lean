import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic

import AqeiBridge.AQEI_Cone

/-!
# Chambers and toy path-connectedness lemmas

This file adds a small “toward proof” step for the bridge conjecture.

The motivating picture is polyhedral/chamber decomposition in parameter space:
regions defined by (in)active linear inequalities are convex, hence path-connected.

We keep this intentionally minimal:
- “chambers” are encoded as finite collections of equalities + inequalities,
- connectedness is purely a finite-dimensional convexity fact.

No claims are made here about Lorentzian $J^+$ continuity.
-/

namespace AqeiBridge

variable {n : ℕ}

/-!
## Closed chambers for a finite family of constraints

Given a family of AQEI-like constraints indexed by `ι`, and a chosen set `active ⊆ ι`,
we define a **closed chamber** where
- active constraints hold at equality, and
- inactive constraints hold as (non-strict) inequalities.

This choice keeps the set convex by construction.
-/

def ClosedChamber {ι : Type} (F : ι → AQEIFunctional n) (active : Set ι) : Set (StressEnergy n) :=
  {T |
    (∀ i, i ∈ active → (F i).L T = -(F i).B) ∧
    (∀ i, i ∉ active → (F i).L T ≥ -(F i).B)}

theorem closedChamber_convex {ι : Type} (F : ι → AQEIFunctional n) (active : Set ι) :
    Convex ℝ (ClosedChamber (n := n) F active) := by
  classical
  intro x hx y hy a b ha hb hab
  constructor
  · intro i hi
    have hx' : (F i).L x = -(F i).B := (hx.1 i hi)
    have hy' : (F i).L y = -(F i).B := (hy.1 i hi)
    -- linearity reduces equality to arithmetic
    have hlin : (F i).L (a • x + b • y) = a * (F i).L x + b * (F i).L y := by
      simp [map_add, map_smul]
    -- substitute and finish
    calc
      (F i).L (a • x + b • y)
          = a * (F i).L x + b * (F i).L y := hlin
      _   = a * (-(F i).B) + b * (-(F i).B) := by simp [hx', hy']
      _   = (a + b) * (-(F i).B) := by ring
      _   = -(F i).B := by simpa [hab]
  · intro i hi
    have hx' : (F i).L x ≥ -(F i).B := (hx.2 i hi)
    have hy' : (F i).L y ≥ -(F i).B := (hy.2 i hi)
    have hlin : (F i).L (a • x + b • y) = a * (F i).L x + b * (F i).L y := by
      simp [map_add, map_smul]
    -- Use nonnegativity of weights to preserve inequalities.
    -- (This is the same arithmetic pattern as AQEI_cone_convex.)
    have h1 : a * (F i).L x ≥ a * (-(F i).B) := by nlinarith
    have h2 : b * (F i).L y ≥ b * (-(F i).B) := by nlinarith
    have hsum : a * (F i).L x + b * (F i).L y ≥ (a + b) * (-(F i).B) := by linarith
    -- Rewrite with hab.
    simpa [ClosedChamber, hlin, hab] using hsum

theorem closedChamber_isPathConnected {ι : Type} (F : ι → AQEIFunctional n) (active : Set ι)
    (hne : (ClosedChamber (n := n) F active).Nonempty) :
    IsPathConnected (ClosedChamber (n := n) F active) :=
  (closedChamber_convex (n := n) F active).isPathConnected hne

/-!
## AQEI cone: nonemptiness + path-connectedness under mild assumptions

The toy AQEI cone uses inequalities `f.L T ≥ -f.B`.
If all bounds satisfy `0 ≤ f.B`, then `T = 0` is feasible.
With convexity, this implies path-connectedness.
-/

theorem zero_mem_AQEI_cone_of_bounds_nonneg (F : List (AQEIFunctional n))
    (hB : ∀ f ∈ F, 0 ≤ f.B) : (0 : StressEnergy n) ∈ AQEI_cone (n := n) F := by
  intro f hf
  have : 0 ≤ f.B := hB f hf
  simpa [AQEI_cone] using (by
    -- `f.L 0 = 0` and `0 ≥ -B` if `B ≥ 0`.
    have : (0 : ℝ) ≥ -f.B := by linarith
    simpa using this)

theorem AQEI_cone_nonempty_of_bounds_nonneg (F : List (AQEIFunctional n))
    (hB : ∀ f ∈ F, 0 ≤ f.B) : (AQEI_cone (n := n) F).Nonempty :=
  ⟨0, zero_mem_AQEI_cone_of_bounds_nonneg (n := n) F hB⟩

theorem AQEI_cone_isPathConnected_of_bounds_nonneg (F : List (AQEIFunctional n))
    (hB : ∀ f ∈ F, 0 ≤ f.B) : IsPathConnected (AQEI_cone (n := n) F) :=
  (AQEI_cone_convex (n := n) F).isPathConnected (AQEI_cone_nonempty_of_bounds_nonneg (n := n) F hB)

end AqeiBridge
