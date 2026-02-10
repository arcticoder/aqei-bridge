import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

import AqeiBridge.StressEnergy

/-!
# AQEI cone

This file defines a finite list of linear AQEI functionals and the corresponding
constraint set (a convex set / polyhedral cone in the toy model).

**Formalizable now:** convexity and basic closure properties under linear ops.
**Heuristic:** interpreting these constraints as genuine AQEI bounds for QFT on
curved spacetimes (that requires substantial analytic/QFT machinery).
-/

namespace AqeiBridge

/-- A linear AQEI functional with a bound. -/
structure AQEIFunctional (n : ℕ) where
  L : StressEnergy n →ₗ[ℝ] ℝ
  B : ℝ

/-- The (toy) AQEI cone cut out by finitely many linear inequalities.

`T ∈ AQEI_cone F` means: for every functional `f ∈ F`, `f.L T ≥ -f.B`.
-/
def AQEI_cone {n : ℕ} (F : List (AQEIFunctional n)) : Set (StressEnergy n) :=
  {T | ∀ f ∈ F, f.L T ≥ -f.B}

/-- Convexity of the AQEI cone is a purely finite-dimensional fact:
intersection of (closed) affine halfspaces is convex.
-/
theorem AQEI_cone_convex {n : ℕ} (F : List (AQEIFunctional n)) : Convex ℝ (AQEI_cone F) := by
  classical
  intro x hx y hy a b ha hb hab
  -- Need to show all inequalities remain true under convex combination.
  intro f hf
  have hx' : f.L x ≥ -f.B := hx f hf
  have hy' : f.L y ≥ -f.B := hy f hf
  -- Use linearity of `f.L` and `linarith`.
  -- `simp` handles `map_add` and `map_smul` for linear maps.
  have : f.L (a • x + b • y) = a * f.L x + b * f.L y := by
    simp [map_add, map_smul, mul_add, add_mul]
  -- Rewrite goal using the computed expression.
  -- Then use the convex weights assumptions.
  -- (The proof is simple arithmetic; we let `linarith` finish.)
  --
  -- `linarith` can use `hab : a + b = 1` as well.
  --
  -- Note: `simp` will unfold scalar multiplication on functions `Fin n → ℝ`.
  --
  -- Goal is `f.L (a•x + b•y) ≥ -f.B`.
  --
  -- Replace `f.L (a•x + b•y)` with `a*f.L x + b*f.L y`.
  --
  -- Then:
  --   a*f.L x + b*f.L y ≥ a*(-B) + b*(-B) = (a+b)*(-B) = -B.
  --
  -- This only needs `ha hb` and the bounds.
  --
  --
  -- Finish:
  simpa [this, hab, mul_assoc, add_comm, add_left_comm, add_assoc, mul_add, add_mul] using
    (by
      have h1 : a * f.L x ≥ a * (-f.B) := by nlinarith
      have h2 : b * f.L y ≥ b * (-f.B) := by nlinarith
      have hsum : a * f.L x + b * f.L y ≥ (a + b) * (-f.B) := by linarith
      -- use `hab` to rewrite `(a+b)*(-B)` to `-B`
      simpa [hab] using hsum)

end AqeiBridge
