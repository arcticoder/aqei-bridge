import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
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

/-- Convenience constructor from a list of `(L, B)` pairs.

This supports a “sampling-based” workflow where constraints are harvested from
finite sets of test functionals.
-/
def mkFunctionals {n : ℕ} (pairs : List ((StressEnergy n →ₗ[ℝ] ℝ) × ℝ)) : List (AQEIFunctional n) :=
  pairs.map (fun p => ⟨p.1, p.2⟩)

/-- The (toy) AQEI cone cut out by finitely many linear inequalities.

`T ∈ AQEI_cone F` means: for every functional `f ∈ F`, `f.L T ≥ -f.B`.

**Naming note:** This set is a **convex polyhedron** (intersection of affine halfspaces),
NOT a homogeneous cone under scaling. Scaling T by α > 1 can violate constraints because
the bounds `-f.B` do not scale proportionally. The name `AQEI_cone` is conventional;
see `energy-tensor-cone/AffineToCone.lean` for the homogenization approach that embeds
this set as the t=1 slice of a true cone in `E × ℝ`.
-/
def AQEI_cone {n : ℕ} (F : List (AQEIFunctional n)) : Set (StressEnergy n) :=
  {T | ∀ f ∈ F, f.L T ≥ -f.B}

/-- Convexity of the AQEI cone is a purely finite-dimensional fact:
intersection of (closed) affine halfspaces is convex.
-/
theorem AQEI_cone_convex {n : ℕ} (F : List (AQEIFunctional n)) : Convex ℝ (AQEI_cone F) := by
  classical
  intro x hx y hy a b ha hb hab f hf
  -- Need to show all inequalities remain true under convex combination.
  have hx' : f.L x ≥ -f.B := hx f hf
  have hy' : f.L y ≥ -f.B := hy f hf
  -- Use linearity of `f.L` and `linarith`.
  -- `simp` handles `map_add` and `map_smul` for linear maps.
  have : f.L (a • x + b • y) = a * f.L x + b * f.L y := by
    simp [map_add, map_smul]
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
  simpa [this, hab] using
    (by
      have h1 : a * f.L x ≥ a * (-f.B) := by nlinarith
      have h2 : b * f.L y ≥ b * (-f.B) := by nlinarith
      have hsum : a * f.L x + b * f.L y ≥ (a + b) * (-f.B) := by linarith
      -- use `hab` to rewrite `(a+b)*(-B)` to `-B`
      simpa [hab] using hsum)

/-- Closedness of the AQEI cone: finite intersection of closed affine halfspaces.

Each halfspace `{T | f.L T ≥ -f.B}` is closed because `f.L` is a continuous linear
map on the finite-dimensional space `StressEnergy n = Fin n → ℝ` (by
`LinearMap.continuous_of_finiteDimensional`).

Foundation: `energy-tensor-cone/AffineToCone.lean` proves the analogous
`affineAdmissible_isClosed` for infinite families using the same argument.
-/
theorem AQEI_cone_isClosed {n : ℕ} (F : List (AQEIFunctional n)) :
    IsClosed (AQEI_cone F) := by
  induction F with
  | nil =>
    -- empty list ⟹ whole space, which is closed
    simp [AQEI_cone]
  | cons f fs ih =>
    -- split head constraint off
    have h : AQEI_cone (f :: fs) = {T : StressEnergy n | f.L T ≥ -f.B} ∩ AQEI_cone fs := by
      ext T
      simp only [AQEI_cone, Set.mem_setOf_eq, List.mem_cons, or_imp, forall_and,
        Set.mem_inter_iff, forall_eq, ge_iff_le]
    rw [h]
    refine IsClosed.inter ?_ ih
    -- {T | f.L T ≥ -f.B} = (f.L)⁻¹' Set.Ici (-f.B), which is closed.
    -- `f.L` is continuous since `StressEnergy n = Fin n → ℝ` is finite-dimensional.
    have hcont : Continuous (f.L : StressEnergy n → ℝ) :=
      f.L.continuous_of_finiteDimensional
    simpa [ge_iff_le] using isClosed_Ici.preimage hcont

end AqeiBridge
