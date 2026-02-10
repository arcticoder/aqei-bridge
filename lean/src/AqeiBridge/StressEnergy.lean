import Mathlib.Data.Real.Basic

/-!
# Stress-energy (finite-dimensional toy model)

We model stress-energy configurations as coefficient vectors `Fin n → ℝ`.
This is the minimal structure needed for:
- linear AQEI functionals,
- convex cones cut out by linear inequalities,
- exporting finite candidates from numerical search.
-/

namespace AqeiBridge

/-- `StressEnergy n` is an `n`-dimensional real vector of coefficients. -/
abbrev StressEnergy (n : ℕ) : Type := Fin n → ℝ

/-!
## Tensor-shaped placeholder

For later stages we may want a tensor-shaped object (e.g. a square matrix of
components) in addition to the finite coefficient model.

This is *not* used by the current pipeline; it exists to make the intended
formalization direction explicit.
-/

/-- A toy stress–energy tensor as a square matrix of real components.

This is a placeholder: real admissibility conditions (AQEI) are not encoded
here yet.
-/
structure StressEnergyTensor (d : ℕ) where
  components : Fin d → Fin d → ℝ

end AqeiBridge
