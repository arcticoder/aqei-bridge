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

end AqeiBridge
