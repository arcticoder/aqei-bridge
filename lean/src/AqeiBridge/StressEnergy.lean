import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric

import AqeiBridge.Spacetime

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
  components : Matrix (Fin d) (Fin d) ℝ
  symmetric : components.IsSymm

/-- Placeholder AQEI-admissibility predicate for tensor-shaped sources.

In the current repo state, admissibility is modeled separately via `AQEI_Cone.lean`
over finite coefficient vectors.
-/
abbrev AQEIAdmissibleTensor {d : ℕ} (_T : StressEnergyTensor d) : Prop := True

/-- Placeholder: map a stress–energy tensor to a metric perturbation.

Later this should represent (linearized) Einstein: $\delta G = 8\pi\,\delta T$.
-/
noncomputable def LinearizedEinstein {M : Spacetime} (_T : StressEnergyTensor 4) : MetricPerturbation M :=
  ⟨fun _ _ => 0⟩

/-- Convenience wrapper: interpret a tensor-shaped source as a metric perturbation.

This is intentionally a placeholder; the real content should be a later
instantiation of the linearized Einstein operator.
-/
noncomputable def StressEnergyTensor.toPerturbation {M : Spacetime} (T : StressEnergyTensor 4) :
    MetricPerturbation M :=
  LinearizedEinstein (M := M) T

end AqeiBridge
