import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic

/-!
# Discrete Hausdorff-style distances on finite sets (scaffold)

This module provides a compilation-safe definition of a Hausdorff-style distance
between *finite* subsets, parameterized by an arbitrary distance function.

Motivation:
- The long-term plan is to reason about continuity/stability of future sets
  `J⁺(p)` under small perturbations.
- In this repo, the continuous/Hausdorff topology is blocked on choosing a
  metric/topology for the base space.
- As an unblock step, we define a *finite* Hausdorff-like quantity on `Finset`.

No metric axioms are assumed about `d`; later work can add hypotheses as needed.
-/

namespace AqeiBridge

namespace FinsetMetric

variable {α : Type}

/-- Minimum distance from a point to a finite set, using `0` for the empty set.

This is a purely algebraic helper; no metric axioms are assumed.
-/
noncomputable def minDistToSet (d : α → α → ℝ) (a : α) (B : Finset α) : ℝ :=
  if hB : B.Nonempty then
    B.inf' hB (fun b => d a b)
  else
    0

/-- Maximum over `a ∈ A` of the minimum distance from `a` to `B`.

This is the directed Hausdorff component `sup_{a∈A} inf_{b∈B} d(a,b)`,
implemented for finite sets, using `0` for the empty set.
-/
noncomputable def maxDistToSet (d : α → α → ℝ) (A B : Finset α) : ℝ :=
  if hA : A.Nonempty then
    A.sup' hA (fun a => minDistToSet d a B)
  else
    0

/-- A discrete Hausdorff-style distance between finite sets.

`d_H(A,B) = max( maxDistToSet A B, maxDistToSet B A )`.
-/
noncomputable def discreteHausdorff (d : α → α → ℝ) (A B : Finset α) : ℝ :=
  max (maxDistToSet d A B) (maxDistToSet d B A)

end FinsetMetric

end AqeiBridge
