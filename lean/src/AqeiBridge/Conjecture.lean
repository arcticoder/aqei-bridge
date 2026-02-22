import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic

import AqeiBridge.StressEnergy
import AqeiBridge.AQEI_Cone
import AqeiBridge.DiscreteCausality

/-!
# Conjecture interface (Lean)

This file states the *interface* conjecture in Lean.

Important:
- The current statements are parameterized and intentionally abstract.
- They are designed to be refined as the manuscript-derived AQEI functionals
  and the causal model become available.

Formalizable now:
- finite-dimensional cones and convexity (already in `AQEI_Cone.lean`)
- discrete reachability models (see `DiscreteCausality.lean`)

Heuristic / not yet formal:
- PDE solution map `T ↦ h[T]`
- equality between Δ proxies and true causal-future changes

Background (external foundation):
- The companion repo `energy-tensor-cone` proves a non-trivial extreme-point result
  (`Candidate_Is_Extreme_Point` in `FinalTheorems.lean`) for the homogenized AQEI cone.
  In this repo we only reference that result at the documentation level; it motivates
  the idea that admissible perturbations live in a geometrically constrained region.
-/

namespace AqeiBridge

variable {n : ℕ}
variable {Pt : Type}

/- A reachability map produced by a stress-energy configuration in a toy model.

This is the formal “slot” where later we plug in:
- solve linearized Einstein,
- build a perturbed causal relation,
- take `Jplus`.

For now it is abstract.
-/
variable (J : StressEnergy n → DiscreteSpacetime Pt → DiscreteSpacetime Pt)

/- A small neighborhood selector around a point in coefficient space.

In the toy formalization we can treat this as an abstract predicate.
-/
variable (Small : StressEnergy n → Prop)

/-- The bridge conjecture (discrete, interface version).

If we restrict to a small neighborhood inside the AQEI polyhedron, the set of
reachable futures varies without “jumping” between disconnected components.

This is stated as a path-connectedness claim on the *parameter space*, not yet
on a topology of sets.
-/
axiom causal_futures_path_connected
  (F : List (AQEIFunctional n)) :
  True

end AqeiBridge
