import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Sheaves.PresheafOfFunctions
import Mathlib.Topology.Sheaves.CommRingCat

import AqeiBridge.CausalPoset

/-!
# Alexandrov presheaf (Mathlib interface)

This module connects the repo’s Alexandrov-topology-on-posets substrate to Mathlib’s
`TopCat.Presheaf` API.

Motivation:
- The blocked TODO item “full Mathlib sheaf cohomology” requires representing presheaves/sheaves
  using Mathlib’s standard definitions.
- As a first unblock step, we provide a *concrete* presheaf valued in commutative rings:
  continuous real-valued functions on Alexandrov opens.

Notes:
- This is a presheaf; we do not attempt to build sheaf cohomology here.
- For finite posets, one future path is to compute Čech-style cohomology on a finite cover and
  compare it with the existing chain-complex proxy in `PosetHomologyProxy.lean`.
-/

namespace AqeiBridge

namespace CausalPoset

open TopologicalSpace

/-- The Alexandrov topological space associated to a causal preorder, packaged as a `TopCat`. -/
noncomputable def alexandrovTopCat (P : AqeiBridge.CausalPoset) : TopCat := by
  letI : TopologicalSpace P.Pt := alexandrovTopology P
  exact TopCat.of P.Pt

/-- Presheaf of commutative rings of continuous real-valued functions on Alexandrov opens. -/
noncomputable def realContinuousPresheaf (P : AqeiBridge.CausalPoset) :
    (alexandrovTopCat P).Presheaf CommRingCat :=
  TopCat.presheafToTopCommRing (X := alexandrovTopCat P) (TopCommRingCat.of ℝ)

end CausalPoset

end AqeiBridge
