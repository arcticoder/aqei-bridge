import AqeiBridge.CausalPoset

import Mathlib.Order.Hom.Basic

/-!
# Global conjecture interface (Lean)

**Foundation from `energy-tensor-cone`:** The PRD submission (Feb 2026) in
`energy-tensor-cone` proves that the AQEI cone has a non-trivial extreme point:
- `Candidate_Is_Extreme_Point` (proven in `FinalTheorems.lean`) — the origin is
  the unique vertex of the homogenized AQEI cone restricted to the slice `t = 1`.
- The extreme point has exact rational coordinates.
- The closedness and convexity of the affine admissible set are proven in
  `AffineToCone.lean` (infinite-family versions) and `AQEIFamilyInterface.lean`.

This structure supports the global conjecture: the AQEI cone's geometry (compact
convex polytope with a unique extreme point) limits the range of admissible
perturbations to a bounded region, which is the foundation for bounding how much
a causal structure can change under AQEI-admissible perturbations.

**H₁ stability (now proven):** The formal analogue
`DiscreteSpacetime.h1_stable_small_pert` in `H1Stability.lean` shows that AQEI-
admissible perturbations (modeled as edge removal) preserve acyclicity (H₁ = 0).
The `ChronologyAsInvariant` axiom below is the abstract formulation whose
discrete version is now a theorem.

This file provides a compilation-safe *placeholder* for global invariance
statements, in the spirit of `AqeiBridge.Conjecture`.

This file deliberately does not commit to:
- a specific perturbation model,
- a specific homology theory,
- or a specific notion of admissibility.

Those pieces can be refined later while keeping downstream Lean code stable.
-/

namespace AqeiBridge

namespace CausalPoset

/-- Acyclicity proxy for a causal preorder: antisymmetry. -/
def Acyclic (P : CausalPoset) : Prop :=
  ∀ p q : P.Pt, P.le p q → P.le q p → p = q

/-- Acyclicity is invariant under order isomorphism.

This is a minimal formal proxy for “chronology is a topological invariant”,
since Alexandrov topologies have the original preorder as specialization order.
-/
theorem acyclic_iff_of_orderIso {P Q : CausalPoset} (e : P.Pt ≃o Q.Pt) :
    Acyclic P ↔ Acyclic Q := by
  constructor
  · intro h p q hpq hqp
    have hpre : e.symm p = e.symm q :=
      h (e.symm p) (e.symm q) ((e.symm.le_iff_le).2 hpq) ((e.symm.le_iff_le).2 hqp)
    have hpush := congrArg e hpre
    simpa using hpush
  · intro h p q hpq hqp
    have hpre : e p = e q :=
      h (e p) (e q) ((e.le_iff_le).2 hpq) ((e.le_iff_le).2 hqp)
    exact e.injective hpre

end CausalPoset

/-- Placeholder perturbation type for a causal structure. -/
structure Perturbation (P : CausalPoset) where
  dummy : Unit := ()

/-- Placeholder predicate: a perturbation is AQEI-admissible. -/
def AQEIAdmissible {P : CausalPoset} (_T : Perturbation P) : Prop := True

/-- Placeholder: apply a perturbation to a causal structure. -/
def PerturbPoset (P : CausalPoset) (_T : Perturbation P) : CausalPoset := P

/-- Placeholder for a (co)homology invariant of a causal structure. -/
def Homology (_P : CausalPoset) (_k : ℕ) : Type := PUnit

/-- Placeholder: global H₁ invariance under AQEI-admissible perturbations.

This is intentionally abstract. In the discrete development, the proven theorem
`h1_stable_small_pert` provides one concrete instance of the intended behavior.
-/
axiom global_h1_invariance
  (P : CausalPoset) (T : Perturbation P) (h : AQEIAdmissible T) :
  Homology P 1 = Homology (PerturbPoset P T) 1

/-- Draft global fragment: chronology/acyclicity and a homology invariant are preserved.

This matches the *shape* of the intended statement while remaining abstract.
-/
axiom ChronologyAsInvariant
  (P : CausalPoset) (T : Perturbation P) (h : AQEIAdmissible T) :
  CausalPoset.Acyclic P →
    CausalPoset.Acyclic (PerturbPoset P T) ∧
    Homology P 1 = Homology (PerturbPoset P T) 1

end AqeiBridge
