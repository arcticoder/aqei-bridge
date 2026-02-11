import Mathlib.Data.Set.Basic
import Mathlib.Tactic

import AqeiBridge.Chambers
import AqeiBridge.ChamberIndexedModel

/-!
# Connecting `ClosedChamber` and `chamberIndex`

There are two closely related “chamber” encodings in this repo:

- `ClosedChamber F active` (from `Chambers.lean`) encodes an *active-set* view:
  constraints in `active` hold at equality, constraints outside `active` hold as
  non-strict inequalities `≥`.

- `chamberIndex F T` (from `ChamberIndexedModel.lean`) encodes a *sign-pattern*
  view: it records which affine functionals satisfy `≤`.

These coincide cleanly on the *interior* of an active-set chamber, i.e. when
every inactive constraint is strict (`>`): then the sign-pattern index equals
the active set.

This file provides the bridge lemmas used to relate computational “active
constraints” diagnostics to the sign-pattern indexing used for the chamber-
indexed discrete model `J`.
-/

namespace AqeiBridge

variable {n : ℕ}
variable {ι : Type}

theorem active_subset_chamberIndex_of_mem_closedChamber
    (F : ι → AQEIFunctional n) (active : Set ι) {T : StressEnergy n}
    (hT : T ∈ ClosedChamber (n := n) F active) :
    active ⊆ chamberIndex (n := n) F T := by
  intro i hi
  -- If `i` is active, we have equality `L T = -B`, hence also `≤ -B`.
  have heq : (F i).L T = -(F i).B := hT.1 i hi
  show (F i).L T ≤ -(F i).B
  simpa [heq]

theorem chamberIndex_eq_active_of_mem_closedChamber_of_inactive_strict
    (F : ι → AQEIFunctional n) (active : Set ι) {T : StressEnergy n}
    (hT : T ∈ ClosedChamber (n := n) F active)
    (hstrict : ∀ i, i ∉ active → (F i).L T > -(F i).B) :
    chamberIndex (n := n) F T = active := by
  classical
  ext i
  constructor
  · intro hi
    by_contra hia
    have : (F i).L T > -(F i).B := hstrict i hia
    exact (not_le_of_gt this) hi
  · intro hi
    have heq : (F i).L T = -(F i).B := hT.1 i hi
    show (F i).L T ≤ -(F i).B
    simpa [heq]

theorem mem_Chamber_of_mem_closedChamber_of_inactive_strict
    (F : ι → AQEIFunctional n) (active : Set ι) {T : StressEnergy n}
    (hT : T ∈ ClosedChamber (n := n) F active)
    (hstrict : ∀ i, i ∉ active → (F i).L T > -(F i).B) :
    T ∈ Chamber (n := n) F active := by
  -- `Chamber F σ` is defined as the preimage of the signature `σ` under `chamberIndex`.
  exact (chamberIndex_eq_active_of_mem_closedChamber_of_inactive_strict (n := n) F active hT hstrict)

end AqeiBridge
