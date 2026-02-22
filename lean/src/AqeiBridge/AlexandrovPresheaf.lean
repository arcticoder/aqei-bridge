import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.CategoryTheory.Category.Basic

import AqeiBridge.CausalPoset

/-!
# Presheaves on Alexandrov opens (scaffold)

This module adds a minimal, compilation-safe “sheaf-like” interface on top of the
Alexandrov topology defined in `AqeiBridge.CausalPoset`.

Goal:
- Provide a concrete place to encode *sections over causal futures* `J⁺(p)` and
  their restriction maps.
- Avoid blocking on full Mathlib sheaf/cohomology infrastructure.

This is intentionally lightweight:
- We define `OpenInAlexandrov P` as the type of opens of the Alexandrov topology.
- A `PresheafOnPoset P C` is just an object assignment on opens plus restriction
  maps satisfying identity and composition.

Later work can:
- upgrade this to a contravariant functor `OpenInAlexandrov P ⥤ C`,
- define Čech cohomology on finite covers, or
- connect to the existing chain-complex proxy (`PosetHomologyProxy.lean`).
-/

namespace AqeiBridge

open CategoryTheory

namespace CausalPoset

/-- Opens in the Alexandrov topology associated to a causal preorder. -/
abbrev OpenInAlexandrov (P : AqeiBridge.CausalPoset) : Type :=
  @TopologicalSpace.Opens P.Pt (alexandrovTopology P)

/-- A minimal presheaf interface on Alexandrov opens.

If `V ≤ U` (i.e. `V ⊆ U`), then `res h : F(U) ⟶ F(V)` is the restriction map.
-/
structure PresheafOnPoset (P : AqeiBridge.CausalPoset) (C : Type) [Category C] where
  obj : OpenInAlexandrov P → C
  res : ∀ {U V : OpenInAlexandrov P}, V ≤ U → (obj U ⟶ obj V)
  res_id : ∀ U, res (show U ≤ U from le_rfl) = 𝟙 (obj U)
  res_comp :
    ∀ {U V W : OpenInAlexandrov P} (hWV : W ≤ V) (hVU : V ≤ U),
      res (le_trans hWV hVU) = res hVU ≫ res hWV

attribute [simp] PresheafOnPoset.res_id

/-- A placeholder for “restriction compatibility” (used by sheaf conditions).

We keep it as `True` for now to avoid introducing `sorry`.
-/
def RestrictionCompatible {P : AqeiBridge.CausalPoset} {C : Type} [Category C]
    (_F : PresheafOnPoset P C) (_U _V : OpenInAlexandrov P) (_h : _V ≤ _U) : Prop :=
  True

/-- A placeholder sheaf condition.

A real sheaf condition would quantify over covers and require unique gluing.
This is intentionally left as a *typed slot*.
-/
def SheafCondition {P : AqeiBridge.CausalPoset} {C : Type} [Category C]
    (_F : PresheafOnPoset P C) : Prop :=
  True

end CausalPoset

end AqeiBridge
