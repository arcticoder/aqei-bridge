import Mathlib.Topology.Continuous

import AqeiBridge.CausalPoset

/-!
# Continuity lemmas for Alexandrov topology on a causal preorder (toy substrate)

In `AqeiBridge.CausalPoset`, the Alexandrov-style topology is defined by taking
opens to be upper sets.

This file records the key functoriality lemma we’ll want later:
- a monotone map pulls back upper sets to upper sets,
- hence a monotone map is continuous between Alexandrov topologies.
-/

namespace AqeiBridge

namespace CausalPoset

/-- Preimage of an upper set under a monotone map is an upper set. -/
theorem isUpperSet_preimage_of_monotone
    {C₁ C₂ : CausalPoset} (f : C₁.Pt → C₂.Pt) (hf : Monotone f)
    {s : Set C₂.Pt} (hs : IsUpperSet C₂ s) :
    IsUpperSet C₁ (f ⁻¹' s) := by
  intro a ha b hab
  exact hs ha (hf hab)

/-- Monotone maps are continuous between Alexandrov topologies (opens = upper sets). -/
theorem continuous_alexandrov_of_monotone
    {C₁ C₂ : CausalPoset} (f : C₁.Pt → C₂.Pt) (hf : Monotone f) :
    @Continuous _ _ (alexandrovTopology C₁) (alexandrovTopology C₂) f := by
  classical
  -- Unfold continuity in terms of preimages of opens.
  refine continuous_def.2 ?_
  intro s hs
  exact isUpperSet_preimage_of_monotone (C₁ := C₁) (C₂ := C₂) f hf hs

/-- A version of `continuous_alexandrov_of_monotone` that avoids `Monotone`.

This is often easier to use when `C₁`/`C₂` are constructed values (e.g. from a graph),
since it does not require synthesizing `Preorder` instances on the underlying carrier types.
-/
theorem continuous_alexandrov_of_le_monotone
    {C₁ C₂ : CausalPoset} (f : C₁.Pt → C₂.Pt)
    (hf : ∀ ⦃a b⦄, C₁.le a b → C₂.le (f a) (f b)) :
    @Continuous _ _ (alexandrovTopology C₁) (alexandrovTopology C₂) f := by
  classical
  refine continuous_def.2 ?_
  intro s hs
  intro a ha b hab
  exact hs ha (hf hab)

end CausalPoset

end AqeiBridge
