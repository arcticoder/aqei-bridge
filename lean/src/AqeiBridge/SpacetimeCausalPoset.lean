import AqeiBridge.Spacetime
import AqeiBridge.CausalPoset

/-!
# From spacetime causal relations to a causal poset (toy bridge)

This file connects the abstract `Spacetime` interface to the order-theoretic
`CausalPoset` substrate.

We keep the connection honest by requiring explicit axioms (reflexivity and
transitivity) for the chosen causal relation.
-/

namespace AqeiBridge

namespace Spacetime

/-- Axioms making the (abstract) causal-curve predicate into a preorder.

This is intentionally minimal: we only need reflexivity and transitivity to
build a `CausalPoset` and its Alexandrov-style topology.
-/
structure CausalAxioms (M : Spacetime) (g : Metric M) : Prop where
  refl : ∀ p, CausalCurve M g p p
  trans : ∀ {p q r}, CausalCurve M g p q → CausalCurve M g q r → CausalCurve M g p r

/-- Package a spacetime point type with `CausalCurve M g` into a `CausalPoset`.

This is *not* a claim that `CausalCurve` has these properties in a physical
model; callers must supply the axioms.
-/
def toCausalPoset (M : Spacetime) (g : Metric M) (ax : CausalAxioms M g) : CausalPoset where
  Pt := M.Pt
  le := CausalCurve M g
  refl := ax.refl
  trans := by
    intro p q r hpq hqr
    exact ax.trans hpq hqr

/-- The Alexandrov-style topology induced by the preorder `CausalCurve M g`.

Opens are precisely the upper sets with respect to the causal preorder.
-/
noncomputable def alexandrovTopology (M : Spacetime) (g : Metric M) (ax : CausalAxioms M g) :
    TopologicalSpace M.Pt :=
  CausalPoset.alexandrovTopology (toCausalPoset M g ax)

/-- The order-theoretic future set $J^+(p)$ associated to `CausalCurve M g`.

This is definitionally the same as `AqeiBridge.Jplus` from `Spacetime.lean`, but
we keep it here to make the order-theoretic rewriting steps explicit.
-/
def Jplus_order (M : Spacetime) (g : Metric M) (p : M.Pt) : Set M.Pt :=
  {q | CausalCurve M g p q}

/-- In the induced Alexandrov topology, the future set `Jplus_order M g p` is open.

This is a direct reuse of the `CausalPoset.isOpen_Jplus` lemma.
-/
theorem isOpen_Jplus_order (M : Spacetime) (g : Metric M) (ax : CausalAxioms M g) (p : M.Pt) :
    @IsOpen _ (alexandrovTopology M g ax) (Jplus_order M g p) := by
  let C : CausalPoset := toCausalPoset M g ax
  simpa [alexandrovTopology, Jplus_order, CausalPoset.Jplus, C] using
    (CausalPoset.isOpen_Jplus (C := C) (p := p))

end Spacetime

end AqeiBridge
