import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.Ker

import AqeiBridge.DiscreteCausalPoset

/-!
# Discrete homology proxy (toy)

This file defines a minimal *chain-level* invariant for a directed graph:
- `C₀`: formal `R`-linear combinations of vertices (`Pt →₀ R`)
- `C₁`: formal `R`-linear combinations of edges (`Edge M →₀ R`)
- `∂₁ : C₁ →ₗ[R] C₀`: the incidence boundary `q - p` for an edge `p → q`

We define the 1-cycle space `Z₁ := ker ∂₁` and prove functoriality of `Z₁` under
edge-homomorphisms.

This is intentionally a proxy: it gives a first “(co)homology-like” object
without committing to a full simplicial/order-complex development.
-/

namespace AqeiBridge

namespace DiscreteSpacetime

/-- A directed edge packaged as data + a proof it is an edge. -/
structure Edge {Pt : Type} (M : DiscreteSpacetime Pt) where
  src : Pt
  dst : Pt
  ok : M.edge src dst

section Boundary

variable {Pt : Type}
variable (M : DiscreteSpacetime Pt)
variable (R : Type) [CommRing R]
variable [DecidableEq Pt]

/-- Boundary of a single edge: `∂(p→q) = q - p` at the chain level. -/
noncomputable def edgeBoundary (e : Edge M) : Pt →₀ R :=
  Finsupp.single e.dst (1 : R) - Finsupp.single e.src (1 : R)

/-- The `R`-linear map sending a coefficient `r` to the boundary chain `r • ∂(e)`. -/
noncomputable def edgeBoundaryMap (e : Edge M) : R →ₗ[R] (Pt →₀ R) where
  toFun r := r • edgeBoundary (M := M) (R := R) e
  map_add' a b := by simp [add_smul]
  map_smul' a b := by simp [mul_smul]

/-- Incidence boundary `∂₁ : C₁ → C₀` as a linear map on `Finsupp`. -/
noncomputable def boundary1 : (Edge M →₀ R) →ₗ[R] (Pt →₀ R) :=
  Finsupp.lsum R (fun e => edgeBoundaryMap (M := M) (R := R) e)

set_option linter.unusedSectionVars false in
@[simp] theorem boundary1_single (e : Edge M) (r : R) :
    boundary1 (M := M) (R := R) (Finsupp.single e r) = r • edgeBoundary (M := M) (R := R) e := by
  simp [boundary1, edgeBoundaryMap, edgeBoundary]

/-- The space of 1-cycles: `Z₁ := ker ∂₁`.

This is a proxy for `H₁` in the absence of 2-cells.
-/
noncomputable def Z1 : Submodule R (Edge M →₀ R) :=
  LinearMap.ker (boundary1 (M := M) (R := R))

end Boundary

section Functorial

variable {Pt₁ Pt₂ : Type}
variable {M₁ : DiscreteSpacetime Pt₁} {M₂ : DiscreteSpacetime Pt₂}

variable (R : Type) [CommRing R]
variable [DecidableEq Pt₁] [DecidableEq Pt₂]

/-- Pushforward of `0`-chains along a function on vertices. -/
noncomputable def push0 (f : Pt₁ → Pt₂) : (Pt₁ →₀ R) →ₗ[R] (Pt₂ →₀ R) :=
  Finsupp.lsum R (fun p =>
    { toFun := fun r => Finsupp.single (f p) r
      map_add' := by intro a b; simp
      map_smul' := by intro a b; simp })

set_option linter.unusedSectionVars false in
@[simp] theorem push0_single (f : Pt₁ → Pt₂) (p : Pt₁) (r : R) :
    push0 (R := R) f (Finsupp.single p r) = Finsupp.single (f p) r := by
  simp [push0]

/-- Map a directed edge along an edge-homomorphism. -/
noncomputable def mapEdge (f : Pt₁ → Pt₂) (hf : EdgeHom M₁ M₂ f) : Edge M₁ → Edge M₂ :=
  fun e => ⟨f e.src, f e.dst, hf e.ok⟩

/-- Pushforward of `1`-chains along an edge-homomorphism. -/
noncomputable def push1 (f : Pt₁ → Pt₂) (hf : EdgeHom M₁ M₂ f) :
    (Edge M₁ →₀ R) →ₗ[R] (Edge M₂ →₀ R) :=
  Finsupp.lsum R (fun e =>
    { toFun := fun r => Finsupp.single (mapEdge (M₁ := M₁) (M₂ := M₂) f hf e) r
      map_add' := by intro a b; simp
      map_smul' := by intro a b; simp })

set_option linter.unusedSectionVars false in
@[simp] theorem push1_single (f : Pt₁ → Pt₂) (hf : EdgeHom M₁ M₂ f) (e : Edge M₁) (r : R) :
    push1 (M₁ := M₁) (M₂ := M₂) (R := R) f hf (Finsupp.single e r)
      = Finsupp.single (mapEdge (M₁ := M₁) (M₂ := M₂) f hf e) r := by
  simp [push1]

set_option linter.unusedSectionVars false in
@[simp] theorem push0_edgeBoundary (f : Pt₁ → Pt₂) (hf : EdgeHom M₁ M₂ f) (e : Edge M₁) :
    push0 (R := R) f (edgeBoundary (M := M₁) (R := R) e)
      = edgeBoundary (M := M₂) (R := R) (mapEdge (M₁ := M₁) (M₂ := M₂) f hf e) := by
  classical
  simp [edgeBoundary, LinearMap.map_sub, mapEdge]

theorem boundary1_natural_single (f : Pt₁ → Pt₂) (hf : EdgeHom M₁ M₂ f) (e : Edge M₁) (r : R) :
    boundary1 (M := M₂) (R := R)
        (push1 (M₁ := M₁) (M₂ := M₂) (R := R) f hf (Finsupp.single e r))
      =
      push0 (R := R) f
        (boundary1 (M := M₁) (R := R) (Finsupp.single e r)) := by
  classical
  have hEdge :=
    push0_edgeBoundary (M₁ := M₁) (M₂ := M₂) (R := R) (f := f) (hf := hf) e
  have hSmul :
      r • push0 (R := R) f (edgeBoundary (M := M₁) (R := R) e)
        = r • edgeBoundary (M := M₂) (R := R) (mapEdge (M₁ := M₁) (M₂ := M₂) f hf e) :=
    congrArg (fun x => r • x) hEdge
  calc
    boundary1 (M := M₂) (R := R)
        (push1 (M₁ := M₁) (M₂ := M₂) (R := R) f hf (Finsupp.single e r))
        = r • edgeBoundary (M := M₂) (R := R) (mapEdge (M₁ := M₁) (M₂ := M₂) f hf e) := by
          simp [push1_single, boundary1_single]
    _ = r • push0 (R := R) f (edgeBoundary (M := M₁) (R := R) e) := by
          simpa using hSmul.symm
    _ = push0 (R := R) f (r • edgeBoundary (M := M₁) (R := R) e) := by
          simp
    _ = push0 (R := R) f (boundary1 (M := M₁) (R := R) (Finsupp.single e r)) := by
          simp [boundary1_single]

/-- Naturality of the incidence boundary under edge-homomorphisms. -/
theorem boundary1_natural (f : Pt₁ → Pt₂) (hf : EdgeHom M₁ M₂ f) (c : Edge M₁ →₀ R) :
    boundary1 (M := M₂) (R := R) (push1 (M₁ := M₁) (M₂ := M₂) (R := R) f hf c)
      =
      push0 (R := R) f (boundary1 (M := M₁) (R := R) c) := by
  classical
  refine Finsupp.induction c ?hz ?ha
  · simp [push1, push0, boundary1]
  · intro e r c _her _hc ih
    have hsingle := boundary1_natural_single (M₁ := M₁) (M₂ := M₂) (R := R) f hf e r
    calc
      boundary1 (M := M₂) (R := R)
          (push1 (M₁ := M₁) (M₂ := M₂) (R := R) f hf (Finsupp.single e r + c))
          = boundary1 (M := M₂) (R := R)
              (push1 (M₁ := M₁) (M₂ := M₂) (R := R) f hf (Finsupp.single e r)
                + push1 (M₁ := M₁) (M₂ := M₂) (R := R) f hf c) := by
              simp [LinearMap.map_add]
      _ = boundary1 (M := M₂) (R := R)
              (push1 (M₁ := M₁) (M₂ := M₂) (R := R) f hf (Finsupp.single e r))
            + boundary1 (M := M₂) (R := R) (push1 (M₁ := M₁) (M₂ := M₂) (R := R) f hf c) := by
              simp [LinearMap.map_add]
      _ = push0 (R := R) f (boundary1 (M := M₁) (R := R) (Finsupp.single e r))
            + push0 (R := R) f (boundary1 (M := M₁) (R := R) c) := by
              -- `congrArg2` isn't in core prelude in this setup; do it by hand.
              have hsum1 :=
                congrArg
                  (fun x => x + boundary1 (M := M₂) (R := R) (push1 (M₁ := M₁) (M₂ := M₂) (R := R) f hf c))
                  hsingle
              have hsum2 :=
                congrArg
                  (fun x =>
                    push0 (R := R) f (boundary1 (M := M₁) (R := R) (Finsupp.single e r)) + x)
                  ih
              exact hsum1.trans hsum2
      _ = push0 (R := R) f
            (boundary1 (M := M₁) (R := R) (Finsupp.single e r) + boundary1 (M := M₁) (R := R) c) := by
              simp [LinearMap.map_add]
      _ = push0 (R := R) f (boundary1 (M := M₁) (R := R) (Finsupp.single e r + c)) := by
              simp [LinearMap.map_add]

/-- Pushforward maps 1-cycles to 1-cycles. -/
theorem push1_mem_Z1 (f : Pt₁ → Pt₂) (hf : EdgeHom M₁ M₂ f) {c : Edge M₁ →₀ R}
    (hc : c ∈ Z1 (M := M₁) (R := R)) :
    push1 (M₁ := M₁) (M₂ := M₂) (R := R) f hf c ∈ Z1 (M := M₂) (R := R) := by
  -- Unfold the kernel definition.
  simp [Z1] at hc ⊢
  calc
    boundary1 (M := M₂) (R := R) (push1 (M₁ := M₁) (M₂ := M₂) (R := R) f hf c)
        = push0 (R := R) f (boundary1 (M := M₁) (R := R) c) :=
          boundary1_natural (M₁ := M₁) (M₂ := M₂) (R := R) f hf c
    _ = push0 (R := R) f 0 := by simp [hc]
    _ = 0 := by simp

end Functorial

end DiscreteSpacetime

end AqeiBridge
