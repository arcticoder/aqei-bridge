import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.Ker

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian

import AqeiBridge.CausalPoset

open CategoryTheory

/-!
# Poset homology proxy (via Mathlib chain complexes)

This file packages the existing “1-cycle boundary” idea into a genuine
`ChainComplex (ModuleCat R) ℕ` so that Mathlib’s `homology` API can be used.

It is intentionally *low-degree*: we only build `C₀` and `C₁` and set `Cₙ = 0`
for `n ≥ 2`. This keeps the development CI-safe while providing a stable
interface for future refinements (e.g. the full order complex).

For a `CausalPoset P`:
- `C₀`: formal `R`-linear combinations of points
- `C₁`: formal `R`-linear combinations of strict edges `p < q`
- `∂₁(p<q) = q - p`

Then `H₁` is available as `posetChainComplex.homology 1`.
-/

namespace AqeiBridge

namespace CausalPoset

/-- A strict edge in a causal preorder (using the `lt` from the `Preorder` instance). -/
structure Edge (P : AqeiBridge.CausalPoset) where
  src : P.Pt
  dst : P.Pt
  ok : src < dst

section Boundary

variable (P : AqeiBridge.CausalPoset)
variable (R : Type) [CommRing R]
variable [DecidableEq P.Pt]

/-- Boundary of a single strict edge: `∂(p<q) = q - p`. -/
noncomputable def edgeBoundary (e : Edge P) : P.Pt →₀ R :=
  Finsupp.single e.dst (1 : R) - Finsupp.single e.src (1 : R)

/-- The `R`-linear map sending `r` to `r • ∂(e)`. -/
noncomputable def edgeBoundaryMap (e : Edge P) : R →ₗ[R] (P.Pt →₀ R) where
  toFun r := r • edgeBoundary (P := P) (R := R) e
  map_add' a b := by simp [add_smul]
  map_smul' a b := by simp [mul_smul]

/-- Incidence boundary `∂₁ : C₁ → C₀`. -/
noncomputable def boundary1 : (Edge P →₀ R) →ₗ[R] (P.Pt →₀ R) :=
  Finsupp.lsum R (fun e => edgeBoundaryMap (P := P) (R := R) e)

/-- The space of 1-cycles `Z₁ := ker ∂₁`. -/
noncomputable def Z1 : Submodule R (Edge P →₀ R) :=
  LinearMap.ker (boundary1 (P := P) (R := R))

end Boundary

section ChainComplex

variable (P : AqeiBridge.CausalPoset)
variable (R : Type) [CommRing R]
variable [DecidableEq P.Pt]

/-- The object part of the low-degree chain complex: `C₀`, `C₁`, and `0` above. -/
noncomputable def chainObj : ℕ → ModuleCat R
  | 0 => ModuleCat.of R (P.Pt →₀ R)
  | 1 => ModuleCat.of R (Edge P →₀ R)
  | _ + 2 => ModuleCat.of R PUnit

/-- The differentials of the low-degree chain complex. -/
noncomputable def chainD : ∀ n : ℕ, chainObj (P := P) (R := R) (n + 1) ⟶ chainObj (P := P) (R := R) n
  | 0 => ModuleCat.ofHom (boundary1 (P := P) (R := R))
  | 1 => 0
  | _ + 2 => 0

theorem chainD_squared (n : ℕ) :
  chainD (P := P) (R := R) (n + 1) ≫ chainD (P := P) (R := R) n = 0 := by
  cases n <;> simp [chainD, chainObj]

/-- A `ChainComplex` whose degree-1 cycles implement the poset 1-cycle proxy. -/
noncomputable abbrev posetChainComplex : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (chainObj (P := P) (R := R)) (chainD (P := P) (R := R))
    (by
      intro n
      simpa using (chainD_squared (P := P) (R := R) n))

/-- The first homology object `H₁` of the low-degree proxy chain complex. -/
noncomputable abbrev H1 : ModuleCat R := (posetChainComplex (P := P) (R := R)).homology 1

end ChainComplex

end CausalPoset

end AqeiBridge
