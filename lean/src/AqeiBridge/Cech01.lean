import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Čech 0/1 cochain complex for a finite cover

We model a finite open cover by a finite index set `I`. The Čech cochain complex
is the sequence

```
  C0(I,R) --d0--> C1(I,R) --d1--> C2(I,R)
```

where:
- `C0 I R := I → R` (0-cochains: sections on each open)
- `C1 I R := I × I → R` (1-cochains: sections on pairwise intersections)
- `C2 I R := I × I × I → R` (2-cochains: sections on triple intersections)

with Čech coboundaries
- `(d0 f)(i,j) = f j - f i`
- `(d1 g)(i,j,k) = g(i,j) - g(i,k) + g(j,k)`

This file:
1. Defines `d0` and `d1` as `R`-linear maps between Pi-modules.
2. Proves the key complex property `d1 ∘ d0 = 0`.
3. Defines the Čech H¹ as `ker(d1) / im(d0)` via `Submodule.Quotient`.

No metric axioms or sheaf conditions are imposed: sections are arbitrary
`R`-valued functions. This provides a minimal, compilable Čech scaffold for use
in aqei-bridge without importing the full sheaf/cohomology infrastructure.
-/

namespace AqeiBridge

namespace Cech01

variable (R : Type) [CommRing R] (I : Type) [Fintype I] [DecidableEq I]

/-! ## Cochain groups -/

/-- 0-cochains: functions `I → R` (sections on each open of the cover). -/
abbrev C0 : Type _ := I → R

/-- 1-cochains: functions `I × I → R` (sections on pairwise intersections). -/
abbrev C1 : Type _ := I × I → R

/-- 2-cochains: functions `I × I × I → R` (sections on triple intersections). -/
abbrev C2 : Type _ := I × I × I → R

/-! ## Coboundary maps -/

/-- Čech coboundary `d⁰ : C0 →ₗ[R] C1`.

`(d0 f)(i, j) = f j - f i`
-/
def d0 : C0 R I →ₗ[R] C1 R I where
  toFun f ij := f ij.2 - f ij.1
  map_add' f g := by
    ext ⟨i, j⟩
    simp [Pi.add_apply]
    ring
  map_smul' r f := by
    ext ⟨i, j⟩
    simp [Pi.smul_apply]
    ring

/-- Čech coboundary `d¹ : C1 →ₗ[R] C2`.

`(d1 g)(i, j, k) = g(i, j) - g(i, k) + g(j, k)`

(using the right-nested `I × (I × I)` convention for triples)
-/
def d1 : C1 R I →ₗ[R] C2 R I where
  toFun g ijk := g (ijk.1, ijk.2.1) - g (ijk.1, ijk.2.2) + g (ijk.2.1, ijk.2.2)
  map_add' f g := by
    ext ⟨i, j, k⟩
    simp [Pi.add_apply]
    ring
  map_smul' r f := by
    ext ⟨i, j, k⟩
    simp [Pi.smul_apply]
    ring

/-! ## Complex property -/

/-- The key chain-complex property: `d1 ∘ d0 = 0`.

Proof: for any `f : C0` and triple `(i, j, k)`,
```
  (d1 (d0 f))(i,j,k)
    = d0 f (i,j) - d0 f (i,k) + d0 f (j,k)
    = (f j - f i) - (f k - f i) + (f k - f j)
    = 0
```
-/
lemma d1_comp_d0 : (d1 R I).comp (d0 R I) = 0 := by
  ext f ⟨i, j, k⟩
  simp [d0, d1, LinearMap.comp_apply, LinearMap.zero_apply]

/-- The image of `d0` lies inside the kernel of `d1`. -/
lemma range_d0_le_ker_d1 :
    LinearMap.range (d0 R I) ≤ LinearMap.ker (d1 R I) := by
  intro x hx
  obtain ⟨f, hf⟩ := LinearMap.mem_range.mp hx
  rw [← hf, LinearMap.mem_ker]
  have h := d1_comp_d0 R I
  simp only [LinearMap.ext_iff, LinearMap.comp_apply, LinearMap.zero_apply] at h
  exact h f

/-! ## Čech H¹ -/

/--
Čech H¹ as a quotient of R-modules:

`H1Cech R I := ker(d1) / (im(d0) ∩ ker(d1))`

Since `im(d0) ⊆ ker(d1)`, this is simply `ker(d1) / im(d0)`, i.e., the quotient of
the submodule `ker(d1)` by the submodule induced by `im(d0)`.
-/
abbrev H1Cech : Type _ :=
  (LinearMap.ker (d1 R I)) ⧸
    ((LinearMap.range (d0 R I)).comap (LinearMap.ker (d1 R I)).subtype)

/-! ## Sanity lemma: H¹ is trivial when ker(d1) ⊆ im(d0) -/

set_option linter.unusedSectionVars false in
/-- If `ker(d1) ⊆ im(d0)` (i.e. every closed cochain is exact), then the denominator
of `H1Cech` equals the whole numerator `ker(d1)`, so `H1Cech` is the zero module. -/
lemma h1Cech_denom_top_of_exact
    (hexact : LinearMap.ker (d1 R I) ≤ LinearMap.range (d0 R I)) :
    ((LinearMap.range (d0 R I)).comap (LinearMap.ker (d1 R I)).subtype) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro ⟨g, hg⟩
  simp only [Submodule.mem_comap, Submodule.coe_subtype]
  exact hexact hg

end Cech01

end AqeiBridge
