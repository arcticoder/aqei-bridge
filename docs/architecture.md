# Architecture: AQEI-Bridge Lean 4 Formalization

This repository is a **pure formal methods project**: a Lean 4 library of
machine-checked proofs for the AQEI-bridge conjecture in the discrete
graph/poset toy model.

The previous Lean + Mathematica + Python hybrid workflow has been split out
into [`aqei-numerical-validation`](https://github.com/arcticoder/aqei-numerical-validation).
This repo is now exclusively the Lean formalization and its manuscript.

## Formalization layers

### 1. Mathematical structures (foundation)
- **Stress-energy vectors:** `StressEnergy n = Fin n → ℝ` (`StressEnergy.lean`)
- **AQEI cone:** Convex polyhedron as a finite halfspace intersection (`AQEI_Cone.lean`)
- **Abstract causal posets:** Preorder axiomatization of causal precedence (`CausalPoset.lean`)
- **Discrete graph model:** Finite directed graphs as causal posets
  (`DiscreteCausalPoset.lean`, `DiscreteCausality.lean`, `DiscreteChronology.lean`)

### 2. Homological invariants
- **Chain complex proxy** (`DiscreteHomologyProxy.lean`, `PosetHomologyProxy.lean`):
  low-degree chain complex C₀ ← C₁ ← C₂ with boundary maps; H₁ ≅ Z₁ proven.
- **Order complex** (`OrderComplexProxy.lean`, `OrderComplexBridge.lean`):
  simplicial construction, full `Z1_oc ↔ Z1` equivalence under `IsCompatible`.
- **Čech cochain complex** (`Cech01.lean`):
  minimal H¹ proxy `ker(d₁) / im(d₀)` for finite covers.

### 3. Main stability theorems

| Theorem | Statement | File |
|---------|-----------|------|
| `h1_stable_small_pert` | H₁=0 is monotone under subgraph inclusion | `H1Stability.lean` |
| `closedChamber_convex` | Chamber is a convex set | `Chambers.lean` |
| `admissible_region_pathConnected` | AQEI cone is path-connected (given nonemptiness) | `CausalStability.lean` |
| `aqei_bridge_conjecture_discrete` | Full bridge (H₁=0 + AQEI cone ∋ T) | `DiscreteStabilityBridge.lean` |

### 4. Quantitative continuity
- **Graph distance** (`GraphDistance.lean`): bounded shortest-path proxy `boundedDist`.
- **Hausdorff bound** (`DiscreteFutureContinuity.lean`):
  `jplus_discreteHausdorff_coverage` gives `discreteHausdorff ≤ n` for n-node graphs.

## Build and test

```bash
# Single clean build (Mathlib noise filtered, diagnostics from src/ shown):
./run_tests.sh

# Or manually:
cd lean && lake build
```

The test runner writes a filtered log to `lean/build.log`.

## Key invariants

- **Zero `sorry`:** All main theorems are fully proven.
- **Formal/conjectural separation:** Open conjectures are in `Conjecture.lean`
  and `GlobalConjectures.lean`, clearly labeled.
- **No overclaims:** The library models a discrete graph toy model, not
  full Lorentzian QFT. Realistic generalizations remain future work.

## Related repositories
- [`energy-tensor-cone`](https://github.com/DawsonInstitute/energy-tensor-cone):
  infinite-family AQEI cone formalization, extreme rays, closedness proofs.
- [`aqei-numerical-validation`](https://github.com/arcticoder/aqei-numerical-validation):
  numerical/Mathematica validation pipeline (split from this repo 2026-02-22).
