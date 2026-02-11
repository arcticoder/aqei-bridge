# TODO: Active Queue for AQEIBridge Workflow

Focus on completing Phase 2 formalizations first (build on recent discrete toy), then iterate Phase 3 improvements. Limit to 5-10 items at a time; move completed to docs/TODO-completed.md.

## Phase 2: Formalize Core Concepts in Lean (High Priority)
- [ ] Formalize basic GR/spacetime structures in `Spacetime.lean`: Define Lorentzian manifolds, causal curves (γ with g(γ̇, γ̇) ≤ 0), future sets J⁺(p) = {q | ∃ causal γ from p to q}, small neighborhoods (ε-balls in chart topology). Use Mathlib.Analysis.NormedSpace and import Mathlib.Topology.Basic. Sample code:
  ```lean
  import Mathlib.Analysis.NormedSpace.Basic
  structure LorentzianManifold where
    metric : ∀ p : M, BilinForm (TangentSpace p) ℝ
    lorentz : ∀ p v, metric p v v ≤ 0 → timelike_or_null v
  def CausalCurve (p q : M) : Prop := ∃ γ : Curve p q, ∀ t, metric (γ t) (γ̇ t) (γ̇ t) ≤ 0
  def CausalFuture (p : M) : Set M := {q | CausalCurve p q}
  ```
- [ ] Complete `StressEnergy.lean`: Define finite-dim stress-energy tensors (e.g., as symmetric 4x4 matrices), map to metric perturbations via linearized Einstein (δG_{ab} = 8π δT_{ab}). Sample:
  ```lean
  structure StressEnergyTensor (M : Type*) [LorentzianManifold M] where
    components : ∀ p : M, SymMatrix ℝ 4
    energy_conditions : ∀ p k : NullVector, components p k k ≥ 0  -- Placeholder for AQEI
  def LinearizedEinstein (T : StressEnergyTensor) : MetricPerturbation := sorry  -- Use Ricci tensor approx
  ```
- [ ] Expand `AQEI_Cone.lean`: Formalize AQEI-admissible as convex cone (intersection of half-spaces from sampling functionals φ ≥ 0). Prove convexity using Mathlib.Convex.Basic. Sub-step: Add sampling-based constructor (list of linear functionals).
- [ ] In `CausalStability.lean`: State conjecture formally. Include homotopy class (use Mathlib.Algebra.Homology.Homotopy). Sample:
  ```lean
  conjecture CausalStability (M : LorentzianManifold) (p : M) (ε : ℝ) (hε : ε > 0) :
    ∀ T : StressEnergyTensor, AQEIAdmissible T ∧ Norm T < ε →
      PathConnected {J⁺(q) | q near p under perturbed metric g + h_T} ∧
      HomotopyEquivalent (GlobalCausalStructure M) (GlobalCausalStructure (M, g + h_T))
  ```
- [ ] Add basic lemmas in `CausalStability.lean`: Prove small perturbations preserve local causality (continuity of causal cones) and J⁺ continuity (using uniform topology on curves).

## Immediate Cross-Phase Tasks
- [ ] Add local test scripts: Expand `run_tests.sh` to include `lake build`, `wolframscript -file search.wl --test`, and `python -m unittest discover tests/`. Sample bash:
  ```bash
  #!/bin/bash
  lake build || exit 1
  wolframscript -file mathematica/search.wl --test-mode
  python python/orchestrator.py --test
  ```
- [ ] Start manuscript draft in `docs/manuscript.md`: Outline sections (Intro with conjecture, Toy pipeline, Formal statements, Bridge to topological chronology protection). Include LaTeX for conjecture.
```