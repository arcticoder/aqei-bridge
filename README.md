# aqei-bridge

Lean 4 formalization of AQEI causal stability: the *bridge* from stress-energy cone geometry to causal poset invariants.  
This repository contains the formal proofs, conjecture statements, and the Lean–Mathematica pipeline that drives the **formal verification track** of the bridge conjecture.

For the companion computational/numerical validation work, see [`aqei-numerical-validation`](https://github.com/arcticoder/aqei-numerical-validation).

## Relationship to companion repos

| Repo | Role |
|------|------|
| **this repo** | Lean 4 formal proofs, bridge conjecture, causal poset invariants |
| [`aqei-numerical-validation`](https://github.com/arcticoder/aqei-numerical-validation) | Discrete simulation, H₁ stability testing, Mathematica AQEI search, numerical manuscript |
| [`energy-tensor-cone`](https://github.com/arcticoder/energy-tensor-cone) | AQEI cone convexity proofs, extreme ray verification (submitted to Physical Review D, February 2026) |

The `energy-tensor-cone` PRD submission provides the convexity foundation (`AQEI_cone_convex`, `Candidate_Is_Extreme_Point`) that this repo builds on for causal stability. This repo is intentionally **independent** from it.

- Local directory: `~/Code/asciimath/energy-tensor-cone`
- Submitted manuscript: `~/Code/asciimath/energy-tensor-cone/papers/aqei-cone-formalization-prd.tex`

## Research goal

**Bridge conjecture:** Causal futures J^+(p) remain topologically stable (same H₁ invariant) under AQEI-admissible stress-energy perturbations.

**Global causality conjecture (longer term):** Chronology (absence of CTCs) is a topological invariant of causal posets — preserved under all AQEI-admissible perturbations.

## What is formalizable vs heuristic

- **Formalizable now (Lean):**
  - `StressEnergy n := Fin n → ℝ`, linear AQEI-like functionals
  - `AQEI_cone` as an intersection of halfspaces — **convexity proven**
  - Discrete causal posets (directed graphs), Alexandrov topology
  - Chain complex boundary map, `∂∂=0` — **proven**
  - H₁ proxy invariant — **functoriality + invariance proven** (see `PosetHomologyProxy.lean` and `H1Stability.lean`)
  - Typed conjecture statements for causal stability (proofs in progress)

- **Heuristic / numerical (see `aqei-numerical-validation`):**
  - FFT perturbation testing of H₁ stability (100% invariance over 100 trials)
  - Mathematica symbolic AQEI constraint search
  - Multi-ray Jaccard overlap proxy

## Repo layout

```
aqei-bridge/
├── lean/                           # Lean 4 formalization (Mathlib)
│   ├── lean-toolchain
│   ├── lakefile.lean
│   └── src/AqeiBridge/
│       ├── Spacetime.lean                    # Lorentzian manifold definitions
│       ├── StressEnergy.lean                 # Finite-dimensional stress-energy
│       ├── AQEI_Cone.lean                    # AQEI cone as convex polyhedron ✓
│       ├── CausalPoset.lean                  # Abstract causal preorder, Alexandrov topology ✓
│       ├── SpacetimeCausalPoset.lean         # Bridge: spacetime → poset
│       ├── CausalStability.lean              # Stability theorem statements
│       ├── CausalContinuity.lean             # Continuity of J⁺ under perturbations
│       ├── CausalIntervals.lean              # Order intervals and Alexandrov topology
│       ├── DiscreteCausalPoset.lean          # Directed graph causal models
│       ├── DiscreteCausality.lean            # Discrete reachability and J⁺
│       ├── DiscreteChronology.lean           # CTC detection in graphs
│       ├── DiscreteHomologyProxy.lean        # Chain complex and H₁ proxy ✓
│       ├── PosetHomologyProxy.lean           # Functorial homology maps (partial)
│       ├── Chambers.lean                     # Parameter space chambers
│       ├── ChamberIndexedModel.lean          # Chamber-indexed causal structures
│       ├── ChamberClosedChamberBridge.lean   # Discrete chamber stability
│       ├── DiscreteChamberStability.lean     # Chamber-crossing analysis
│       ├── Conjecture.lean                   # Main conjecture statements
│       ├── GlobalConjectures.lean            # Global invariance statements
│       ├── GeneratedCandidates.lean          # Auto-generated from Mathematica search
│       ├── GeneratedPosetConjectures.lean    # Auto-generated from Python sweeps
│       └── Tactics/                          # Custom tactics
├── python/
│   ├── orchestrator.py             # Main workflow driver (stages I-IV)
│   └── analyze_candidates.py       # Mathematica JSON → Lean skeleton emission
├── papers/
│   ├── aqei-lean-formalization.tex      # Manuscript: Lean 4 formal methods (CPP/ITP target)
│   └── aqei-bridge-hybrid-workflow.md   # Living draft overview of bridge conjecture
├── docs/
│   ├── TODO.md                     # High-priority active tasks
│   ├── TODO-backlog.md             # Lower-priority future work
│   ├── TODO-BLOCKED.md             # Blocked items
│   ├── TODO-completed.md           # Completed task history
│   ├── architecture.md             # System design overview
│   ├── conjecture.md               # Mathematical conjecture statements
│   ├── toy-model.md                # Discrete model description
│   ├── code-overview.md            # Newcomer guide to codebase
│   └── history/                    # Chronological development log
├── tests/
│   ├── build_lean.sh               # Build Lean codebase
│   └── lean_tests.sh               # Typecheck all Lean files
└── run_tests.sh                    # Master test script (Lean only)
```

**Code inventory:**
- **Lean 4:** ~2500 lines across 20+ modules
- **Python:** ~400 lines (pipeline glue: orchestrator + Lean skeleton emitter)
- **Numerical analysis (~3000 lines) and Mathematica search (~800 lines) are in** [`aqei-numerical-validation`](https://github.com/arcticoder/aqei-numerical-validation)

## Quick start

### Build Lean formalization

```bash
cd lean && lake build
```

### Emit Lean skeletons from Mathematica candidates

After running the Mathematica search in `aqei-numerical-validation`:

```bash
python python/analyze_candidates.py --input /path/to/aqei-numerical-validation/mathematica/results/top_candidates.json
```

### Run all tests

```bash
./run_tests.sh
```

## Publication track

### Formal Verification Track (`papers/aqei-lean-formalization.tex`)

**Target venue:** CPP / ITP (formal methods / theorem proving)

**Focus:** Lean 4 formalization of AQEI cone convexity, discrete causal poset stability, Alexandrov topology, H₁ invariance, real-world applications.

**Current status:** 10 pages, compiles. ~15 theorems proven, ~300 `sorry` obligations remaining.

**Empirical support:** See [`aqei-numerical-validation`](https://github.com/arcticoder/aqei-numerical-validation) — 100% H₁ invariance over 100 trials.

## Key proven theorems

| Theorem | File | Status |
|---------|------|--------|
| `AQEI_cone_convex` | `AQEI_Cone.lean` | ✓ proven |
| `causalFuture_open` | `CausalPoset.lean` | ✓ proven |
| `boundary_boundary_zero` | `DiscreteHomologyProxy.lean` | ✓ proven |
| `H1IsoZ1`, `H1IsoOfEdgeIso` | `PosetHomologyProxy.lean` | ✓ proven |
| `aqei_bridge_conjecture_discrete` | `CausalStability.lean` | axiom (proof target) |
| `admissible_region_pathConnected` | `CausalStability.lean` | ✓ proven (requires nonempty AQEI cone) |

## Foundation

[`energy-tensor-cone`](https://github.com/arcticoder/energy-tensor-cone) (PRD submission, February 2026) proves:
- `candidate_active_binding`: rational-exact vertex constraint satisfaction
- `Candidate_Is_Extreme_Point`: the AQEI cone has a verified non-trivial extreme point

This geometric foundation underpins this repo's causal stability direction.

## License

MIT (see `LICENSE`).
