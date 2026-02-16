# aqei-bridge

A *bridge* repo: human conjecture → Lean language (toy formalization) → Mathematica heuristic “destruction” search → Lean lemma skeleton emission, orchestrated by Python.
This repository supports **two parallel publication tracks**:
1. **Formal verification** (Lean 4 formalization): `papers/aqei-lean-formalization.tex`
2. **Numerical validation** (computational methods): `papers/aqei-numerical-validation.tex`

See `papers/aqei-bridge-hybrid-workflow.md` for the living draft overview.
This repository is intentionally **independent** from the (still-in-review) CQG manuscript. When referencing prior work, prefer citing the unpublished manuscript rather than re-deriving or duplicating it:

- Related repo (reference only): https://github.com/DawsonInstitute/energy-tensor-cone
- Local directory: `~/Code/asciimath/energy-tensor-cone`
- Unpublished manuscript (CQG review): `~/Code/asciimath/energy-tensor-cone/papers/aqei-cone-formalization-cqg.tex`

## What is formal vs heuristic

- **Formalizable now (Lean):**
  - finite-dimensional `StressEnergy n := Fin n → ℝ`
  - linear AQEI-like functionals `StressEnergy n →ₗ[ℝ] ℝ` with bounds
  - `AQEI_cone` as an intersection of halfspaces
  - convexity theorem for `AQEI_cone`
  - typed conjecture *statements* (placeholders) about causal stability

- **Heuristic / experimental (Mathematica + pipeline):**
  - the PDE → observable reduction
  - any identification of Δ>0 with “cone advance”
  - the synthetic AQEI constraints used in the current toy search

Treat everything in `mathematica/` as **experimental**. Positive results are only *candidates* to refine and then formalize.

## Repo layout

```
aqei-bridge/
├── lean/                           # Lean 4 formalization (Mathlib)
│   ├── lean-toolchain
│   ├── lakefile.lean
│   └── src/AqeiBridge/
│       ├── Spacetime.lean                    # Lorentzian manifold definitions
│       ├── StressEnergy.lean                 # Finite-dimensional stress-energy
│       ├── AQEI_Cone.lean                    # AQEI cone as convex polyhedron
│       ├── CausalPoset.lean                  # Abstract causal preorder structure
│       ├── SpacetimeCausalPoset.lean         # Bridge: spacetime → poset
│       ├── CausalStability.lean              # Stability theorem statements
│       ├── CausalContinuity.lean             # Continuity of J⁺ under perturbations
│       ├── CausalIntervals.lean              # Order intervals and Alexandrov topology
│       ├── DiscreteCausalPoset.lean          # Directed graph causal models
│       ├── DiscreteCausality.lean            # Discrete reachability and J⁺
│       ├── DiscreteChronology.lean           # CTC detection in graphs
│       ├── DiscreteHomologyProxy.lean        # Chain complex and H₁ proxy
│       ├── PosetHomologyProxy.lean           # Functorial homology maps
│       ├── Chambers.lean                     # Parameter space chambers
│       ├── ChamberIndexedModel.lean          # Chamber-indexed causal structures
│       ├── ChamberClosedChamberBridge.lean   # Discrete chamber stability
│       ├── DiscreteChamberStability.lean     # Chamber-crossing analysis
│       ├── Conjecture.lean                   # Main conjecture statements
│       ├── GlobalConjectures.lean            # Global invariance statements
│       ├── GeneratedCandidates.lean          # Auto-generated from Mathematica
│       ├── GeneratedPosetConjectures.lean    # Auto-generated from Python sweeps
│       └── Tactics/                          # Custom tactics
├── mathematica/
│   ├── search.nb                   # Notebook interface for AQEI search
│   ├── search.wl                   # Batch script for symbolic optimization
│   ├── visualize_results.wl        # Post-processing and plotting
│   └── results/                    # Output JSON files
├── python/
│   ├── orchestrator.py             # Main workflow driver (all stages)
│   ├── analyze_candidates.py       # Parse Mathematica → Lean emission
│   ├── minkowski_poset.py          # Generate discrete Minkowski grids
│   ├── poset_homology_proxy.py     # H₁ computation and perturbation tests
│   ├── poset_interval_tools.py     # Order interval utilities
│   ├── causal_graph_tools.py       # Graph causality analysis
│   ├── ctc_scan.py                 # Closed timelike curve detection
│   ├── multi_ray_analysis.py       # Multi-ray Jaccard overlap proxy
│   ├── sweep_parameters.py         # Parameter space sweeps
│   └── sweep_analysis.py           # Aggregate sweep statistics
├── papers/
│   ├── aqei-lean-formalization.tex      # Manuscript 1: Lean 4 proofs
│   ├── aqei-numerical-validation.tex    # Manuscript 2: computational methods
│   └── aqei-bridge-hybrid-workflow.md   # Living draft overview
├── docs/
│   ├── TODO.md                     # High-priority immediate tasks
│   ├── TODO-backlog.md             # Lower-priority future work
│   ├── TODO-BLOCKED.md             # Blocked/underspecified items
│   ├── TODO-completed.md           # Completed task history
│   ├── architecture.md             # System design overview
│   ├── conjecture.md               # Mathematical conjecture statements
│   ├── toy-model.md                # Discrete model description
│   ├── phase4_searches.md          # Sweep workflow documentation
│   ├── h1_stability_results.md     # Empirical H₁ stability test results
│   ├── matlab_comsol_integration.md # MATLAB/COMSOL setup guide
│   └── history/                    # Chronological development log
├── tests/
│   ├── build_lean.sh               # Build Lean codebase
│   ├── lean_tests.sh               # Typecheck all Lean files
│   ├── mathematica_tests.sh        # Run Mathematica in test mode
│   ├── python_tests.sh             # Python unit tests
│   └── integration_tests.sh        # End-to-end pipeline tests
├── runs/                           # Timestamped run artifacts
│   └── <timestamp>/
│       ├── run.json                # Run metadata
│       └── artifacts/              # Outputs (graphs, JSON, logs)
├── results/                        # Persistent results (not timestamped)
├── run_tests.sh                    # Master test script (all 3267 jobs)
└── LICENSE
```

**Code inventory summary:**
- **Lean 4:** ~2500 lines across 20+ modules (formal definitions, theorems, conjectures)
- **Python:** ~3000 lines across 12 scripts (discrete models, homology, sweeps, analysis)
- **Mathematica:** ~800 lines (symbolic AQEI search, Green's function, visualization)
- **Tests:** Full test suite with 3267 jobs (Lean build, Python validation, Mathematica runs)
- **Documentation:** 10+ markdown files covering architecture, conjectures, results, integration guides

## Quick start

### Prereqs

- Wolfram engine / WolframScript on PATH (`wolframscript` preferred).
- Lean 4 + Lake (via `elan`), already present on your machine.
- Python 3.8+ with NetworkX, NumPy, SciPy

### Run the 4-stage loop

From repo root:

1) Stage III (heuristic search)

- `wolframscript -file mathematica/search.wl`

2) Stage IV (emit Lean skeletons)

- `python python/analyze_candidates.py`

3) Stage I (typecheck)

- `cd lean && lake build`

Or run the single orchestrator:

- `python python/orchestrator.py`

## Publication tracks

This repository supports two separate manuscripts currently in draft:

### 1. Formal Verification Track (`papers/aqei-lean-formalization.tex`)

**Target venue:** Formal methods / theorem proving conference (CPP, ITP, etc.)

**Focus:**
- Lean 4 formalization of AQEI cone convexity
- Discrete causal poset stability theorems
- Alexandrov topology bridge to Lorentzian causality
- Machine-checked proofs of H₁ invariance

**Current status:**
- Core definitions: complete
- Convexity theorems: proven
- Stability theorems: partial proofs (300 sorries remaining)
- Integration with Mathlib: ongoing

### 2. Numerical Validation Track (`papers/aqei-numerical-validation.tex`)

**Target venue:** Computational physics journal (CPC, JCP, etc.)

**Focus:**
- Hybrid symbolic-numeric AQEI search pipeline
- FFT-based perturbation testing and homology stability
- Multi-ray overlap analysis (path-connectedness proxy)
- MATLAB/COMSOL analog gravity integration

**Current status:**
- Core Python pipeline: complete
- Mathematica symbolic search: operational
- H₁ stability validation: 100% invariance over 100 trials
- MATLAB/COMSOL integration: planned (skeleton code documented)

Both manuscripts reference the hybrid workflow described in `papers/aqei-bridge-hybrid-workflow.md`.

## Recent progress

## Recent progress

**2026-02-16: Empirical H₁ stability validation and manuscript separation**
- Tested H₁ invariance under FFT perturbations: 100% stability across mild (ε=0.05) and strong (ε=0.3) perturbations
- Documented results in `docs/h1_stability_results.md`
- Created MATLAB/COMSOL integration guide (`docs/matlab_comsol_integration.md`)
- Separated publication tracks into two manuscripts:
  - `papers/aqei-lean-formalization.tex` (formal verification)
  - `papers/aqei-numerical-validation.tex` (computational methods)
- All tests green (3267 jobs)

**Earlier milestones:**
- Discrete reachability toy model and typed conjecture skeletons in Lean
- Order-theoretic bridge: causal preorders / causal posets and Alexandrov-style topology
- `Spacetime` → `CausalPoset` bridge under explicit axioms
- Phase 3 analysis tooling: multi-ray overlap summaries with connectedness proxy (mean pairwise Jaccard)
- Tests default to fast Mathematica runs (`--test-mode`) for CI efficiency

### Phase 4: searches (diagnostics)

- Sweep + aggregation workflow: see `docs/phase4_searches.md`.
- Over-scoped / underspecified items are tracked in `docs/TODO-BLOCKED.md` until we choose concrete, reproducible implementations.

### Phase 4 scope (tracked, but currently blocked)

The larger Phase 4 items (large-scale nondeterministic searches, realistic backgrounds, PDE solver-in-loop,
and a precise continuity topology for $J^+$) are tracked in `docs/TODO-BLOCKED.md` until we choose concrete
implementations that fit the repo’s reproducibility + CI constraints.

## Debugging / common failure modes

- **Mathematica script errors / huge output**
  - Start with the smallest test settings: `bash tests/mathematica_tests.sh`.
  - If Wolfram prints enormous expressions, it's usually a failed numeric path
    (e.g. symbolic leakage). Check `mathematica/search.wl` for any unevaluated
    symbols and force `N@` where needed.

- **WolframScript not found**
  - `tests/mathematica_tests.sh` will fall back to `wolfram -script`.
  - Ensure `which wolframscript` or `which wolfram` works.

- **Lean build fails / Mathlib cache mismatch**
  - The toolchain is pinned in `lean/lean-toolchain`.
  - If you see cache warnings, run `cd lean && lake build` once to sync.

- **Slow tests**
  - Reduce `AQEI_GRID` and `AQEI_NUM_CONSTRAINTS`.
  - Keep `AQEI_NUM_BASIS` small while iterating.

## Notes on the toy model

- Current search works in a 1+1 grid, builds Gaussian wavepacket basis functions, applies a scalar Fourier-space Green multiplier, then integrates a proxy field along several “null-ish” rays.
- This is an **ansatz** for quick iteration only.
- As the bridge paper matures, the constraints and observable must be replaced with ones justified by the manuscript and/or formal derivations.

## License

MIT (see `LICENSE`).
