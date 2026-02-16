# Code Overview: AQEIBridge Repository

This document provides a guided tour of the codebase for newcomers, organized by language and purpose.

**Last updated:** 2026-02-16

---

## Lean 4 Formalization (`lean/src/AqeiBridge/`)

The formal verification layer: machine-checked mathematical definitions and proofs.

### Core Mathematical Structures

#### `StressEnergy.lean`
- **Purpose:** Finite-dimensional stress-energy tensor representation
- **Key types:**
  - `StressEnergy n := Fin n → ℝ` (n-component coefficient vector)
  - `LinearConstraint n := StressEnergy n →ₗ[ℝ] ℝ` (linear functionals)
- **Key theorems:** None yet (foundation only)
- **Dependencies:** Mathlib linear algebra

#### `AQEI_Cone.lean`
- **Purpose:** AQEI-admissible region as a convex polyhedron
- **Key definitions:**
  - `aqei_cone n m constraints`: Intersection of m halfspaces in ℝⁿ
- **Key theorems:**
  - `aqei_cone_convex`: Convexity proof via halfspace intersection
- **Dependencies:** `StressEnergy.lean`, Mathlib convex analysis

#### `Spacetime.lean`
- **Purpose:** Lorentzian manifold structure (placeholder for future work)
- **Key types:**
  - `Spacetime`: Smooth manifold with Lorentzian metric signature
  - `CausalCurve M g p q`: Predicate for causal curves
- **Status:** Axiomatized interface; full diff-geo formalization pending
- **Dependencies:** Mathlib manifolds (future integration)

### Causal Structure

#### `CausalPoset.lean`
- **Purpose:** Abstract causal preorder axiomatization
- **Key types:**
  - `CausalPoset`: A preorder (reflexive, transitive) representing causal precedence
  - `causalFuture p`: The set J⁺(p) = {q | p ≤ q}
- **Key theorems:**
  - `causalFuture_mono`: Monotonicity of J⁺
  - `causalFuture_union`: J⁺(p ∪ q) = J⁺(p) ∪ J⁺(q)
- **Dependencies:** Mathlib order theory

#### `SpacetimeCausalPoset.lean`
- **Purpose:** Bridge from Lorentzian spacetime to causal poset
- **Key constructions:**
  - `spacetimeToPoset`: Functor mapping (M, g) to abstract causal preorder
  - Axioms: `causalCurve_refl`, `causalCurve_trans`
- **Status:** Interface layer only; full proof requires Lorentzian geometry formalization
- **Dependencies:** `Spacetime.lean`, `CausalPoset.lean`

#### `CausalIntervals.lean`
- **Purpose:** Order intervals and Alexandrov topology
- **Key definitions:**
  - `orderInterval p q`: Future of p ∩ past of q
  - `AlexandrovTopology`: Topology where upper sets are open
- **Key theorems:**
  - `causalFuture_open`: J⁺(p) is open in Alexandrov topology
- **Dependencies:** `CausalPoset.lean`, Mathlib topology

#### `CausalContinuity.lean`
- **Purpose:** Continuity of J⁺ under metric perturbations
- **Key statements:**
  - `causalFuture_continuous`: J⁺ is continuous in suitable topology (conjecture)
- **Status:** Skeleton only; proof pending
- **Dependencies:** `Spacetime.lean`, `CausalPoset.lean`, Mathlib topology

### Discrete Models

#### `DiscreteCausalPoset.lean`
- **Purpose:** Causal poset realized as a directed graph
- **Key types:**
  - `DiscretePoset V`: Nodes V with edge relation →
- **Key constructions:**
  - `transitiveClosure`: Compute J⁺ via graph reachability
- **Dependencies:** Mathlib graph theory (Quiver)

#### `DiscreteCausality.lean`
- **Purpose:** Discrete reachability and causal future computation
- **Key algorithms:**
  - `reachableFrom v`: BFS/DFS to compute J⁺(v)
- **Status:** Computational model only; connects to NetworkX Python implementation
- **Dependencies:** `DiscreteCausalPoset.lean`

#### `DiscreteChronology.lean`
- **Purpose:** CTC detection in directed graphs
- **Key definitions:**
  - `hasCTC G`: Predicate for cycles in transitive closure
- **Key algorithms:**
  - `detectCycle`: Tarjan's SCC algorithm wrapper
- **Status:** Placeholder; Python implementation is authoritative
- **Dependencies:** `DiscreteCausalPoset.lean`

### Homological Invariants

#### `DiscreteHomologyProxy.lean`
- **Purpose:** Chain complex construction on directed graphs
- **Key types:**
  - `ChainComplex n`: ℤ-modules with boundary maps ∂ₙ
  - `boundary1`: Edge → vertex incidence map (∂(p→q) = q - p)
- **Key definitions:**
  - `Z1 := ker(∂₁)`: 1-cycle space
  - `z1Dim`: Dimension of Z₁ (topological invariant proxy)
- **Key theorems:**
  - `boundary_boundary_zero`: ∂² = 0 (chain complex axiom)
- **Dependencies:** Mathlib homology (algebra.homology)

#### `PosetHomologyProxy.lean`
- **Purpose:** Functorial homology maps under poset morphisms
- **Key constructions:**
  - `inducedChainMap f`: Poset map f : P → P' induces chain map f* : C(P) → C(P')
  - `homologyMap f n`: Induced map on Hₙ
- **Key theorems:**
  - `homology_functorial`: (g ∘ f)* = g* ∘ f*
  - `h1_preserves_zero` (conjecture): If H₁(P) = 0, small perturbations preserve this
- **Dependencies:** `DiscreteHomologyProxy.lean`, Mathlib category theory

### Stability and Conjectures

#### `CausalStability.lean`
- **Purpose:** Stability of causal structure under stress-energy perturbations
- **Key statements:**
  - `aqei_bridge_conjecture_discrete`: Path-connectedness of {J⁺(p)_T | T ∈ AQEI_cone, ||T - T₀|| < δ}
- **Status:** Conjecture formalized; proof obligations remain (300 sorries)
- **Dependencies:** `AQEI_Cone.lean`, `CausalPoset.lean`, Mathlib topology

#### `Chambers.lean`
- **Purpose:** Parameter space partitioned into chambers (convex regions)
- **Key types:**
  - `Chamber`: Convex subset of parameter space
  - `chamberWalls`: Boundaries where constraints become active/inactive
- **Dependencies:** `AQEI_Cone.lean`, Mathlib convex geometry

#### `ChamberIndexedModel.lean`
- **Purpose:** Causal structures indexed by chambers
- **Key constructions:**
  - `chamberToCausalPoset c`: Map each chamber to a causal poset
- **Status:** Interface layer for multi-parameter analysis
- **Dependencies:** `Chambers.lean`, `CausalPoset.lean`

#### `DiscreteChamberStability.lean`
- **Purpose:** Stability of discrete causal structure when crossing chamber walls
- **Key conjectures:**
  - `chamber_stability`: H₁ invariant within chamber interior
- **Dependencies:** `ChamberIndexedModel.lean`, `DiscreteHomologyProxy.lean`

#### `Conjecture.lean`
- **Purpose:** Main conjecture statements (human-readable)
- **Key statements:**
  - `AQEI_implies_causality_stability`: AQEI constraints prevent CTC formation
  - `path_connected_futures`: Smooth variation of J⁺
- **Dependencies:** All core modules

#### `GlobalConjectures.lean`
- **Purpose:** Global invariance statements (compilation-safe placeholders)
- **Key skeletons:**
  - `global_h1_invariance`: H₁ invariant under all AQEI perturbations (to be refined)
- **Dependencies:** `PosetHomologyProxy.lean`, `Conjecture.lean`

### Auto-Generated Files

#### `GeneratedCandidates.lean`
- **Purpose:** Lean definitions emitted from Mathematica search results
- **Source:** `python/analyze_candidates.py` parses `mathematica/results/top_candidates.json`
- **Content:** Stress-energy coefficient vectors as Lean terms
- **Example:**
  ```lean
  def candidate_0 : StressEnergy 10 := ![0.5, -0.3, 0.1, ...]
  ```

#### `GeneratedPosetConjectures.lean`
- **Purpose:** Conjectures emitted from Python parameter sweeps
- **Source:** `python/poset_homology_proxy.py sweep-minkowski`
- **Content:** Stability statements for specific grid parameters
- **Example:**
  ```lean
  -- Minkowski 10×10 grid: dim Z₁ = 190
  axiom minkowski_10_10_z1 : z1Dim (minkowskiPoset 10 10) = 190
  ```

---

## Python Pipeline (`python/`)

Discrete causal models, homology computation, sweep orchestration, and Lean code generation.

### Core Workflow

#### `orchestrator.py`
- **Purpose:** Master workflow driver (all 4 stages)
- **Usage:** `python orchestrator.py [--test-mode]`
- **Stages:**
  1. Lean typecheck (`cd lean && lake build`)
  2. Python setup (validate imports)
  3. Mathematica search (`wolframscript mathematica/search.wl`)
  4. Analysis & Lean emission (`analyze_candidates.py`)
- **Outputs:** Timestamped run directory under `runs/<timestamp>/`

#### `analyze_candidates.py`
- **Purpose:** Parse Mathematica JSON results → emit Lean code
- **Input:** `mathematica/results/top_candidates.json`
- **Output:** `lean/src/AqeiBridge/GeneratedCandidates.lean`
- **Key functions:**
  - `parse_json()`: Load and validate Mathematica output
  - `rationalize_floats()`: Convert floats to Lean-compatible rationals
  - `emit_lean_defs()`: Generate Lean definition strings

### Discrete Causal Models

#### `minkowski_poset.py`
- **Purpose:** Generate discrete Minkowski grid causal posets
- **Usage:** Can be imported or run standalone for JSON export
- **Key functions:**
  - `generate_minkowski_poset(tmax, xmax)`: Create NetworkX DiGraph
  - Causal edge rule: `(t2 - t1) > abs(x2 - x1)` (lightcone condition)
- **Output format:** NetworkX JSON graph serialization

#### `causal_graph_tools.py`
- **Purpose:** General causal analysis on directed graphs
- **Key functions:**
  - `compute_causal_future(G, node)`: BFS reachability
  - `causal_diamond(G, p, q)`: J⁺(p) ∩ J⁻(q)
  - `is_acyclic(G)`: Check for CTCs
- **Dependencies:** NetworkX

#### `ctc_scan.py`
- **Purpose:** Detect closed timelike curves in graph JSON files
- **Usage:** `python ctc_scan.py <graph.json>`
- **Algorithm:** Tarjan's strongly connected components
- **Output:** Boolean + cycle listing (if detected)
- **Testing:** Used in `tests/python_tests.sh` for validation

### Homological Invariants

#### `poset_homology_proxy.py`
- **Purpose:** Compute H₁ proxy and run perturbation stability tests
- **Subcommands:**
  - `compute-z1 <graph.json>`: Output dim Z₁
  - `sweep-minkowski --tmaxs t1,t2,... --xmaxs x1,x2,...`: Generate grid family
  - `perturb-fft <graph.json> --trials N --epsilon E`: FFT-based edge perturbations
  - `scan-minkowski-perturb`: Cone-widening perturbation scan
  - `sweep-minkowski-perturb`: Combined sweep + perturbation
- **Key functions:**
  - `compute_z1_dim(G)`: |E| - |V| + c (connected components)
  - `perturb_via_fft(G, epsilon, threshold, window)`: Smooth edge dropout
  - `cone_widening_perturb(G, alpha_min, alpha_max)`: Lightcone slope variation
- **Output:** JSON with `{z1Dim, fractionUnchanged, maxAbsDeltaZ1, meanAbsDeltaZ1, trials}`
- **Integration:** Emits Lean code to `GeneratedPosetConjectures.lean`

#### `poset_interval_tools.py`
- **Purpose:** Order interval computations (future ∩ past)
- **Key functions:**
  - `order_interval(G, p, q)`: J⁺(p) ∩ J⁻(q)
  - `alexandrov_open_sets(G)`: Generate upper sets (Alexandrov topology)
- **Status:** Utility library; used by other scripts

### Parameter Sweeps and Analysis

#### `sweep_parameters.py`
- **Purpose:** Systematically sweep AQEI constraint parameters
- **Usage:** `python sweep_parameters.py --grid-sizes 5,10,15 --num-constraints 50,100,200`
- **Outputs:** One Mathematica run per parameter combination
- **Integration:** Calls `wolframscript mathematica/search.wl` with env vars

#### `sweep_analysis.py`
- **Purpose:** Aggregate sweep results and compute statistics
- **Input:** Multiple `runs/<timestamp>/artifacts/` directories
- **Key metrics:**
  - Max observable across all runs
  - Active constraint frequency histogram
  - Chamber boundary crossings
- **Output:** CSV summary + plots (via matplotlib, if available)

#### `multi_ray_analysis.py`
- **Purpose:** Multi-ray constraint-set overlap (path-connectedness proxy)
- **Input:** Mathematica JSON with multi-ray results
- **Key metrics:**
  - Pairwise Jaccard similarity: |C_i ∩ C_j| / |C_i ∪ C_j|
  - Mean Jaccard
  - Connectedness proxy: fraction of pairs above threshold θ
  - Connectivity threshold estimate (via sweep over θ)
- **Output:** JSON with `{meanJaccard, connProxy, connThreshold}`
- **Usage:** `python multi_ray_analysis.py <results.json> [--theta 0.5]`

---

## Mathematica (`mathematica/`)

Symbolic AQEI constraint solving and heuristic search.

### Search Scripts

#### `search.nb`
- **Purpose:** Interactive notebook for exploratory search
- **Contents:**
  - Gaussian wavepacket basis generation
  - Fourier-space Green's function (scalar toy model)
  - Ray-path integration of proxy observable
  - Visualization of constraint polytope
- **Usage:** Open in Mathematica desktop app

#### `search.wl`
- **Purpose:** Batch script for automated runs (CI-friendly)
- **Key parameters (env vars or defaults):**
  - `AQEI_GRID`: Grid resolution (default 16)
  - `AQEI_NUM_BASIS`: Number of basis functions (default 5)
  - `AQEI_NUM_CONSTRAINTS`: Number of linear AQEI constraints (default 10)
  - `AQEI_NUM_RAYS`: Number of null-ish rays to integrate (default 1)
- **Algorithm:**
  1. Generate basis in Fourier space (Gaussians)
  2. Build Green's function response (scalar field)
  3. For each ray:
     - Integrate proxy observable along ray
     - Maximize subject to AQEI constraints (NMaximize)
  4. Export top candidates to JSON
- **Output:** `mathematica/results/top_candidates.json`
- **Test mode:** `AQEI_TEST_MODE=1` reduces grid/basis for fast CI
- **Dependencies:** Optimization, Symbolic Math toolboxes

#### `visualize_results.wl`
- **Purpose:** Post-processing and plotting
- **Key functions:**
  - `PlotConstraintPolytope`: 2D/3D polytope visualization
  - `PlotActiveConstraints`: Heatmap of active constraint frequency
- **Input:** JSON results from `search.wl`
- **Output:** PNG/PDF plots in `mathematica/results/`

### Results Directory

#### `mathematica/results/`
- **Contents:**
  - `summary.json`: Aggregate statistics (mean, max, std dev of observable)
  - `top_candidates.json`: Optimal stress-energy coefficients + active constraints
  - `*.png`: Plots (if visualization script is run)
- **Persistence:** Copied to `runs/<timestamp>/artifacts/` by orchestrator

---

## Tests (`tests/`)

Validation and CI infrastructure.

### Individual Test Scripts

#### `build_lean.sh`
- **Purpose:** Build Lean codebase and check for errors
- **Command:** `cd lean && lake build`
- **Output:** Build log + error count
- **Exit code:** 0 if build succeeds, 1 otherwise

#### `lean_tests.sh`
- **Purpose:** Typecheck all Lean files (stricter than build)
- **Command:** `cd lean && lake build && lake env lean --run src/AqeiBridge.lean`
- **Checks:** No sorries in critical theorems (optional lint)

#### `mathematica_tests.sh`
- **Purpose:** Run Mathematica search in test mode
- **Environment:** `AQEI_TEST_MODE=1` (reduced grid/basis)
- **Command:** `wolframscript -file mathematica/search.wl`
- **Validation:** Check JSON output schema
- **Exit code:** 0 if JSON is valid, 1 otherwise

#### `python_tests.sh`
- **Purpose:** Python unit tests and validation
- **Tests:**
  - Import all modules (syntax check)
  - `compute_z1_dim` on known graphs
  - JSON parsing roundtrip
  - CTC detection on artificial cycles
- **Framework:** Plain assertions (no pytest/unittest dependency)
- **Exit code:** 0 if all assertions pass, 1 otherwise

#### `integration_tests.sh`
- **Purpose:** End-to-end pipeline test
- **Steps:**
  1. Generate Minkowski graph (Python)
  2. Compute Z₁ (Python)
  3. Run Mathematica search (test mode)
  4. Parse results and emit Lean (Python)
  5. Typecheck generated Lean (Lake)
- **Exit code:** 0 if all stages succeed

### Master Test Script

#### `run_tests.sh`
- **Purpose:** Run all tests (Lean + Mathematica + Python + integration)
- **Usage:** `./run_tests.sh`
- **Output:** Combined log with per-stage results
- **Total jobs:** 3267 (mostly Lean build parallelism)
- **CI integration:** GitHub Actions calls this script
- **Green status:** All tests pass as of 2026-02-16

---

## Documentation (`docs/`)

Living documentation for architecture, conjectures, results, and issue tracking.

### Planning and Tracking

#### `TODO.md`
- **Purpose:** High-priority immediate tasks (1-2 days)
- **Format:** Checklist with status markers
- **Current focus:** H₁ stability validation, MATLAB/COMSOL integration
- **Update frequency:** Daily during active development

#### `TODO-backlog.md`
- **Purpose:** Lower-priority future work (weeks-months)
- **Examples:** Extended Mathlib integration, higher-order homology, realistic QFT constraints

#### `TODO-BLOCKED.md`
- **Purpose:** Items blocked by external dependencies or underspecified
- **Examples:** Full Lorentzian geometry formalization, experimental analog gravity validation

#### `TODO-completed.md`
- **Purpose:** Historical record of completed tasks
- **Format:** Date-stamped entries

### Architectural Documentation

#### `architecture.md`
- **Purpose:** High-level system design overview
- **Sections:**
  - 4-stage workflow (Lean → Python → Mathematica → Python → Lean)
  - Data flow diagrams
  - Module dependency graph
- **Target audience:** New contributors

#### `conjecture.md`
- **Purpose:** Mathematical statements of main conjectures
- **Format:** LaTeX math in Markdown
- **Key conjectures:**
  - AQEI bridge (path-connectedness of J⁺ families)
  - H₁ stability under perturbations
  - Chronology protection via topological invariants
- **Status annotations:** Formalized, partially proven, open

#### `toy-model.md`
- **Purpose:** Detailed description of discrete causal poset model
- **Sections:**
  - Minkowski grid construction
  - Edge relation rules (lightcone condition)
  - Homology proxy definition (Z₁ dimension)
  - Limitations and scope

### Results and Integration

#### `h1_stability_results.md`
- **Purpose:** Empirical validation results for H₁ invariance
- **Created:** 2026-02-16
- **Contents:**
  - Baseline Minkowski 10×10 grid (121 nodes, 310 edges, dim Z₁ = 190)
  - FFT perturbation test 1 (ε=0.05): 100% invariance over 50 trials
  - FFT perturbation test 2 (ε=0.3): 100% invariance over 50 trials
  - Mathematical framework and interpretation
  - Caveats (discrete only, toy model)

#### `matlab_comsol_integration.md`
- **Purpose:** Integration guide for MATLAB/COMSOL analog gravity tools
- **Created:** 2026-02-16
- **Contents:**
  - MATLAB R2025b toolbox verification (PDE, Optimization, Control)
  - COMSOL 6.4 module verification (Acoustics, CFD, AC/DC)
  - Skeleton code for Lorentzian flow PDE solver (MATLAB)
  - Skeleton code for acoustic horizon analog (COMSOL Java API)
  - Data exchange pipeline (Python ↔ MATLAB ↔ COMSOL JSON)
- **Status:** Planned (skeleton code only; not yet implemented)

#### `phase4_searches.md`
- **Purpose:** Workflow documentation for parameter sweeps
- **Sections:**
  - Sweep strategy (grid resolution, constraint count, basis size)
  - Aggregation methods (max, mean, variance)
  - Reproducibility (random seeds, versioning, artifact storage)
  - Multi-ray analysis integration

### Historical Log

#### `history/`
- **Purpose:** Chronological development log
- **Format:** Markdown files by date or milestone
- **Latest entry:** 2026-02-16 (H₁ stability validation, manuscript separation)

---

## Artifacts and Results (`runs/`, `results/`)

Persistent and timestamped outputs from pipeline runs.

### Timestamped Runs (`runs/`)

Each orchestrator invocation creates a directory `runs/<timestamp>/`:

**Structure:**
```
runs/2026-02-16T14-30-45/
├── run.json               # Metadata: parameters, git commit, timestamps
├── artifacts/
│   ├── minkowski_t10_x10.json   # Generated graph
│   ├── fft_pert_results.json    # Perturbation test results
│   ├── top_candidates.json      # Mathematica search output (copy)
│   └── *.log                    # Stage-specific logs
└── generated_lean/
    └── GeneratedCandidates.lean  # Auto-generated Lean code (copy)
```

**Retention:** All runs are kept for reproducibility tracing.

### Persistent Results (`results/`)

Curated results (not timestamped):

- Best candidates across all runs
- Publication-quality plots
- Aggregated statistics CSVs

**Workflow:** Manual curation from `runs/` artifacts.

---

## Papers (`papers/`)

Draft manuscripts for publication.

#### `aqei-lean-formalization.tex`
- **Track:** Formal verification
- **Target:** Theorem proving conference (CPP, ITP)
- **Contents:** Lean 4 formalization, convexity proofs, discrete stability theorems
- **Status:** Draft (300 sorries remaining in Lean proofs)

#### `aqei-numerical-validation.tex`
- **Track:** Computational methods
- **Target:** Computational physics journal (CPC, JCP)
- **Contents:** Hybrid pipeline, FFT perturbations, multi-ray analysis, MATLAB/COMSOL integration
- **Status:** Draft (MATLAB/COMSOL code not yet implemented)

#### `aqei-bridge-hybrid-workflow.md`
- **Purpose:** Living draft overview (Markdown for easy iteration)
- **Contents:** Unified narrative for both publication tracks
- **Status:** Active development; feeds into both .tex manuscripts

---

## Contributing

For newcomers:

1. **Start here:**
   - Read `README.md` (this file)
   - Skim `docs/architecture.md` for workflow overview
   - Read `docs/conjecture.md` for mathematical context

2. **Build and test:**
   - `./run_tests.sh` (ensure all green)
   - `python orchestrator.py --test-mode` (fast end-to-end run)

3. **Pick a task:**
   - Check `docs/TODO.md` for high-priority items
   - Look for `-- TODO` or `sorry` in Lean code for proof opportunities
   - Check GitHub issues (if repo is public)

4. **Development workflow:**
   - Lean changes: Edit `.lean` files → `cd lean && lake build` → check errors
   - Python changes: Edit `.py` files → `bash tests/python_tests.sh` → verify
   - Mathematica changes: Edit `search.wl` → `bash tests/mathematica_tests.sh` → validate JSON

5. **Commit conventions:**
   - Descriptive messages with context
   - Reference TODO.md items or issue numbers
   - Keep test suite green before pushing

---

## Further Reading

- **Formal methods:** [Lean 4 tutorial](https://lean-lang.org/theorem_proving_in_lean4/)
- **Mathlib:** [Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- **Causal sets:** Bombelli et al., *Phys. Rev. Lett.* 59, 521 (1987)
- **AQEI:** Fewster, *Lectures on quantum energy inequalities*, arXiv:1208.5399
- **Chronology protection:** Hawking, *Phys. Rev. D* 46, 603 (1992)

---

**Questions?** Open an issue or contact the maintainer.
