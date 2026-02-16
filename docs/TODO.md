# TODO: Next Steps for AQEIBridge Workflow

Based on the latest commits (e.g., 5277e454 on Feb 14 adding canonical H1 invariance via homologyMap; 693374a2 functorial chain map on H1; 56fd396f induced chain map + H1 map; 7a1aafc1 invariance layer on poset homology proxy; a815570b low-degree isomorphism/validation; cab1fc39 VSCode chore; 1370dfe9 Z1 kernel bridge to Mathlib cycles; 56e3ca98 discrete sweep + Lean emission in Python; 0146af50 compiling poset chain-complex with H1; c823e9b4 compiling homology proxy + green tests), progress is strong on poset homology invariants—key for conjecture evidence (e.g., H1 = 0 preserved under perturbations implies no CTCs). No full proofs yet, but invariance layers support bridge conjecture stability.

## High-Priority Next Steps (1-2 days)

1. **Test H1 invariance under toy FFT perturbations** (tie to warp pathways)
   - Extend `poset_homology_proxy.py` with FFT-based edge perturbation
   - Run stability sweeps: `dim H₁(P') = dim H₁(P)` for small ε
   - Emit Lean stubs if stable across trials

2. **Sweep discrete posets for conjecture stubs**
   - Run on Minkowski grid posets with varying parameters
   - Document parameter regimes where H₁ stability holds
   - Generalize to non-Minkowski causal structures

3. **Generalize to continuous via Mathlib topology**
   - Bridge discrete poset results to topological spaces
   - Use Alexandrov topology on causal posets
   - Target: formal statement about limits of perturbations

4. **Expand manuscript with H1 evidence**
   - Add section on H₁ invariance under perturbations
   - Include LaTeX proofs and computational results
   - Frame as evidence for bridge conjecture stability

## Tool Migration & Simulation Setup

### MATLAB Integration
Move verification/simulations to MATLAB for flows/reachability PDEs. Focus on:
- Lorentzian flow simulations (metric evolution toward superluminal attractors)
- PDE-based reachability analysis
- Symbolic computation for GR invariants

**Installed Toolboxes:**
- Partial Differential Equation Toolbox (R2025b)
- Symbolic Math Toolbox (R2025b)
- Optimization Toolbox (R2025b)
- Global Optimization Toolbox (R2025b)
- Control System Toolbox (R2025b)
- Robust Control Toolbox (R2025b)

### COMSOL Multiphysics Setup
Use COMSOL for analog gravity multiphysics simulations:
- Acoustic horizons (fluid flows mimicking warped metrics)
- Effective metric evolution in fluids
- Metamaterial simulations for optical/EM analogs

**Recommended Modules:**
- **Acoustics Module**: Essential for acoustic horizons and analog gravity
- **CFD Module**: Fluid dynamics for effective metrics in analogs
- **AC/DC Module**: Metamaterial simulations (negative refraction, cloaking)
- **Optimization Module**: Constrained optimization for flows/metrics
- **Particle Tracing Module**: Null geodesic proxies in analogs

## Code Examples & Implementation Targets

### Python: FFT Perturbation for H₁ Stability

Extend `poset_homology_proxy.py`:

```python
import numpy as np
import networkx as nx
from scipy.fft import fft, ifft

def perturb_via_fft(graph, epsilon=0.01):
    """Apply FFT-based smooth perturbation to edge weights."""
    edges = list(graph.edges)
    weights = np.random.normal(1, epsilon, len(edges))  # AQEI-like noise
    fft_w = fft(weights)
    fft_w[10:] = 0  # Low-pass for smoothing
    pert_w = np.real(ifft(fft_w))
    pert_g = nx.DiGraph()
    for (u,v), w in zip(edges, pert_w):
        if w > 0: pert_g.add_edge(u, v, weight=w)
    return pert_g

def test_h1_invariance(graph, trials=10):
    """Test H₁ stability under perturbations."""
    orig_h1 = compute_h1_dim(graph)  # Your existing proxy
    pert_h1s = [compute_h1_dim(perturb_via_fft(graph)) for _ in range(trials)]
    return all(p == orig_h1 for p in pert_h1s)  # Stable if True
```

### Mathematica: Poset H₁ Visualization Post-Perturbation

```mathematica
points = Flatten[Table[{t, x}, {t, 0, 9}, {x, 0, 9}], 1];
precedes[p_, q_] := (q[[1]] - p[[1]]) > Abs[q[[2]] - p[[2]]];
edges = Select[Tuples[points, 2], precedes[#1, #2] &];
pertEdges = Select[edges, RandomReal[] < 0.99 &];  (* FFT proxy pert *)
Graph[pertEdges, VertexLabels -> Automatic]
```

### Lean: Invariance Under Small Perturbations

Extend `PosetHomologyProxy.lean`:

```lean
def PerturbationInducedMap {P P' : CausalPoset} (f : PosetMap P P') : 
    ChainMap (posetChainComplex P) (posetChainComplex P') := sorry

lemma H1InvariantUnderSmallPert (ε : ℝ) (h : SmallPert ε) : 
    ∀ f : PerturbationMap ε, IsIso (homologyMap (PerturbationInducedMap f) 1) := sorry
```

### MATLAB: Lorentzian Flow Simulation

```matlab
% LorentzianFlow.m - Evolve metric toward superluminal attractor
tspan = [0 1];
initial_g = -eye(4);  % Flat Minkowski
[t, g] = ode45(@(t,g) -2*ricci(g) + lambda_term(g), tspan, initial_g);
surf(t, g(:,1));  % Viz component; check for v>c paths

function dgdt = ricci(g)
    dgdt = zeros(size(g));  % Placeholder PDE; add GR terms
end

function lt = lambda_term(g)
    lt = 0.1 * (g - target_warped_g);  % Attract to warped
end
```

### COMSOL: Acoustic Horizon Analog (Java API)

```java
// COMSOL Java API snippet for acoustic horizon (warp analog)
Model model = ModelUtil.create("Model");
model.modelNode().create("mod1");
GeomFeature geom = model.geom().create("geom1", 2);
geom.feature().create("r1", "Rectangle").set("size", new double[]{1,1});
PhysFeature phys = model.physics().create("acpr", "PressureAcoustics", "geom1");
Study study = model.study().create("std1");
study.feature().create("acou1", "Acoustic");
model.sol().create("sol1").attach("std1");
model.result().create("pg1", "PlotGroup2D");
model.result("pg1").feature().create("surf1", "Surface");
model.result("pg1").run();  // Simulate fluid flow for effective metric
```

## Mathematical Framework

### H₁ Invariance Under Perturbations

For perturbed chain map $f_*: H_1(P) \to H_1(P')$, show it's an isomorphism if perturbation is small:

$$
f_*([c]) = [f(c)], \quad \|\delta\| < \epsilon \implies f_* \text{ iso if } H_1(P) \cong H_1(P + \delta)
$$

Key result: If $\dim H_1(P) = 0$ (no cycles), then small perturbations preserve this (chronology protection).

## Immediate Tasks

- [ ] Implement `perturb_via_fft` in `poset_homology_proxy.py`
- [ ] Run stability sweeps on Minkowski grid (tmax=10, xmax=10)
- [ ] Set up MATLAB PDE environment for metric flows
- [ ] Configure COMSOL Acoustics Module for first analog test
- [ ] Update manuscript with H₁ invariance section
- [ ] Document MATLAB/COMSOL integration in `docs/phase4_searches.md`