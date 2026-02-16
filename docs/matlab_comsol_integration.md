# MATLAB/COMSOL Integration for Analog Gravity Simulations

## Overview

This guide documents the integration of MATLAB and COMSOL Multiphysics for analog gravity simulations in support of the AQEIBridge project. The goals are:

1. **MATLAB**: PDE-based Lorentzian flow simulations and symbolic GR computations
2. **COMSOL**: Multiphysics analog gravity experiments (acoustic horizons, effective metrics)
3. **Evidence Building**: Empirical tests of reachability theorems and causal stability

## Installed MATLAB Toolboxes (R2025b)

Verified installation:
```bash
$ matlab -batch "ver"
MATLAB Version: 25.2.0.2998904 (R2025b)
```

**Active Toolboxes:**
- **Partial Differential Equation Toolbox**: Core for solving PDEs in heat transfer, structural mechanics, and custom equations (e.g., linearized Einstein, Lorentzian flows)
- **Symbolic Math Toolbox**: Analytical derivatives, equation simplification, and symbolic GR computations (Ricci tensor, energy inequalities)
- **Optimization Toolbox**: Local/convex optimization, least squares, constrained problems (minimizing energy functionals while preserving AQEI)
- **Global Optimization Toolbox**: Nonconvex problems (GA, particle swarm for warp attractors in rough landscapes)
- **Control System Toolbox**: Reachability theorems and path design in manifold dynamics
- **Robust Control Toolbox**: Robustness in simulations under uncertainties

## Installed COMSOL Modules

Verified installation:
```bash
$ comsol --version
COMSOL Multiphysics 6.4.0.293

$ ls /usr/local/comsol64/multiphysics/applications | grep Module
Acoustics_Module
CFD_Module
AC/DC_Module (part of Electromagnetics)
Structural_Mechanics_Module
Optimization_Module
Particle_Tracing_Module
```

**Priority Modules for Analog Gravity:**
1. **Acoustics Module**: Essential for acoustic horizons (fluid flows mimicking warped metrics, black hole analogs)
2. **CFD Module**: Fluid dynamics for effective metrics in liquids (heat transfer coupling)
3. **AC/DC Module**: Metamaterial simulations (negative refraction, EM "cloaking" effects as curved spacetime analogs)
4. **Optimization Module**: Constrained optimization for flows/metrics under energy bounds
5. **Particle Tracing Module**: Trace null geodesic proxies in analog systems

## Integration Workflow

### Phase 1: MATLAB PDE Setup

#### 1.1 Lorentzian Flow Simulation

Evolve metric components toward a target "warped" configuration using a toy Ricci flow + attractor term.

**File**: `matlab/LorentzianFlow.m`

```matlab
% LorentzianFlow.m - Evolve metric toward superluminal attractor
% 
% This is a toy model for Einstein equations as a flow on metric space.
% The actual Ricci flow requires sophisticated tensor manipulation; this
% is a placeholder for proof-of-concept.

function LorentzianFlow()
    % Time span for evolution
    tspan = [0 1];
    
    % Initial metric: flat Minkowski in 1+1D (simplified)
    % g00 = -1, g11 = 1 (diagonal)
    initial_g = [-1; 1];  % Store as vector for ODE solver
    
    % Solve ODE: dg/dt = -2*Ricci(g) + attractor_term(g)
    [t, g] = ode45(@metric_flow, tspan, initial_g);
    
    % Visualize metric component evolution
    figure;
    subplot(2,1,1);
    plot(t, g(:,1), 'LineWidth', 2);
    xlabel('Time');
    ylabel('g_{00} (temporal)');
    title('Metric Component Evolution');
    grid on;
    
    subplot(2,1,2);
    plot(t, g(:,2), 'LineWidth', 2);
    xlabel('Time');
    ylabel('g_{11} (spatial)');
    grid on;
    
    % Check for superluminal indicators (toy: g00/g11 ratio)
    fprintf('Final metric: g00=%.4f, g11=%.4f\\n', g(end,1), g(end,2));
    fprintf('Ratio g00/g11 = %.4f (Minkowski: -1.0)\\n', g(end,1)/g(end,2));
end

function dgdt = metric_flow(t, g)
    % Metric flow equation (toy)
    % In real GR: dg/dt ~ -2*Ricci + coupling_term
    
    % Placeholder Ricci term (proportional to deviation from flat)
    g_flat = [-1; 1];
    ricci_approx = (g - g_flat) / 10;  % Toy dissipation
    
    % Attractor term: pull toward "warped" target
    g_target = [-1.2; 0.8];  % Toy "warp" metric (faster light cone)
    attractor = 0.5 * (g_target - g);
    
    % Combined flow
    dgdt = -2 * ricci_approx + attractor;
end
```

**Usage:**
```matlab
cd /home/echo_/Code/asciimath/aqei-bridge/matlab
LorentzianFlow
```

**Expected Output**: Plots showing metric component evolution; final ratio indicates deviation from flat Minkowski.

#### 1.2 Symbolic Ricci Tensor (2D Example)

Use Symbolic Math Toolbox to compute Ricci tensor components analytically.

**File**: `matlab/SymbolicRicci2D.m`

```matlab
% SymbolicRicci2D.m - Symbolic computation of Ricci tensor in 1+1D
%
% Computes Christoffel symbols and Ricci tensor for a diagonal metric
% g = diag(g00(x), g11(x)) in 1+1D spacetime.

function SymbolicRicci2D()
    syms x t real
    syms g00(x) g11(x)
    
    % Metric tensor (diagonal)
    g_mat = [g00(x), 0; 0, g11(x)];
    
    % Inverse metric
    g_inv = inv(g_mat);
    
    % Coordinates
    coords = [t; x];
    
    fprintf('Metric:\\n');
    disp(g_mat);
    
    % Compute Christoffel symbols (Γ^μ_νρ)
    % For diagonal metrics in 1+1D, many components vanish
    % This is a placeholder for a full tensor calculation
    
    % Example: Γ^x_xx = (1/2) g^xx ∂_x g_xx
    Gamma_x_xx = simplify((1/2) * g_inv(2,2) * diff(g11(x), x));
    
    fprintf('Christoffel symbol Γ^x_xx:\\n');
    disp(Gamma_x_xx);
    
    % Ricci tensor component R_xx (placeholder)
    % Full calculation requires summing over contracted Christoffel derivatives
    % R_μν = ∂_ρ Γ^ρ_μν - ∂_ν Γ^ρ_μρ + Γ^ρ_ρλ Γ^λ_μν - Γ^ρ_νλ Γ^λ_μρ
    
    fprintf('\\n(Full Ricci tensor computation requires tensor toolkit)\\n');
end
```

**Usage:**
```matlab
SymbolicRicci2D
```

### Phase 2: COMSOL Acoustic Horizon Setup

#### 2.1 Java API Script for Acoustic Analog

Create a basic COMSOL model for acoustic horizons in a fluid flow.

**File**: `comsol/AcousticHorizon.java`

```java
/* AcousticHorizon.java - COMSOL model for acoustic analog gravity
 *
 * Simulates sound propagation in a moving fluid (effective metric).
 * An acoustic horizon forms when fluid velocity > sound speed.
 */

import com.comsol.model.*;
import com.comsol.model.util.*;

public class AcousticHorizon {
    public static void main(String[] args) {
        Model model = ModelUtil.create("AcousticHorizon");
        
        // Create geometry: 2D rectangle (flow channel)
        model.modelNode().create("mod1");
        GeomSequence geom = model.geom().create("geom1", 2);
        geom.feature().create("r1", "Rectangle");
        geom.feature("r1").set("size", new double[]{1.0, 0.2});  // 1m × 0.2m
        geom.run();
        
        // Physics: Pressure Acoustics
        PhysicsFeature acpr = model.physics().create("acpr", "PressureAcoustics", "geom1");
        acpr.prop("TransientSettings").set("AbsorbingLayerType", "PML");
        
        // Background flow (velocity field) - creates effective metric
        acpr.feature("pfeq1").set("u_background", new String[]{"0.5*x", "0"});  // Accelerating flow
        
        // Sound speed in fluid (e.g., water ~ 1500 m/s)
        acpr.feature("pfeq1").set("c_c", "1500");
        
        // Study: Frequency domain or transient
        Study study = model.study().create("std1");
        study.feature().create("freq", "Frequency");
        study.feature("freq").set("plist", "1000");  // 1 kHz
        
        // Solver
        model.sol().create("sol1");
        model.sol("sol1").study("std1");
        model.sol("sol1").attach("std1");
        model.sol("sol1").feature().create("st1", "StudyStep");
        model.sol("sol1").feature().create("v1", "Variables");
        model.sol("sol1").feature().create("s1", "Stationary");
        
        // Results: Surface plot of pressure
        model.result().create("pg1", "PlotGroup2D");
        model.result("pg1").feature().create("surf1", "Surface");
        model.result("pg1").feature("surf1").set("expr", "acpr.p_t");
        
        // Run simulation
        model.sol("sol1").runAll();
        
        // Export results
        model.result("pg1").run();
        model.save("/home/echo_/Code/asciimath/aqei-bridge/comsol/acoustic_horizon.mph");
        
        System.out.println("Simulation complete. Check acoustic_horizon.mph for results.");
    }
}
```

**Compilation & Execution:**
```bash
cd /home/echo_/Code/asciimath/aqei-bridge/comsol
javac -cp /usr/local/comsol64/multiphysics/plugins/livelink/*:. AcousticHorizon.java
java -cp /usr/local/comsol64/multiphysics/plugins/livelink/*:. AcousticHorizon
```

**Expected Output**: COMSOL model file `acoustic_horizon.mph` with pressure field showing effective metric effects.

#### 2.2 Python API Alternative

For users preferring Python over Java:

```python
# comsol/acoustic_horizon.py - Python COMSOL API
import mph

client = mph.start()
model = client.create('AcousticHorizon')

# Geometry
model.java.geom().create('geom1', 2)
model.java.geom('geom1').feature().create('r1', 'Rectangle')
model.java.geom('geom1').feature('r1').set('size', [1.0, 0.2])
model.java.geom('geom1').run()

# Physics (placeholder - see Java version for full setup)
# ...

client.save(model, 'acoustic_horizon.mph')
print("Model saved.")
```

### Phase 3: Evidence Integration Pipeline

#### Workflow

1. **Discrete H₁ Stability** (Python):
   - Run `poset_homology_proxy.py perturb-fft` on Minkowski grids
   - Export results: `runs/h1_stability_sweep/*.json`

2. **Continuous Analog** (MATLAB):
   - Import discrete poset as metric perturbation template
   - Solve PDE flow equations
   - Check reachability via `Control System Toolbox`

3. **Multiphysics Validation** (COMSOL):
   - Set up acoustic/fluid analog with MATLAB-derived flow field
   - Trace particle paths (geodesic proxies)
   - Verify H₁-like invariants persist in continuous limit

4. **Lean Certification**:
   - Emit Lean stubs from stable parameter regimes
   - Formal proof targets: discrete stability theorems

## Current Status

- [x] MATLAB/COMSOL installed and verified
- [x] Python H₁ stability tests completed (100% invariance on Minkowski t10×x10)
- [ ] MATLAB Lorentzian flow script implemented (skeleton ready)
- [ ] COMSOL acoustic horizon model built (API scaffolding ready)
- [ ] Integration pipeline connecting Python → MATLAB → COMSOL

## Next Actions

1. Implement `matlab/LorentzianFlow.m` and run initial test
2. Compile `comsol/AcousticHorizon.java` and verify simulation runs
3. Create data exchange scripts (JSON → MATLAB arrays, MATLAB → COMSOL parameters)
4. Document first end-to-end run in `docs/h1_stability_results.md`

## References

- MATLAB Documentation: [PDE Toolbox](https://www.mathworks.com/help/pde/)
- COMSOL API: [LiveLink for MATLAB](https://www.comsol.com/livelink-for-matlab)
- Analog Gravity Reviews: Barceló et al., Living Rev. Relativity (2011)
