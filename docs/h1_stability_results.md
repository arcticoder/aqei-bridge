# H₁ Stability Under FFT Perturbations: Empirical Results

## Summary

Tested H₁ invariance on Minkowski grid poset (tmax=10, xmax=10) under toy FFT-based edge perturbations. Results show **perfect stability** (100% invariance) across multiple parameter regimes.

## Baseline Graph

- **Grid**: 11×11 Minkowski lattice (t ∈ [0,10], x ∈ [0,10])
- **Nodes**: 121
- **Edges**: 310 (directed, causal)
- **Weak Components**: 1 (connected)
- **H₁ dimension (Z₁)**: 190
- **Has Directed Cycles**: False (chronological)

## Perturbation Model

The FFT perturbation model:
1. Assign each edge a baseline weight w₀ = 1.0
2. Generate Gaussian noise ξᵢ ~ N(0,1) for each edge
3. Apply cyclic moving-average low-pass filter (window=9)
4. Perturb weights: wᵢ = 1.0 + ε·smooth(ξ)ᵢ
5. Drop edges where wᵢ < threshold

This mimics smooth metric perturbations in continuum limit.

## Results

### Test 1: Mild Perturbation
- **Parameters**: ε=0.05, threshold=0.5, window=9, seed=42
- **Trials**: 50
- **Output**: `runs/h1_stability_sweep/fft_pert_t10_x10.json`

**Results:**
- `fractionUnchanged`: **1.0** (100%)
- `meanAbsDeltaZ1`: **0.0**
- `maxAbsDeltaZ1`: **0**
- All 50 trials: Z₁ dimension remained at 190
- Verdict: **Perfect H₁ invariance**

### Test 2: Strong Perturbation  
- **Parameters**: ε=0.3, threshold=0.3, window=9, seed=42
- **Trials**: 50
- **Output**: `runs/h1_stability_sweep/fft_pert_strong.json`

**Results:**
- `fractionUnchanged`: **1.0** (100%)
- `meanAbsDeltaZ1`: **0.0**
- `maxAbsDeltaZ1`: **0**
- Verdict: **Perfect H₁ invariance** (even at 6× noise amplitude)

## Interpretation

### What This Means

The empirical stability $\dim H_1(P') = \dim H_1(P)$ under FFT perturbations suggests:

1. **Chronology Protection (Toy)**: If $H_1(P) = 0$ (no cycles in the proxy), small smooth perturbations preserve this.
2. **Robustness of Z₁**: The kernel dimension of the boundary operator $\partial_1$ is stable under edge dropout when perturbations are smooth (low-pass filtered).
3. **Bridge Conjecture Evidence**: This supports the conjecture that $H_1$ is a stable topological invariant for causal structures under small AQEI-admissible perturbations.

### Caveats

- **Discrete Model Only**: This is a toy finite poset, not a Lorentzian spacetime.
- **Not a CTC Detector**: Z₁ ≠ 0 does not imply CTCs (DAGs can have nonzero Z₁).
- **Toy Perturbation**: The FFT low-pass model is a heuristic proxy for smooth metric perturbations, not a rigorous GR calculation.

## Mathematical Framework

For the boundary map $\partial_1: C_1 \to C_0$ with $\partial_1(e: p \to q) = q - p$, we have:

$$
\dim Z_1 = \dim \ker(\partial_1) = |E| - \text{rank}(\partial_1) = |E| - |V| + c
$$

where $c$ is the number of weakly connected components.

**Stability Condition**: The perturbation map $f: P \to P'$ induces a chain map $f_*$ such that:

$$
f_*([z]) = [f(z)] \in H_1(P'), \quad \text{preserves } \dim H_1
$$

when $\|\delta\| < \epsilon$ for small $\epsilon$.

**Observed**: For the Minkowski grid under FFT perturbations with $\epsilon \in [0.05, 0.3]$ and threshold $\in [0.3, 0.5]$, we have:

$$
\dim H_1(P') = \dim H_1(P) = 190 \quad \text{(100% of trials)}
$$

## Next Steps

1. **Test on non-Minkowski posets**: Generalize to random causal graphs, non-uniform grids.
2. **Parameter sweep**: Scan (ε, threshold, window) to find critical boundaries.
3. **Lean formalization**: Emit invariance certificates from stable parameter regimes.
4. **MATLAB PDE analogs**: Translate to continuous metric flow simulations.

## References

- Lean implementation: `lean/src/AqeiBridge/PosetHomologyProxy.lean`
- Python tooling: `python/poset_homology_proxy.py`
- TODO plan: `docs/TODO.md`
