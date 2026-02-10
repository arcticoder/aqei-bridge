# Toy model (1+1): assumptions, limitations, and the Δ proxy

This document describes the current heuristic model implemented in
`mathematica/search.wl`.

## Summary

- Dimension: 1+1 grid in $(t,x)$.
- Ansatz: finite Gaussian wavepacket basis $T(t,x) = \sum_i a_i T_i(t,x)$.
- Solver: FFT-based scalar Green multiplier approximating a linearized operator.
- Observable: integrate the resulting field along “null-ish” rays:

$$
\Delta_{\ell}(a) := \int_{\ell} h[a](t(\lambda),x(\lambda))\, d\lambda
$$

**IMPORTANT:** this is a search proxy only; it is not an established equivalence
with changes to causal futures.

## Basis: Gaussian wavepackets

Each basis element is a localized oscillatory Gaussian:

$$
T_i(t,x) = \exp\left(-\frac{(t-t_i)^2+(x-x_i)^2}{2\sigma^2}\right)\cos(k_i x + \omega_i t + \phi_i)
$$

In Mathematica this is implemented by `gaussianMode`.

## Green multiplier

We apply a scalar Fourier-space multiplier

$$
G(\omega,k) = -\frac{1}{k^2 - \omega^2 + \varepsilon}
$$

with small $\varepsilon>0$ as Tikhonov-type regularization near the lightcone.

This is **heuristic**; the correct tensor structure and gauge conditions are not
represented.

## Rays

We probe along lines $(t=\lambda, x=v\lambda)$ for a small set of velocities
$v\in\{\pm 1, \pm 0.5\}$.

## Constraints (current status)

At present, “AQEI constraints” are represented as synthetic halfspaces
$w_\gamma\cdot a \ge -B_\gamma$.

Replacing these with manuscript-derived functionals is a Phase 3 milestone.

## Python analysis

`python/analyze_candidates.py` reads the JSON outputs and emits a Lean file
containing rationalized versions of candidate vectors. This is intended to
support the workflow:

- heuristic candidate → exact rational certificate → Lean lemma skeleton.
