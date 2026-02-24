# Toy model — historical note

> **Status (2026-02-23):** This document describes the **deprecated** heuristic
> Mathematica+Python search pipeline that was previously part of this repository.
> That pipeline has been moved to
> [`aqei-numerical-validation`](https://github.com/arcticoder/aqei-numerical-validation).
> The scripts (`python/analyze_candidates.py`, `python/orchestrator.py`) have been
> deprecated and archived in `deprecated/python/`.
>
> The current repository is a **pure Lean 4 formal methods project**.
> See `docs/architecture.md` and `docs/code-overview.md` for the current design.

---

## (Archived) What the heuristic search proxy did

The original pipeline used a 1+1 grid toy model:

- **Ansatz:** finite Gaussian wavepacket basis
  $T(t,x) = \sum_i a_i T_i(t,x)$.
- **Solver:** FFT-based scalar Green multiplier (heuristic; not a genuine
  linearized Einstein operator).
- **Observable proxy:** ray integrals
  $\Delta_{\ell}(a) := \int_{\ell} h[a](t(\lambda),x(\lambda))\, d\lambda$
  along a small set of null-ish rays.
- **Output:** `mathematica/results/top_candidates.json`, consumed by
  `python/analyze_candidates.py` to emit Lean data files.

This approach was a useful scaffold for understanding the problem but was
never claimed to produce formal proofs. The formal statements and proofs
now live entirely in `lean/src/AqeiBridge/`.
