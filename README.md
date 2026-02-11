# aqei-bridge

A *bridge* repo: human conjecture → Lean language (toy formalization) → Mathematica heuristic “destruction” search → Lean lemma skeleton emission, orchestrated by Python.

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
├── lean/                      # Lean 4 project (Mathlib)
│   ├── lean-toolchain
│   ├── lakefile.lean
│   └── src/
│       ├── Spacetime.lean
│       ├── StressEnergy.lean
│       ├── AQEI_Cone.lean
│       ├── CausalStability.lean
│       ├── GeneratedCandidates.lean
│       └── Tactics/
├── mathematica/
│   ├── search.nb
│   └── search.wl
├── python/
│   ├── orchestrator.py
│   └── analyze_candidates.py
└── tests/
    ├── build_lean.sh
    ├── lean_tests.sh
    ├── mathematica_tests.sh
    └── python_tests.sh
```

## Quick start

### Prereqs

- Wolfram engine / WolframScript on PATH (`wolframscript` preferred).
- Lean 4 + Lake (via `elan`), already present on your machine.

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
