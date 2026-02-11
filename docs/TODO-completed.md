# TODO — completed

(Entries moved here from docs/TODO.md as they are completed.)

## 2026-02-09
- Created `docs/` directory and moved the active TODO tracking here.
- Added `docs/architecture.md` (4-stage pipeline + mermaid diagram).
- Added `docs/conjecture.md` (precise bridge conjecture statement; formal vs heuristic separation).
- Added `docs/toy-model.md` (1+1 toy model assumptions + Δ proxy explanation).
- Expanded README with debugging / common failure modes.
- Added repo-level `run_tests.sh` to run python/mathematica/lean smoke tests.
- Added `docs/TODO-completed.md` and `docs/TODO-BLOCKED.md`.

## 2026-02-09 (later)
- Added timestamped run persistence in `runs/<UTC timestamp>/run.json` via `python/orchestrator.py`.
- Added `tests/test_pipeline.py` (unittest end-to-end smoke test) and wired it into `tests/python_tests.sh`.

## 2026-02-10
- Migrated long-term checklist items into `docs/TODO-backlog.md` so `docs/TODO.md` can remain empty as the active-queue file.

## 2026-02-10 (later)
- Added `--test-mode` flag support in `mathematica/search.wl` and expanded `run_tests.sh` to run explicit smoke checks (`lake build`, Mathematica test-mode, unittest discovery).
- Started `docs/manuscript.md` with a structured outline aligned to `energy-tensor-cone/papers/` style.
- Tightened Phase 2 Lean skeletons:
	- `Spacetime.lean`: added abstract `CausalCurve`/`Jplus` interface and a neighborhood hook.
	- `StressEnergy.lean`: made `StressEnergyTensor` a symmetric matrix; added `LinearizedEinstein` placeholder.
	- `AQEI_Cone.lean`: added a sampling-based `mkFunctionals` helper.
	- `CausalStability.lean`: added an `IsPathConnected` skeleton statement for the admissible region.

## 2026-02-11
- Added MIT `LICENSE` and mentioned it in the README.
- Added `lean/src/AqeiBridge/CausalPoset.lean` with a causal preorder interface and an Alexandrov-style topology (opens are upper sets).
- Proved basic lemmas in `CausalPoset.lean`, including that order-futures (`Jplus`) are open and a monotonicity/antitone property.
- Wired `AqeiBridge.CausalPoset` into `lean/src/AqeiBridge.lean`.
- Updated `docs/manuscript.md` with a short causal-poset/Alexandrov-topology bridge section.
- Updated `docs/TODO-BLOCKED.md` to reflect that the topology substrate exists; remaining cohomology/sheaf step is blocked on choosing a target invariant.
- Made `python/orchestrator.py` pass `--test-mode` to Mathematica when `AQEI_TEST_MODE=1` (used by the end-to-end unit test).
