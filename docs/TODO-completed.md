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
