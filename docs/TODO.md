# TODO: Active Queue for AQEIBridge Workflow

Keep this file to ~5–8 concrete, CI-friendly tasks. Move overscoped items into `docs/TODO-BLOCKED.md`.

## Active batch (2026-02-11): CTC proxy integration (diagnostics)
- [ ] Add a tiny wrapper script `python/ctc_scan.py` that:
  - runs cycle detection on a graph JSON (edges or futures-map)
  - optionally generates a Minkowski 1+1 poset graph and checks it is acyclic
- [ ] Extend `tests/python_tests.sh` to assert the generated Minkowski poset is acyclic under the cycle detector.
- [ ] Update `docs/phase4_searches.md` with a short “CTC proxy workflow” example chaining poset generation → cycle check.
- [ ] Add a short note to `docs/manuscript.md` pointing to the diagnostic tooling (no new claims).
- [ ] Run `./run_tests.sh`, then drain this TODO batch and commit.

