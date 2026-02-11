## Active batch (2026-02-11): Phase 4 ramp-up (docs + sweep tooling)
- [ ] Triage over-scoped Phase 4 items into `docs/TODO-BLOCKED.md` with explicit blockers (CI/runtime/topology dependencies).
- [ ] Add `docs/phase4_searches.md` documenting the “large-scale search” workflow using existing `python/sweep_parameters.py` + `python/sweep_analysis.py` + `python/multi_ray_analysis.py`.
- [ ] Add a small CLI improvement: `python/sweep_parameters.py --analyze` to run `sweep_analysis` automatically after executing a sweep.
- [ ] Update `docs/manuscript.md` with a short “Phase 4: empirical bounds via sweeps” subsection (no new claims).
- [ ] Update `README.md` to link to the Phase 4 searches doc and clarify what is blocked.
- [ ] Run `./run_tests.sh`, then drain this TODO batch and commit.


