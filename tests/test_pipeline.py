"""End-to-end pipeline smoke test.

This test is intentionally minimal: it asserts that the pipeline can run with
small parameters and produce the expected output artifacts.

It does NOT assert that the physics is correct.
"""

from __future__ import annotations

import os
import unittest
from pathlib import Path


class TestPipeline(unittest.TestCase):
    def test_end_to_end_tiny(self) -> None:
        repo_root = Path(__file__).resolve().parents[1]

        # Keep the Mathematica run fast.
        env = os.environ.copy()
        env.update(
            {
                "AQEI_TEST_MODE": "1",
                "AQEI_NUM_BASIS": "2",
                "AQEI_NUM_CONSTRAINTS": "6",
                "AQEI_GRID": "32",
                "AQEI_DOMAIN": "2.0",
                "AQEI_SIGMA": "0.8",
                "AQEI_SEED": "123",
            }
        )

        # Run orchestrator in-process.
        from python.orchestrator import run_pipeline

        run_info = run_pipeline(repo_root=repo_root, env=env)

        results_dir = Path(run_info["resultsDir"])
        self.assertTrue((results_dir / "summary.json").exists())
        self.assertTrue((results_dir / "top_candidates.json").exists())

        gen = repo_root / "lean" / "src" / "AqeiBridge" / "GeneratedCandidates.lean"
        self.assertTrue(gen.exists())


if __name__ == "__main__":
    unittest.main()
