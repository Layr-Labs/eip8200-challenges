#!/usr/bin/env python3
"""Integration checks for the built runners' JSON vector interface.

Run after `lake build modexpchallenge ripemd160challenge`.
"""

import copy
import csv
import io
import json
import hashlib
from pathlib import Path
import subprocess
import tempfile
import unittest

import yukon_benchmark as benchmark


ROOT = Path(__file__).resolve().parents[1]


class VectorFilesTest(unittest.TestCase):
    def run_case(self, kind, document, *args):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "vectors.json"
            path.write_text(json.dumps(document))
            return subprocess.run(
                [str(ROOT / ".lake/build/bin" / f"{kind}challenge"),
                 f"--vectors={path}", *args],
                cwd=ROOT, capture_output=True, text=True, timeout=60,
            )

    def fixture(self, kind):
        document = json.loads((ROOT / "test-vectors" / f"{kind}.json").read_text())
        document["vectors"] = document["vectors"][:1]
        return document

    def test_valid_files_and_csv_labels(self):
        for kind in ("modexp", "ripemd160"):
            with self.subTest(kind=kind):
                document = self.fixture(kind)
                document["vectors"][0]["label"] = 'a, "quoted" label'
                document["vectors"][0]["input"] = "0x"
                result = self.run_case(kind, document, "--csv")
                self.assertEqual(result.returncode, 0, result.stderr)
                rows = list(csv.DictReader(io.StringIO(result.stdout)))
                self.assertEqual(len(rows), 1 if kind == "modexp" else 2)
                for row in rows:
                    self.assertEqual(row["vector"], 'a, "quoted" label')
                    self.assertEqual(row["status"], "ok")

    def test_reject_invalid_files(self):
        for kind in ("modexp", "ripemd160"):
            fixture = self.fixture(kind)
            mutations = [
                ("wrong tag", lambda d: d.update(precompile="other"), "expected precompile"),
                ("empty suite", lambda d: d.update(vectors=[]), "must not be empty"),
                ("odd hex", lambda d: d["vectors"][0].update(input="0"), "even-length hex"),
                ("invalid hex", lambda d: d["vectors"][0].update(input="zz"), "even-length hex"),
                ("missing expected", lambda d: d["vectors"][0].pop("expected"), "expected"),
                ("wrong expected", lambda d: d["vectors"][0].update(expected="ff"), "disagrees"),
                ("duplicate label", lambda d: d["vectors"].append(d["vectors"][0]), "duplicate label"),
            ]
            for name, mutate, message in mutations:
                with self.subTest(kind=kind, case=name):
                    document = copy.deepcopy(fixture)
                    mutate(document)
                    result = self.run_case(kind, document)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn(message, result.stderr)

    def test_reject_oversized_modexp(self):
        document = self.fixture("modexp")
        document["vectors"][0]["input"] = (1025).to_bytes(32, "big").hex()
        result = self.run_case("modexp", document)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("outside supported challenge domain", result.stderr)

    def test_wrong_candidate_fails(self):
        for kind in ("modexp", "ripemd160"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
                code = Path(directory) / "stop.hex"
                code.write_text("00")
                result = self.run_case(kind, self.fixture(kind), f"--hex={code}")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Tier 1: FAIL", result.stdout)

    def test_benchmark_scores_the_selected_suite(self):
        for kind in ("modexp", "ripemd160"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                document = self.fixture(kind)
                result = self.run_case(kind, document, "--csv")
                self.assertEqual(result.returncode, 0, result.stderr)
                vectors = root / "vectors.json"
                vectors.write_text(json.dumps(document))
                artifact = root / "code.hex"
                artifact.write_text("00\n")
                rows = root / "scorer.csv"
                rows.write_text(result.stdout)
                score = root / "score.json"
                summary = root / "summary.md"
                benchmark.write_score(kind, artifact, rows, score, summary, vectors)
                metrics = json.loads(score.read_text())["metrics"]
                self.assertEqual(metrics["vectors"], 1)
                self.assertEqual(metrics["vectorSuiteSha256"],
                                 hashlib.sha256(vectors.read_bytes()).hexdigest())
                # A stale scorer returning another suite must not publish a score.
                document["vectors"][0]["label"] = "a different case"
                vectors.write_text(json.dumps(document))
                with self.assertRaises(ValueError):
                    benchmark.write_score(kind, artifact, rows, score, summary, vectors)


if __name__ == "__main__":
    unittest.main()
