import json
import tempfile
import unittest
from pathlib import Path

from locryp.cli import main
from locryp.engine import Engine
from locryp.result import Status
from locryp.spec import SpecError, load_specification, parse_specification

EXAMPLES = Path(__file__).resolve().parent.parent / "examples"
P = 175374040658033212745386689539757367483
R = 43843510164508303186346672384939341871
GX = 130597128020004527160661139397028115636
GY = 158655805246611342134752349769561103546


def run(data, effort="normal"):
    return {result.key: result for result in Engine(parse_specification(data), effort).run()}


def curve_spec(**overrides):
    curve = {"field": "Fp", "a": 1, "b": 0, "subgroup_order": R, "cofactor": 4, "generator": {"x": GX, "y": GY}}
    curve.update(overrides)
    return {"locryp": 1, "fields": {"Fp": {"prime": P}}, "curves": {"E": curve}}


class ExampleTests(unittest.TestCase):
    def test_standard_examples_pass_completely(self):
        for name in ("secp256k1", "p256", "wei25519", "bn254"):
            with self.subTest(name):
                results = Engine(load_specification(EXAMPLES / ("%s.toml" % name))).run()
                self.assertTrue(results)
                self.assertTrue(all(r.status == Status.PASS for r in results), [r.key for r in results if r.status != Status.PASS])

    def test_flawed_example_reports_each_planted_flaw(self):
        results = {r.key: r.status for r in Engine(load_specification(EXAMPLES / "flawed.toml")).run()}
        expected_failures = {
            "FIELD-PRIME:Fq",
            "FIELD-IRREDUCIBLE:Fp2",
            "CURVE-EMBEDDING-DEGREE:Supersingular",
            "CURVE-COFACTOR:WrongCardinality",
            "CURVE-CARDINALITY:WrongCardinality",
            "CURVE-POINT:OffCurve",
            "R1CS-WITNESS:Cubic",
        }
        self.assertEqual({k for k, s in results.items() if s == Status.FAIL}, expected_failures)
        self.assertEqual(results["GENERATOR-ORDER:OffCurve"], Status.INDETERMINATE)

    def test_suzuki_group_order(self):
        results = Engine(load_specification(EXAMPLES / "suzuki_sz8.toml")).run()
        self.assertTrue(all(r.status == Status.PASS for r in results))


class EngineTests(unittest.TestCase):
    def test_wrong_generator_order_is_refuted(self):
        results = run(curve_spec(subgroup_order=R * 2, prime_order=False, cofactor=2))
        self.assertEqual(results["GENERATOR-ORDER:E"].status, Status.FAIL)

    def test_cardinality_outside_hasse_interval_fails(self):
        data = curve_spec(cardinality=4 * R * 3, cofactor=12)
        self.assertEqual(run(data)["CURVE-CARDINALITY:E"].status, Status.FAIL)

    def test_small_field_counts_points_exhaustively(self):
        data = {
            "locryp": 1,
            "fields": {"F": {"prime": 1009}},
            "curves": {"E": {"field": "F", "a": 2, "b": 3, "subgroup_order": 2, "prime_order": False, "cardinality": 1000}},
        }
        result = run(data)["CURVE-CARDINALITY:E"]
        self.assertIn(result.status, (Status.PASS, Status.FAIL))
        self.assertEqual(result.method, "exhaustive point count")

    def test_assumption_skips_check_and_conditions_dependents(self):
        data = curve_spec()
        data["assumptions"] = ["SUBGROUP-PRIME:E"]
        results = run(data)
        self.assertEqual(results["SUBGROUP-PRIME:E"].status, Status.ASSUMED)
        self.assertEqual(results["GENERATOR-ORDER:E"].status, Status.PASS)
        self.assertIn("SUBGROUP-PRIME:E", results["GENERATOR-ORDER:E"].conditional_on)
        self.assertIn("SUBGROUP-PRIME:E", results["CURVE-CARDINALITY:E"].conditional_on)

    def test_unknown_assumption_is_rejected(self):
        data = curve_spec()
        data["assumptions"] = ["SUBGROUP-PRIME:Nope"]
        with self.assertRaises(SpecError):
            run(data)

    def test_composite_field_blocks_dependents(self):
        data = curve_spec()
        data["fields"]["Fp"]["prime"] = P * 3
        results = run(data)
        self.assertEqual(results["FIELD-PRIME:Fp"].status, Status.FAIL)
        self.assertEqual(results["CURVE-NONSINGULAR:E"].status, Status.INDETERMINATE)

    def test_embedding_degree_claim_that_is_too_large_fails(self):
        self.assertEqual(run(curve_spec(embedding_degree=4))["CURVE-EMBEDDING-DEGREE:E"].status, Status.FAIL)


class SpecificationTests(unittest.TestCase):
    def assertRejected(self, data, fragment):
        with self.assertRaises(SpecError) as context:
            parse_specification(data)
        self.assertIn(fragment, str(context.exception))

    def test_rejections(self):
        base = {"locryp": 1, "fields": {"Fp": {"prime": 101}}}
        self.assertRejected({"locryp": 2}, "version")
        self.assertRejected(dict(base, extra=1), "unknown keys")
        self.assertRejected({"locryp": 1, "fields": {"Fp": {"prime": True}}}, "boolean")
        self.assertRejected({"locryp": 1, "fields": {"Fp": {"prime": "12x"}}}, "integer")
        self.assertRejected({"locryp": 1, "fields": {"F": {"prime": 3}}, "curves": {"E": {"field": "F", "a": 1, "b": 1}}}, "characteristic")
        self.assertRejected(dict(base, curves={"E": {"field": "Fq", "a": 1, "b": 1}}), "unknown field")
        self.assertRejected(dict(base, curves={"E": {"field": "Fp", "a": 1, "b": 1, "generator": {"x": 1, "y": 1}}}), "subgroup_order")
        self.assertRejected(dict(base, fields={"Fp": {"prime": 101}, "F2": {"base": "Fp", "modulus": [1, 0, 0]}}), "leading")
        group = {"field": "Fp", "size": 1, "generators": {"a": [[2]]}, "relators": ["a^"]}
        self.assertRejected(dict(base, matrix_groups={"G": group}), "malformed")
        group = {"field": "Fp", "size": 1, "generators": {"a": [[2]]}, "relators": ["b"]}
        self.assertRejected(dict(base, matrix_groups={"G": group}), "unknown generator")
        system = {"field": "Fp", "variables": 2, "constraints": [{"a": {"5": 1}}]}
        self.assertRejected(dict(base, constraint_systems={"C": system}), "out of range")


class CommandLineTests(unittest.TestCase):
    def test_exit_codes_report_and_verification(self):
        with tempfile.TemporaryDirectory() as directory:
            report = Path(directory) / "report.json"
            self.assertEqual(main(["check", str(EXAMPLES / "wei25519.toml"), "--quiet", "--report", str(report)]), 0)
            self.assertEqual(main(["verify", str(report)]), 0)
            data = json.loads(report.read_text())
            for result in data["results"]:
                if "certificate" in result["evidence"]:
                    result["evidence"]["n"] = str(int(result["evidence"]["n"]) + 2)
            report.write_text(json.dumps(data))
            self.assertEqual(main(["verify", str(report)]), 1)
            self.assertEqual(main(["check", str(EXAMPLES / "flawed.toml"), "--quiet"]), 1)
            missing = Path(directory) / "missing.toml"
            self.assertEqual(main(["check", str(missing), "--quiet"]), 2)

    def test_prove_command(self):
        self.assertEqual(main(["prove", "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed"]), 0)
        self.assertEqual(main(["prove", "3825123056546413051"]), 1)


if __name__ == "__main__":
    unittest.main()
