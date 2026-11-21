import copy
import random
import unittest

from locryp.certificates import (
    DETERMINISTIC_BOUND,
    CertificateError,
    Prover,
    deterministic_miller_rabin,
    ecpp_bound_holds,
    verify_certificate,
)
from locryp.numtheory import is_probable_prime

STANDARD_PRIMES = {
    "secp256k1 p": 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F,
    "secp256k1 n": 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141,
    "P-256 p": 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF,
    "P-256 n": 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551,
    "Curve25519 p": 2**255 - 19,
    "Curve25519 l": 2**252 + 27742317777372353535851937790883648493,
    "BLS12-381 r": 0x73EDA753299D7D483339D80809A1D80553BDA402FFFE5BFEFFFFFFFF00000001,
}


def methods(certificate, found=None):
    found = set() if found is None else found
    found.add(certificate["method"])
    for entry in certificate.get("factors", []):
        methods(entry["certificate"], found)
    if "certificate" in certificate:
        methods(certificate["certificate"], found)
    return found


def random_prime(rng, bits):
    while True:
        n = rng.getrandbits(bits) | (1 << (bits - 1)) | 1
        if is_probable_prime(n):
            return n


class ProverTests(unittest.TestCase):
    def test_standard_curve_primes_are_certified(self):
        for label, n in STANDARD_PRIMES.items():
            with self.subTest(label):
                certificate = Prover().certify(n)
                self.assertIsNotNone(certificate)
                self.assertTrue(verify_certificate(certificate, n))

    def test_curve25519_order_needs_elliptic_curve_step(self):
        certificate = Prover().certify(STANDARD_PRIMES["Curve25519 l"])
        self.assertIn("goldwasser-kilian", methods(certificate))

    def test_random_primes_are_certified(self):
        rng = random.Random(3)
        for bits in (64, 100, 160, 224):
            for _ in range(3):
                n = random_prime(rng, bits)
                certificate = Prover().certify(n)
                self.assertIsNotNone(certificate, n)
                self.assertTrue(verify_certificate(certificate, n))

    def test_composites_are_never_certified(self):
        rng = random.Random(4)
        composites = [561, 3825123056546413051, 318665857834031151167461]
        composites += [random_prime(rng, 90) * random_prime(rng, 90) for _ in range(3)]
        for n in composites:
            self.assertIsNone(Prover().certify(n))

    def test_deterministic_range(self):
        self.assertTrue(deterministic_miller_rabin(DETERMINISTIC_BOUND - 2) == is_probable_prime(DETERMINISTIC_BOUND - 2))
        self.assertFalse(deterministic_miller_rabin(3825123056546413051))
        self.assertTrue(deterministic_miller_rabin(2**61 - 1))


class VerifierTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.n = STANDARD_PRIMES["Curve25519 l"]
        cls.certificate = Prover().certify(cls.n)

    def test_wrong_expected_value_is_rejected(self):
        with self.assertRaises(CertificateError):
            verify_certificate(self.certificate, self.n + 2)

    def test_every_numeric_change_to_a_proven_quantity_is_rejected(self):
        proven_fields = {"n", "q", "m", "e", "x", "y"}
        paths = []

        def walk(node, path):
            if isinstance(node, dict):
                for key, value in node.items():
                    if key in proven_fields and isinstance(value, str):
                        paths.append(path + [key])
                    else:
                        walk(value, path + [key])
            elif isinstance(node, list):
                for i, value in enumerate(node):
                    walk(value, path + [i])

        walk(self.certificate, [])
        self.assertGreater(len(paths), 10)
        for path in paths:
            forged = copy.deepcopy(self.certificate)
            node = forged
            for key in path[:-1]:
                node = node[key]
            node[path[-1]] = str(int(node[path[-1]]) + 2)
            with self.assertRaises(CertificateError, msg=str(path)):
                verify_certificate(forged, self.n)

    def test_composite_disguised_as_small_prime_is_rejected(self):
        with self.assertRaises(CertificateError):
            verify_certificate({"n": "3825123056546413051", "method": "deterministic-miller-rabin"})

    def test_small_method_above_bound_is_rejected(self):
        n = 2**127 - 1
        with self.assertRaises(CertificateError):
            verify_certificate({"n": str(n), "method": "deterministic-miller-rabin"})

    def test_pocklington_with_insufficient_factored_part_is_rejected(self):
        n = 2**127 - 1
        forged = {
            "n": str(n),
            "method": "pocklington",
            "factors": [{"q": "2", "e": "1", "base": "3", "certificate": {"n": "2", "method": "deterministic-miller-rabin"}}],
        }
        with self.assertRaises(CertificateError):
            verify_certificate(forged)

    def test_pocklington_for_composite_with_fake_factor_is_rejected(self):
        n = 1000000016000000063
        forged = {
            "n": str(n),
            "method": "pocklington",
            "factors": [
                {"q": str(n - 1), "e": "1", "base": "2", "certificate": {"n": str(n - 1), "method": "deterministic-miller-rabin"}}
            ],
        }
        with self.assertRaises(CertificateError):
            verify_certificate(forged)

    def test_goldwasser_kilian_requires_q_dividing_m(self):
        step = copy.deepcopy(self._first_elliptic_step())
        step["m"] = str(int(step["m"]) + 1)
        with self.assertRaises(CertificateError):
            verify_certificate(step)

    def test_unknown_method_and_malformed_fields_are_rejected(self):
        for forged in (
            {"n": "7", "method": "trust-me"},
            {"n": 7, "method": "deterministic-miller-rabin"},
            {"n": "-7", "method": "deterministic-miller-rabin"},
            "not an object",
        ):
            with self.assertRaises(CertificateError):
                verify_certificate(forged)

    def test_ecpp_bound_is_conservative(self):
        rng = random.Random(8)
        for _ in range(2000):
            n = rng.randrange(10**4, 10**12)
            q = rng.randrange(1, 4 * int(n**0.5) + 100)
            if ecpp_bound_holds(q, n):
                self.assertGreater(q, (n**0.25 + 1) ** 2)
        self.assertFalse(ecpp_bound_holds(4, 1))

    def _first_elliptic_step(self):
        stack = [self.certificate]
        while stack:
            node = stack.pop()
            if node["method"] == "goldwasser-kilian":
                return node
            stack.extend(entry["certificate"] for entry in node.get("factors", []))
            if "certificate" in node:
                stack.append(node["certificate"])
        self.fail("no elliptic curve step")


if __name__ == "__main__":
    unittest.main()
