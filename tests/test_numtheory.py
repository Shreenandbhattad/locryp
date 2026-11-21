import random
import unittest

from locryp.numtheory import (
    compositeness_witness,
    factor,
    is_probable_prime,
    jacobi,
    lucas_sequence,
    small_primes,
    sqrt_mod,
    strong_lucas_probable_prime,
)


def trial_prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n**0.5) + 1))


class PrimalityTests(unittest.TestCase):
    def test_sieve_agrees_with_trial_division(self):
        self.assertEqual(small_primes(5000), [n for n in range(5001) if trial_prime(n)])

    def test_probable_prime_is_exact_below_one_hundred_thousand(self):
        expected = set(small_primes(100000))
        self.assertEqual({n for n in range(100001) if is_probable_prime(n)}, expected)

    def test_rejects_known_pseudoprimes(self):
        for n in (561, 1105, 1729, 2047, 3215031751, 3825123056546413051, 318665857834031151167461):
            self.assertFalse(is_probable_prime(n), n)

    def test_strong_lucas_rejects_perfect_squares(self):
        for root in (101, 7919, 104729):
            self.assertFalse(strong_lucas_probable_prime(root * root))

    def test_compositeness_witness_finds_strong_pseudoprime(self):
        witness = compositeness_witness(3825123056546413051)
        self.assertIsNotNone(witness)

    def test_no_witness_for_primes(self):
        for p in (2, 3, 97, 2**61 - 1, 2**127 - 1):
            self.assertIsNone(compositeness_witness(p))


class ArithmeticTests(unittest.TestCase):
    def test_jacobi_matches_euler_criterion(self):
        for p in small_primes(400)[1:]:
            for a in range(p):
                euler = pow(a, (p - 1) // 2, p)
                self.assertEqual(jacobi(a, p) % p, euler)

    def test_jacobi_rejects_even_modulus(self):
        with self.assertRaises(ValueError):
            jacobi(3, 10)

    def test_sqrt_mod(self):
        rng = random.Random(1)
        for p in (3, 5, 13, 17, 97, 65537, 2**127 - 1, 2**255 - 19):
            for _ in range(20):
                a = rng.randrange(p)
                root = sqrt_mod(a, p)
                if jacobi(a, p) == -1:
                    self.assertIsNone(root)
                else:
                    self.assertEqual(root * root % p, a)

    def test_lucas_sequence_matches_recurrence(self):
        n = 1000003
        for p_param, q_param in ((1, -1), (3, 2), (5, -3), (2, 7)):
            u = [0, 1]
            v = [2, p_param]
            for _ in range(60):
                u.append(p_param * u[-1] - q_param * u[-2])
                v.append(p_param * v[-1] - q_param * v[-2])
            for k in range(60):
                self.assertEqual(lucas_sequence(p_param, q_param, k, n), (u[k] % n, v[k] % n))

    def test_factor_reconstructs_input(self):
        rng = random.Random(2)
        for _ in range(30):
            n = rng.randrange(2, 2**80)
            result = factor(n)
            product = result.factored_part
            for m in result.unfactored:
                product *= m
            self.assertEqual(product, n)
            for p in result.primes:
                self.assertTrue(is_probable_prime(p))

    def test_factor_of_one(self):
        self.assertTrue(factor(1).complete)
        self.assertEqual(factor(1).primes, {})


if __name__ == "__main__":
    unittest.main()
