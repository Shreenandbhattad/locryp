import itertools
import random
import unittest

from locryp.algebra import ExtensionField, IntegersMod, NotInvertible, rabin_irreducibility
from locryp.cm import hilbert_class_polynomial, reduced_forms, roots_mod
from locryp.ec import INFINITY, WeierstrassCurve


def mobius(n):
    result, d = 1, 2
    while d * d <= n:
        if n % d == 0:
            n //= d
            if n % d == 0:
                return 0
            result = -result
        d += 1
    return -result if n > 1 else result


def irreducible_count(q, d):
    return sum(mobius(d // k) * q**k for k in range(1, d + 1) if d % k == 0) // d


class ExtensionFieldTests(unittest.TestCase):
    def setUp(self):
        self.fp = IntegersMod(10007)
        self.fp2 = ExtensionField(self.fp, [1, 0, 1])
        self.fp6 = ExtensionField(self.fp2, [(10007 - 9, 10007 - 1), (0, 0), (0, 0), (1, 0)])
        self.rng = random.Random(5)

    def random_element(self, field):
        if isinstance(field, IntegersMod):
            return self.rng.randrange(field.n)
        return tuple(self.random_element(field.base) for _ in range(field.degree))

    def test_field_axioms_hold_on_random_elements(self):
        for field in (self.fp2, self.fp6):
            for _ in range(25):
                x, y, z = (self.random_element(field) for _ in range(3))
                self.assertEqual(field.mul(x, field.add(y, z)), field.add(field.mul(x, y), field.mul(x, z)))
                self.assertEqual(field.mul(field.mul(x, y), z), field.mul(x, field.mul(y, z)))
                self.assertEqual(field.mul(x, y), field.mul(y, x))
                if not field.is_zero(x):
                    self.assertEqual(field.mul(x, field.inv(x)), field.one())

    def test_frobenius_order(self):
        x = self.random_element(self.fp2)
        self.assertEqual(self.fp2.pow(x, self.fp2.order), x)

    def test_reducible_modulus_has_zero_divisors(self):
        ring = ExtensionField(IntegersMod(7), [6, 0, 1])
        with self.assertRaises(NotInvertible):
            ring.inv((1, 1))

    def test_rabin_counts_match_gauss_formula(self):
        for p, d in ((2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (5, 2), (2, 6)):
            field = IntegersMod(p)
            count = 0
            for coefficients in itertools.product(range(p), repeat=d):
                if rabin_irreducibility(field, list(coefficients) + [1])["irreducible"]:
                    count += 1
            self.assertEqual(count, irreducible_count(p, d), (p, d))

    def test_rabin_over_extension_base(self):
        f8 = ExtensionField(IntegersMod(2), [1, 1, 0, 1])
        count = 0
        for a, b in itertools.product([tuple(c) for c in itertools.product(range(2), repeat=3)], repeat=2):
            if rabin_irreducibility(f8, [a, b, f8.one()])["irreducible"]:
                count += 1
        self.assertEqual(count, irreducible_count(8, 2))


class CurveTests(unittest.TestCase):
    def setUp(self):
        self.p = 1009
        self.ring = IntegersMod(self.p)
        self.curve = WeierstrassCurve(self.ring, 2, 3)
        self.points = [INFINITY] + [
            (x, y) for x in range(self.p) for y in range(self.p) if self.curve.contains((x, y))
        ]

    def test_group_law_is_associative_and_closed(self):
        rng = random.Random(6)
        for _ in range(200):
            a, b, c = (rng.choice(self.points) for _ in range(3))
            left = self.curve.add(self.curve.add(a, b), c)
            right = self.curve.add(a, self.curve.add(b, c))
            self.assertEqual(left, right)
            self.assertTrue(self.curve.contains(left))

    def test_every_point_is_killed_by_group_order(self):
        order = len(self.points)
        for point in self.points[:100]:
            self.assertIsNone(self.curve.multiply(point, order))
            self.assertEqual(self.curve.multiply(point, order + 1), point)

    def test_composite_modulus_exposes_non_invertible_denominator(self):
        n = 1009 * 1013
        curve = WeierstrassCurve(IntegersMod(n), 2, 3)
        x = 5
        candidates = [y for y in range(n) if (y * y - curve.rhs(x)) % n == 0][:1]
        if candidates:
            point = (x, candidates[0])
            with self.assertRaises(NotInvertible):
                for k in range(1, 3000):
                    curve.multiply(point, k)


class ComplexMultiplicationTests(unittest.TestCase):
    def test_known_class_numbers(self):
        for d, h in ((-3, 1), (-4, 1), (-23, 3), (-47, 5), (-71, 7), (-163, 1), (-199, 9)):
            self.assertEqual(len(reduced_forms(d)), h)

    def test_known_class_polynomials(self):
        self.assertEqual(hilbert_class_polynomial(-163), [262537412640768000, 1])
        self.assertEqual(hilbert_class_polynomial(-15), [-121287375, 191025, 1])
        self.assertEqual(
            hilbert_class_polynomial(-23), [12771880859375, -5151296875, 3491750, 1]
        )

    def test_roots_mod_returns_roots(self):
        p = 1000003
        polynomial = [(-3) * (-5) * (-7) % p, (3 * 5 + 3 * 7 + 5 * 7) % p, (-15) % p, 1]
        roots = roots_mod(polynomial, p, random.Random(7), limit=3)
        self.assertEqual(sorted(roots), [3, 5, 7])


if __name__ == "__main__":
    unittest.main()
