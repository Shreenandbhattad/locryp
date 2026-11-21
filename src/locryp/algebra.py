from math import gcd

from .numtheory import factor


class NotInvertible(ArithmeticError):
    pass


class IntegersMod:
    degree = 1

    def __init__(self, n):
        if n < 2:
            raise ValueError("modulus must be at least two")
        self.n = n
        self.characteristic = n
        self.order = n

    def __eq__(self, other):
        return isinstance(other, IntegersMod) and other.n == self.n

    def __hash__(self):
        return hash(("IntegersMod", self.n))

    def zero(self):
        return 0

    def one(self):
        return 1

    def element(self, value):
        if not isinstance(value, int):
            raise TypeError("prime field element must be an integer")
        return value % self.n

    def from_int(self, value):
        return value % self.n

    def add(self, x, y):
        return (x + y) % self.n

    def sub(self, x, y):
        return (x - y) % self.n

    def neg(self, x):
        return -x % self.n

    def mul(self, x, y):
        return x * y % self.n

    def inv(self, x):
        if gcd(x, self.n) != 1:
            raise NotInvertible(x)
        return pow(x, -1, self.n)

    def is_zero(self, x):
        return x == 0

    def pow(self, x, e):
        return pow(x, e, self.n)

    def encode(self, x):
        return str(x)


class ExtensionField:
    def __init__(self, base, modulus):
        modulus = poly_trim(base, list(modulus))
        if len(modulus) < 2:
            raise ValueError("extension modulus must have positive degree")
        lead_inverse = base.inv(modulus[-1])
        self.base = base
        self.modulus = [base.mul(c, lead_inverse) for c in modulus]
        self.degree = len(self.modulus) - 1
        self.characteristic = base.characteristic
        self.order = base.order**self.degree

    def __eq__(self, other):
        return (
            isinstance(other, ExtensionField)
            and other.base == self.base
            and other.modulus == self.modulus
        )

    def __hash__(self):
        return hash(("ExtensionField", self.base, tuple(self.modulus)))

    def zero(self):
        return (self.base.zero(),) * self.degree

    def one(self):
        return (self.base.one(),) + (self.base.zero(),) * (self.degree - 1)

    def element(self, value):
        if not isinstance(value, list) or len(value) > self.degree:
            raise TypeError("extension element must be a list of at most %d coefficients" % self.degree)
        coefficients = [self.base.element(v) for v in value]
        coefficients += [self.base.zero()] * (self.degree - len(coefficients))
        return tuple(coefficients)

    def from_int(self, value):
        return (self.base.from_int(value),) + (self.base.zero(),) * (self.degree - 1)

    def add(self, x, y):
        return tuple(self.base.add(a, b) for a, b in zip(x, y))

    def sub(self, x, y):
        return tuple(self.base.sub(a, b) for a, b in zip(x, y))

    def neg(self, x):
        return tuple(self.base.neg(a) for a in x)

    def _pad(self, coefficients):
        return tuple(coefficients) + (self.base.zero(),) * (self.degree - len(coefficients))

    def mul(self, x, y):
        base = self.base
        d = self.degree
        product = [base.zero()] * (2 * d - 1)
        for i, a in enumerate(x):
            if base.is_zero(a):
                continue
            for j, b in enumerate(y):
                if not base.is_zero(b):
                    product[i + j] = base.add(product[i + j], base.mul(a, b))
        modulus = self.modulus
        for k in range(2 * d - 2, d - 1, -1):
            c = product[k]
            if base.is_zero(c):
                continue
            for i in range(d):
                product[k - d + i] = base.sub(product[k - d + i], base.mul(c, modulus[i]))
        return tuple(product[:d])

    def inv(self, x):
        g, s, _ = poly_xgcd(self.base, poly_trim(self.base, list(x)), self.modulus)
        if len(g) != 1:
            raise NotInvertible(x)
        scale = self.base.inv(g[0])
        return self._pad([self.base.mul(c, scale) for c in s])

    def is_zero(self, x):
        return all(self.base.is_zero(a) for a in x)

    def pow(self, x, e):
        result = self.one()
        while e:
            if e & 1:
                result = self.mul(result, x)
            x = self.mul(x, x)
            e >>= 1
        return result

    def encode(self, x):
        return [self.base.encode(a) for a in x]


def poly_trim(ring, f):
    while f and ring.is_zero(f[-1]):
        f.pop()
    return f


def poly_add(ring, f, g):
    if len(f) < len(g):
        f, g = g, f
    result = list(f)
    for i, c in enumerate(g):
        result[i] = ring.add(result[i], c)
    return poly_trim(ring, result)


def poly_sub(ring, f, g):
    return poly_add(ring, f, [ring.neg(c) for c in g])


def poly_mul(ring, f, g):
    if not f or not g:
        return []
    result = [ring.zero()] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if ring.is_zero(a):
            continue
        for j, b in enumerate(g):
            result[i + j] = ring.add(result[i + j], ring.mul(a, b))
    return poly_trim(ring, result)


def poly_divmod(ring, f, g):
    if not g:
        raise ZeroDivisionError("polynomial division by zero")
    remainder = list(f)
    lead_inverse = ring.inv(g[-1])
    quotient = [ring.zero()] * max(len(f) - len(g) + 1, 0)
    for shift in range(len(f) - len(g), -1, -1):
        coefficient = ring.mul(remainder[shift + len(g) - 1], lead_inverse)
        quotient[shift] = coefficient
        if ring.is_zero(coefficient):
            continue
        for i, c in enumerate(g):
            remainder[shift + i] = ring.sub(remainder[shift + i], ring.mul(coefficient, c))
    return poly_trim(ring, quotient), poly_trim(ring, remainder[: len(g) - 1])


def poly_monic(ring, f):
    if not f:
        return f
    scale = ring.inv(f[-1])
    return [ring.mul(c, scale) for c in f]


def poly_gcd(ring, f, g):
    while g:
        f, g = g, poly_divmod(ring, f, g)[1]
    return poly_monic(ring, f)


def poly_xgcd(ring, f, g):
    r0, r1 = f, g
    s0, s1 = [ring.one()], []
    t0, t1 = [], [ring.one()]
    while r1:
        q, r = poly_divmod(ring, r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, poly_sub(ring, s0, poly_mul(ring, q, s1))
        t0, t1 = t1, poly_sub(ring, t0, poly_mul(ring, q, t1))
    return r0, s0, t0


def poly_mulmod(ring, f, g, modulus):
    return poly_divmod(ring, poly_mul(ring, f, g), modulus)[1]


def poly_powmod(ring, f, e, modulus):
    result = poly_divmod(ring, [ring.one()], modulus)[1]
    f = poly_divmod(ring, f, modulus)[1]
    while e:
        if e & 1:
            result = poly_mulmod(ring, result, f, modulus)
        f = poly_mulmod(ring, f, f, modulus)
        e >>= 1
    return result


def frobenius_powers(ring, modulus, count):
    x = [ring.zero(), ring.one()]
    powers = []
    current = x
    for _ in range(count):
        current = poly_powmod(ring, current, ring.order, modulus)
        powers.append(current)
    return powers


def rabin_irreducibility(ring, modulus):
    f = poly_monic(ring, poly_trim(ring, list(modulus)))
    d = len(f) - 1
    if d < 1:
        raise ValueError("polynomial must have positive degree")
    if d == 1:
        return {"irreducible": True, "degree": 1}
    x = [ring.zero(), ring.one()]
    powers = frobenius_powers(ring, f, d)
    top = poly_sub(ring, powers[d - 1], x)
    if top:
        return {"irreducible": False, "degree": d, "failed": "x^(q^%d) - x is not divisible by f" % d}
    for r in sorted(factor(d).primes):
        h = poly_sub(ring, powers[d // r - 1], x)
        g = poly_gcd(ring, f, h)
        if len(g) > 1:
            return {
                "irreducible": False,
                "degree": d,
                "failed": "gcd(f, x^(q^%d) - x) has degree %d" % (d // r, len(g) - 1),
                "factor": [ring.encode(c) for c in g],
            }
    return {"irreducible": True, "degree": d}
