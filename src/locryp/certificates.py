import random
from math import gcd, isqrt

from .algebra import IntegersMod, NotInvertible
from .cm import discriminants, hilbert_class_polynomial, roots_mod
from .ec import INFINITY, WeierstrassCurve
from .numtheory import (
    SMALL_PRIMES,
    factor,
    is_probable_prime,
    is_square,
    jacobi,
    lucas_sequence,
    pollard_brent,
    sqrt_mod,
    strong_probable_prime,
)

DETERMINISTIC_BOUND = 3317044064679887385961981
DETERMINISTIC_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
MAX_DEPTH = 512
DISCRIMINANTS = discriminants()


class CertificateError(ValueError):
    pass


def deterministic_miller_rabin(n):
    if n < 2:
        return False
    for p in DETERMINISTIC_BASES:
        if n % p == 0:
            return n == p
    return all(strong_probable_prime(n, a) for a in DETERMINISTIC_BASES)


def _int(value, name):
    if not isinstance(value, str) or not value.isdigit():
        raise CertificateError("field %s must be a decimal string" % name)
    return int(value)


def _require(condition, message):
    if not condition:
        raise CertificateError(message)


def ecpp_bound_holds(q, n):
    s = isqrt(q)
    return s >= 2 and (s - 1) ** 4 > n


def verify_certificate(certificate, expected=None, depth=0):
    _require(isinstance(certificate, dict), "certificate must be an object")
    _require(depth <= MAX_DEPTH, "certificate nesting exceeds %d" % MAX_DEPTH)
    n = _int(certificate.get("n"), "n")
    if expected is not None:
        _require(n == expected, "certificate proves %d, expected %d" % (n, expected))
    method = certificate.get("method")
    if method == "deterministic-miller-rabin":
        _require(n < DETERMINISTIC_BOUND, "n exceeds the deterministic Miller-Rabin bound")
        _require(deterministic_miller_rabin(n), "n fails deterministic Miller-Rabin")
    elif method == "pocklington":
        _verify_pocklington(n, certificate, depth)
    elif method == "morrison":
        _verify_morrison(n, certificate, depth)
    elif method == "goldwasser-kilian":
        _verify_goldwasser_kilian(n, certificate, depth)
    else:
        raise CertificateError("unknown certificate method %r" % method)
    return True


def _factor_entries(n, certificate, depth):
    entries = certificate.get("factors")
    _require(isinstance(entries, list) and entries, "factors must be a nonempty list")
    total = 1
    seen = set()
    parsed = []
    for entry in entries:
        _require(isinstance(entry, dict), "factor entry must be an object")
        q = _int(entry.get("q"), "q")
        e = _int(entry.get("e"), "e")
        _require(q not in seen, "factor %d is repeated" % q)
        _require(e >= 1, "factor exponent must be positive")
        _require(1 < q < n, "factor %d is out of range" % q)
        seen.add(q)
        verify_certificate(entry.get("certificate"), q, depth + 1)
        total *= q**e
        parsed.append((q, e, entry))
    return total, parsed


def _verify_pocklington(n, certificate, depth):
    _require(n > 2 and n % 2 == 1, "n must be an odd integer greater than two")
    f, parsed = _factor_entries(n, certificate, depth)
    _require((n - 1) % f == 0, "factored part does not divide n - 1")
    for q, _, entry in parsed:
        a = _int(entry.get("base"), "base")
        _require(1 < a < n, "base out of range")
        _require(pow(a, n - 1, n) == 1, "base %d fails the Fermat condition" % a)
        _require(gcd(pow(a, (n - 1) // q, n) - 1, n) == 1, "base %d fails the gcd condition for %d" % (a, q))
    if (f + 1) ** 2 > n:
        return
    _require(f**3 >= n, "factored part is below the cube root of n")
    c2, c1 = divmod((n - 1) // f, f)
    _require(not is_square(c1 * c1 - 4 * c2), "Brillhart-Lehmer-Selfridge discriminant is a square")


def _verify_morrison(n, certificate, depth):
    _require(n > 2 and n % 2 == 1, "n must be an odd integer greater than two")
    f, parsed = _factor_entries(n, certificate, depth)
    _require((n + 1) % f == 0, "factored part does not divide n + 1")
    _require(f > 1 and (f - 1) ** 2 > n, "factored part does not exceed sqrt(n) + 1")
    for q, _, entry in parsed:
        p_param = _signed(entry.get("p"), "p")
        q_param = _signed(entry.get("qparam"), "qparam")
        d_param = p_param * p_param - 4 * q_param
        _require(d_param != 0, "discriminant must be nonzero")
        _require(gcd(n, 2 * q_param * d_param) == 1, "n is not coprime to 2QD")
        u_full, _ = lucas_sequence(p_param, q_param, n + 1, n)
        _require(u_full == 0, "U_(n+1) is not divisible by n")
        u_part, _ = lucas_sequence(p_param, q_param, (n + 1) // q, n)
        _require(gcd(u_part, n) == 1, "gcd condition fails for %d" % q)


def _signed(value, name):
    _require(isinstance(value, str), "field %s must be a string" % name)
    body = value[1:] if value.startswith("-") else value
    _require(body.isdigit(), "field %s must be an integer string" % name)
    return int(value)


def _verify_goldwasser_kilian(n, certificate, depth):
    _require(gcd(n, 6) == 1, "n must be coprime to 6")
    a = _int(certificate.get("a"), "a") % n
    b = _int(certificate.get("b"), "b") % n
    x = _int(certificate.get("x"), "x") % n
    y = _int(certificate.get("y"), "y") % n
    m = _int(certificate.get("m"), "m")
    q = _int(certificate.get("q"), "q")
    _require(1 < q < n, "q is out of range")
    _require(m % q == 0, "q does not divide m")
    _require(ecpp_bound_holds(q, n), "q does not exceed (n^(1/4) + 1)^2")
    ring = IntegersMod(n)
    curve = WeierstrassCurve(ring, a, b)
    _require(gcd(curve.discriminant_factor(), n) == 1, "curve is singular modulo a divisor of n")
    point = (x, y)
    _require(curve.contains(point), "point is not on the curve")
    try:
        _require(curve.multiply(point, m) is INFINITY, "[m]P is not the point at infinity")
        _require(curve.multiply(point, m // q) is not INFINITY, "[m/q]P is the point at infinity")
    except NotInvertible:
        raise CertificateError("a non-invertible denominator occurred modulo n")
    verify_certificate(certificate.get("certificate"), q, depth + 1)


class Prover:
    def __init__(self, rho_iterations=100000, node_budget=4000):
        self.rho_iterations = rho_iterations
        self.node_budget = node_budget
        self.nodes = 0
        self.memo = {}
        self.factorizations = {}

    def factorization(self, n):
        if n not in self.factorizations:
            self.factorizations[n] = factor(n, self.rho_iterations)
        return self.factorizations[n]

    def certify(self, n):
        if n in self.memo:
            return self.memo[n]
        self.memo[n] = None
        result = self._certify(n)
        self.memo[n] = result
        return result

    def _certify(self, n):
        if n < 2:
            return None
        if n < DETERMINISTIC_BOUND:
            if deterministic_miller_rabin(n):
                return {"n": str(n), "method": "deterministic-miller-rabin"}
            return None
        if not is_probable_prime(n):
            return None
        self.nodes += 1
        if self.nodes > self.node_budget:
            return None
        for method in (self._pocklington, self._morrison, self._goldwasser_kilian):
            certificate = method(n)
            if certificate is not None:
                return certificate
        return None

    def _proven_part(self, n, m, enough):
        f = 1
        proven = []
        for q, e in sorted(self.factorization(m).primes.items()):
            if enough(f):
                break
            certificate = self.certify(q)
            if certificate is None:
                continue
            f *= q**e
            proven.append((q, e, certificate))
        return f, proven

    def _pocklington(self, n):
        def enough(f):
            if (f + 1) ** 2 > n:
                return True
            if f**3 < n:
                return False
            c2, c1 = divmod((n - 1) // f, f)
            return not is_square(c1 * c1 - 4 * c2)

        f, proven = self._proven_part(n, n - 1, enough)
        if not enough(f):
            return None
        factors = []
        for q, e, certificate in proven:
            base = next(
                (a for a in range(2, 2000) if pow(a, n - 1, n) == 1 and gcd(pow(a, (n - 1) // q, n) - 1, n) == 1),
                None,
            )
            if base is None:
                return None
            factors.append({"q": str(q), "e": str(e), "base": str(base), "certificate": certificate})
        return {"n": str(n), "method": "pocklington", "factors": factors}

    def _morrison(self, n):
        f, proven = self._proven_part(n, n + 1, lambda f: f > 1 and (f - 1) ** 2 > n)
        if not (f > 1 and (f - 1) ** 2 > n):
            return None
        candidates = [
            (p, q)
            for p in range(1, 64)
            for q in (2, -1, -2, 3, -3, 5, -5, 7, -7)
            if p * p - 4 * q != 0 and gcd(n, 2 * q * (p * p - 4 * q)) == 1 and jacobi((p * p - 4 * q) % n, n) == -1
        ]
        factors = []
        for q, e, certificate in proven:
            chosen = None
            for p_param, q_param in candidates:
                if lucas_sequence(p_param, q_param, n + 1, n)[0] != 0:
                    continue
                if gcd(lucas_sequence(p_param, q_param, (n + 1) // q, n)[0], n) == 1:
                    chosen = (p_param, q_param)
                    break
            if chosen is None:
                return None
            factors.append(
                {"q": str(q), "e": str(e), "p": str(chosen[0]), "qparam": str(chosen[1]), "certificate": certificate}
            )
        return {"n": str(n), "method": "morrison", "factors": factors}

    def _goldwasser_kilian(self, n):
        if n.bit_length() < 64 or gcd(n, 6) != 1:
            return None
        candidates = []
        for d in DISCRIMINANTS:
            for m in _cm_orders(n, d):
                q = _strip_small_factors(m)
                if q < n and ecpp_bound_holds(q, n) and is_probable_prime(q):
                    candidates.append((q, m, d))
        rng = random.Random(n)
        for q, m, d in sorted(set(candidates)):
            try:
                step = _find_curve(n, d, m, q, rng)
            except NotInvertible:
                step = None
            if step is None:
                continue
            sub = self.certify(q)
            if sub is None:
                continue
            a, b, (x, y) = step
            return {
                "n": str(n),
                "method": "goldwasser-kilian",
                "a": str(a),
                "b": str(b),
                "x": str(x),
                "y": str(y),
                "m": str(m),
                "q": str(q),
                "certificate": sub,
            }
        return None


def _strip_small_factors(m, rounds=4, iterations=3000):
    for p in SMALL_PRIMES:
        while m % p == 0 and m > p:
            m //= p
    for _ in range(rounds):
        if is_probable_prime(m):
            break
        d = pollard_brent(m, iterations)
        if d is None or d in (1, m):
            break
        m = max(d, m // d)
    return m


def _cornacchia(n, d):
    root = sqrt_mod(d % n, n)
    if root is None:
        return None
    if root % 2 != d % 2:
        root = n - root
    a, b = 2 * n, root
    limit = isqrt(4 * n)
    while b > limit:
        a, b = b, a % b
    rest = 4 * n - b * b
    if rest % -d or not is_square(rest // -d):
        return None
    return b, isqrt(rest // -d)


def _cm_orders(n, d):
    if jacobi(d % n, n) != 1:
        return []
    solution = _cornacchia(n, d)
    if solution is None:
        return []
    u, v = solution
    traces = {u}
    if d == -4:
        traces.add(2 * v)
    if d == -3:
        traces.update({abs(u + 3 * v) // 2, abs(u - 3 * v) // 2})
    orders = set()
    for t in traces:
        orders.update({n + 1 - t, n + 1 + t})
    return sorted(m for m in orders if m > 0)


def _find_curve(n, d, m, q, rng, attempts=48):
    ring = IntegersMod(n)
    if d in (-3, -4):
        shapes = [None]
    else:
        shapes = [j for j in roots_mod(hilbert_class_polynomial(d), n, rng) if j not in (0, 1728 % n)]
        if not shapes:
            return None
    for _ in range(attempts):
        c = rng.randrange(1, n)
        if d == -3:
            a, b = 0, c
        elif d == -4:
            a, b = c, 0
        else:
            j = rng.choice(shapes)
            k = j * pow(1728 - j, -1, n) % n
            a, b = 3 * k * c * c % n, 2 * k * c * c * c % n
        curve = WeierstrassCurve(ring, a, b)
        if gcd(curve.discriminant_factor(), n) != 1:
            continue
        x = rng.randrange(n)
        y = sqrt_mod(curve.rhs(x), n)
        if y is None:
            continue
        point = (x, y)
        try:
            if curve.multiply(point, m) is not INFINITY:
                continue
            if curve.multiply(point, m // q) is INFINITY:
                continue
        except NotInvertible:
            continue
        return a, b, point
    return None
