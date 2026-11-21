from math import gcd, isqrt

from .algebra import IntegersMod, NotInvertible, poly_divmod, poly_gcd, poly_monic, poly_powmod, poly_sub

_CACHE = {}


def reduced_forms(d):
    if d >= 0 or d % 4 not in (0, 1):
        raise ValueError("discriminant must be negative and congruent to 0 or 1 mod 4")
    forms = []
    a = 1
    while 3 * a * a <= -d:
        for b in range(-a + 1, a + 1):
            if (b - d) % 2:
                continue
            numerator = b * b - d
            if numerator % (4 * a):
                continue
            c = numerator // (4 * a)
            if c < a or (b < 0 and c == a):
                continue
            if gcd(gcd(a, b), c) != 1:
                continue
            forms.append((a, b, c))
        a += 1
    return forms


def _atan_inverse(x, one):
    total = term = one // x
    x2 = x * x
    k = 1
    sign = -1
    while term:
        term //= x2
        total += sign * (term // (2 * k + 1))
        sign = -sign
        k += 1
    return total


def _pi(bits):
    one = 1 << (bits + 32)
    value = 16 * _atan_inverse(5, one) - 4 * _atan_inverse(239, one)
    return value >> 32


def _exp(x, bits):
    one = 1 << bits
    halvings = max(0, abs(x).bit_length() - bits + 8)
    x >>= halvings
    total = term = one
    k = 1
    while term:
        term = term * x // (one * k)
        total += term
        k += 1
    for _ in range(halvings):
        total = total * total >> bits
    return total


def _cos_sin(theta, bits):
    one = 1 << bits
    cos_total = cos_term = one
    sin_total = sin_term = theta
    k = 1
    while cos_term or sin_term:
        cos_term = -cos_term * theta * theta // (one * one * (2 * k - 1) * (2 * k))
        sin_term = -sin_term * theta * theta // (one * one * (2 * k) * (2 * k + 1))
        cos_total += cos_term
        sin_total += sin_term
        k += 1
    return cos_total, sin_total


def _cmul(x, y, bits):
    return ((x[0] * y[0] - x[1] * y[1]) >> bits, (x[0] * y[1] + x[1] * y[0]) >> bits)


def _cdiv(x, y, bits):
    norm = (y[0] * y[0] + y[1] * y[1]) >> bits
    numerator = _cmul(x, (y[0], -y[1]), bits)
    return ((numerator[0] << bits) // norm, (numerator[1] << bits) // norm)


def _j_value(form, d, bits, pi):
    a, b, _ = form
    one = 1 << bits
    root = isqrt(-d << (2 * bits))
    modulus = _exp(-(pi * root // one) // a, bits)
    angle = -(pi * b) // a
    cos_value, sin_value = _cos_sin(angle, bits)
    q = (modulus * cos_value >> bits, modulus * sin_value >> bits)
    terms = bits // 7 + 2
    sigma3 = [0] * (terms + 1)
    for i in range(1, terms + 1):
        for k in range(i, terms + 1, i):
            sigma3[k] += i**3
    e4 = (one, 0)
    product = (one, 0)
    power = (one, 0)
    for n in range(1, terms + 1):
        power = _cmul(power, q, bits)
        e4 = (e4[0] + 240 * sigma3[n] * power[0], e4[1] + 240 * sigma3[n] * power[1])
        product = _cmul(product, (one - power[0], -power[1]), bits)
    eta24 = (one, 0)
    for _ in range(24):
        eta24 = _cmul(eta24, product, bits)
    cube = _cmul(_cmul(e4, e4, bits), e4, bits)
    return _cdiv(cube, _cmul(q, eta24, bits), bits)


def hilbert_class_polynomial(d):
    if d in _CACHE:
        return _CACHE[d]
    forms = reduced_forms(d)
    pi_estimate = 3.1416
    magnitude_bits = int(sum(pi_estimate * (-d) ** 0.5 / a for a, _, _ in forms) / 0.6931) + 1
    bits = 2 * magnitude_bits + 160
    while True:
        pi = _pi(bits)
        roots = [_j_value(form, d, bits, pi) for form in forms]
        one = 1 << bits
        coefficients = [(one, 0)]
        for root in roots:
            shifted = [(0, 0)] + coefficients
            for i, c in enumerate(coefficients):
                product = _cmul(c, root, bits)
                shifted[i] = (shifted[i][0] - product[0], shifted[i][1] - product[1])
            coefficients = shifted
        tolerance = one >> 16
        result = []
        exact = True
        for re, im in coefficients:
            nearest = (re + one // 2) >> bits
            if abs(re - (nearest << bits)) > tolerance or abs(im) > tolerance:
                exact = False
                break
            result.append(nearest)
        if exact:
            _CACHE[d] = result
            return result
        bits *= 2


def discriminants(limit=1200, max_class_number=12):
    found = []
    for magnitude in range(3, limit + 1):
        d = -magnitude
        if d % 4 not in (0, 1):
            continue
        h = len(reduced_forms(d))
        if h <= max_class_number:
            found.append((h, magnitude, d))
    return [d for _, _, d in sorted(found)]


def roots_mod(polynomial, n, rng, limit=1):
    ring = IntegersMod(n)
    f = poly_monic(ring, [c % n for c in polynomial])
    x = [0, 1]
    split = poly_gcd(ring, f, poly_sub(ring, poly_powmod(ring, x, n, f), x))
    roots = []
    pending = [split]
    while pending and len(roots) < limit:
        g = pending.pop()
        if len(g) <= 1:
            continue
        if len(g) == 2:
            roots.append(-g[0] % n)
            continue
        for _ in range(64):
            shift = [rng.randrange(n), 1]
            h = poly_sub(ring, poly_powmod(ring, shift, (n - 1) // 2, g), [1])
            candidate = poly_gcd(ring, g, h)
            if 1 < len(candidate) < len(g):
                pending.append(candidate)
                pending.append(poly_monic(ring, poly_divmod(ring, g, candidate)[0]))
                break
        else:
            raise NotInvertible("root splitting did not converge")
    return roots
