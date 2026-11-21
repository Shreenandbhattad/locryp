from math import gcd, isqrt


def small_primes(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, isqrt(limit) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(range(i * i, limit + 1, i)))
    return [i for i in range(limit + 1) if sieve[i]]


SMALL_PRIMES = small_primes(1 << 16)


def is_square(n):
    if n < 0:
        return False
    r = isqrt(n)
    return r * r == n


def jacobi(a, n):
    if n <= 0 or n % 2 == 0:
        raise ValueError("jacobi symbol requires a positive odd modulus")
    a %= n
    result = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a %= n
    return result if n == 1 else 0


def strong_probable_prime(n, base):
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    x = pow(base, d, n)
    if x == 1 or x == n - 1:
        return True
    for _ in range(s - 1):
        x = x * x % n
        if x == n - 1:
            return True
    return False


def _half(x, n):
    return (x + n) // 2 if x % 2 else x // 2


def strong_lucas_probable_prime(n):
    d_param = 5
    while True:
        j = jacobi(d_param, n)
        if j == -1:
            break
        if j == 0 and abs(d_param) != n:
            return False
        d_param = -d_param - 2 if d_param > 0 else -d_param + 2
        if d_param == 13 and is_square(n):
            return False
    q_param = (1 - d_param) // 4
    d = n + 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    u, v, qk = 1, 1, q_param % n
    for bit in bin(d)[3:]:
        u = u * v % n
        v = (v * v - 2 * qk) % n
        qk = qk * qk % n
        if bit == "1":
            u, v = _half((u + v) % n, n), _half((d_param * u + v) % n, n)
            qk = qk * q_param % n
    if u == 0 or v == 0:
        return True
    for _ in range(s - 1):
        v = (v * v - 2 * qk) % n
        qk = qk * qk % n
        if v == 0:
            return True
    return False


def is_probable_prime(n):
    if n < 2:
        return False
    for p in SMALL_PRIMES[:64]:
        if n % p == 0:
            return n == p
    return strong_probable_prime(n, 2) and strong_lucas_probable_prime(n)


def compositeness_witness(n, rounds=32):
    if n < 2:
        return {"reason": "less than two"}
    for p in SMALL_PRIMES:
        if p * p > n:
            return None
        if n % p == 0:
            return None if n == p else {"factor": p}
    for base in SMALL_PRIMES[:rounds]:
        if not strong_probable_prime(n, base):
            return {"miller_rabin_base": base}
    return None


def pollard_brent(n, max_iterations):
    if n % 2 == 0:
        return 2
    for c in range(1, 64):
        y, r, q, g = 2, 1, 1, 1
        x = ys = 2
        iterations = 0
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(128, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = gcd(q, n)
                k += 128
            r *= 2
            iterations += r
            if iterations > max_iterations:
                return None
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n
                g = gcd(abs(x - ys), n)
        if g != n:
            return g
    return None


class Factorization:
    def __init__(self, n, primes, unfactored):
        self.n = n
        self.primes = primes
        self.unfactored = unfactored

    @property
    def complete(self):
        return not self.unfactored

    @property
    def factored_part(self):
        result = 1
        for p, e in self.primes.items():
            result *= p**e
        return result


def factor(n, max_iterations=200000):
    if n < 1:
        raise ValueError("factor requires a positive integer")
    primes = {}
    for p in SMALL_PRIMES:
        if p * p > n:
            break
        while n % p == 0:
            primes[p] = primes.get(p, 0) + 1
            n //= p
    pending = [n] if n > 1 else []
    unfactored = []
    while pending:
        m = pending.pop()
        if m == 1:
            continue
        if is_probable_prime(m):
            primes[m] = primes.get(m, 0) + 1
            continue
        root = isqrt(m)
        if root * root == m:
            pending.extend([root, root])
            continue
        d = pollard_brent(m, max_iterations)
        if d is None:
            unfactored.append(m)
        else:
            pending.extend([d, m // d])
    total = 1
    for p, e in primes.items():
        total *= p**e
    for m in unfactored:
        total *= m
    return Factorization(total, dict(sorted(primes.items())), sorted(unfactored))


def sqrt_mod(a, p):
    a %= p
    if a == 0:
        return 0
    if p == 2:
        return a
    if pow(a, (p - 1) // 2, p) != 1:
        return None
    if p % 4 == 3:
        root = pow(a, (p + 1) // 4, p)
        return root if root * root % p == a else None
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
        if z > 1000:
            return None
    m, c, t, root = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p
            i += 1
            if i == m:
                return None
        b = pow(c, 1 << (m - i - 1), p)
        m, c = i, b * b % p
        t, root = t * c % p, root * b % p
    return root if root * root % p == a else None


def lucas_sequence(p_param, q_param, k, n):
    d_param = p_param * p_param - 4 * q_param
    u, v, qk = 0, 2 % n, 1
    for bit in bin(k)[2:]:
        u = u * v % n
        v = (v * v - 2 * qk) % n
        qk = qk * qk % n
        if bit == "1":
            u, v = _half((p_param * u + v) % n, n), _half((d_param * u + p_param * v) % n, n)
            qk = qk * q_param % n
    return u, v
