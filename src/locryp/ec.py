from .algebra import NotInvertible

INFINITY = None


class WeierstrassCurve:
    def __init__(self, ring, a, b):
        self.ring = ring
        self.a = a
        self.b = b

    def discriminant_factor(self):
        r = self.ring
        a3 = r.mul(r.mul(self.a, self.a), self.a)
        b2 = r.mul(self.b, self.b)
        return r.add(r.mul(r.from_int(4), a3), r.mul(r.from_int(27), b2))

    def rhs(self, x):
        r = self.ring
        return r.add(r.add(r.mul(r.mul(x, x), x), r.mul(self.a, x)), self.b)

    def contains(self, point):
        if point is INFINITY:
            return True
        x, y = point
        r = self.ring
        return r.sub(r.mul(y, y), self.rhs(x)) == r.zero()

    def neg(self, point):
        if point is INFINITY:
            return INFINITY
        return (point[0], self.ring.neg(point[1]))

    def double(self, point):
        if point is INFINITY:
            return INFINITY
        r = self.ring
        x, y = point
        if r.is_zero(y):
            return INFINITY
        numerator = r.add(r.mul(r.from_int(3), r.mul(x, x)), self.a)
        slope = r.mul(numerator, r.inv(r.add(y, y)))
        x3 = r.sub(r.mul(slope, slope), r.add(x, x))
        y3 = r.sub(r.mul(slope, r.sub(x, x3)), y)
        return (x3, y3)

    def add(self, p, q):
        if p is INFINITY:
            return q
        if q is INFINITY:
            return p
        r = self.ring
        x1, y1 = p
        x2, y2 = q
        if x1 == x2:
            if r.is_zero(r.add(y1, y2)):
                return INFINITY
            if y1 == y2:
                return self.double(p)
            raise NotInvertible(r.sub(y1, y2))
        slope = r.mul(r.sub(y2, y1), r.inv(r.sub(x2, x1)))
        x3 = r.sub(r.sub(r.mul(slope, slope), x1), x2)
        y3 = r.sub(r.mul(slope, r.sub(x1, x3)), y1)
        return (x3, y3)

    def multiply(self, point, k):
        if k < 0:
            return self.multiply(self.neg(point), -k)
        result = INFINITY
        addend = point
        while k:
            if k & 1:
                result = self.add(result, addend)
            k >>= 1
            if k:
                addend = self.double(addend)
        return result
