import re

from .algebra import NotInvertible

_TOKEN = re.compile(r"\s*(?:([A-Za-z_][A-Za-z0-9_]*)|(-?\d+)|(.))")


class WordError(ValueError):
    pass


def identity(ring, n):
    return tuple(tuple(ring.one() if i == j else ring.zero() for j in range(n)) for i in range(n))


def multiply(ring, x, y):
    size = len(y)
    columns = list(zip(*y))
    result = []
    for row in x:
        out = []
        for column in columns:
            total = ring.zero()
            for k in range(size):
                total = ring.add(total, ring.mul(row[k], column[k]))
            out.append(total)
        result.append(tuple(out))
    return tuple(result)


def inverse(ring, matrix):
    n = len(matrix)
    rows = [list(row) + list(identity_row) for row, identity_row in zip(matrix, identity(ring, n))]
    for column in range(n):
        pivot = next((r for r in range(column, n) if not ring.is_zero(rows[r][column])), None)
        if pivot is None:
            raise NotInvertible("matrix is singular")
        rows[column], rows[pivot] = rows[pivot], rows[column]
        scale = ring.inv(rows[column][column])
        rows[column] = [ring.mul(v, scale) for v in rows[column]]
        for r in range(n):
            if r != column and not ring.is_zero(rows[r][column]):
                factor_value = rows[r][column]
                rows[r] = [ring.sub(v, ring.mul(factor_value, w)) for v, w in zip(rows[r], rows[column])]
    return tuple(tuple(row[n:]) for row in rows)


def power(ring, matrix, exponent):
    if exponent < 0:
        return power(ring, inverse(ring, matrix), -exponent)
    result = identity(ring, len(matrix))
    while exponent:
        if exponent & 1:
            result = multiply(ring, result, matrix)
        matrix = multiply(ring, matrix, matrix)
        exponent >>= 1
    return result


def _tokens(text):
    position = 0
    tokens = []
    text = text.rstrip()
    while position < len(text):
        match = _TOKEN.match(text, position)
        name, number, symbol = match.groups()
        if symbol is not None and symbol not in "*^()":
            raise WordError("unexpected character %r in word %r" % (symbol, text))
        tokens.append(("name", name) if name else ("number", int(number)) if number else ("symbol", symbol))
        position = match.end()
    return tokens


def parse_word(text, generators):
    tokens = _tokens(text)
    position = 0

    def peek():
        return tokens[position] if position < len(tokens) else (None, None)

    def take(kind, value=None):
        nonlocal position
        token = peek()
        if token[0] != kind or (value is not None and token[1] != value):
            raise WordError("malformed word %r" % text)
        position += 1
        return token[1]

    def word():
        parts = [factor_term()]
        while peek() == ("symbol", "*"):
            take("symbol", "*")
            parts.append(factor_term())
        return ("product", parts)

    def factor_term():
        token = peek()
        if token == ("symbol", "("):
            take("symbol", "(")
            base = word()
            take("symbol", ")")
        elif token[0] == "name":
            name = take("name")
            if name not in generators:
                raise WordError("unknown generator %r in word %r" % (name, text))
            base = ("generator", name)
        else:
            raise WordError("malformed word %r" % text)
        if peek() == ("symbol", "^"):
            take("symbol", "^")
            return ("power", base, take("number"))
        return base

    if not tokens:
        raise WordError("empty word")
    tree = word()
    if position != len(tokens):
        raise WordError("malformed word %r" % text)
    return tree


def evaluate(ring, tree, matrices, size):
    kind = tree[0]
    if kind == "generator":
        return matrices[tree[1]]
    if kind == "power":
        return power(ring, evaluate(ring, tree[1], matrices, size), tree[2])
    result = identity(ring, size)
    for part in tree[1]:
        result = multiply(ring, result, evaluate(ring, part, matrices, size))
    return result


def enumerate_group(ring, generators, size, limit):
    one = identity(ring, size)
    seen = {one}
    frontier = [one]
    while frontier:
        next_frontier = []
        for element in frontier:
            for generator in generators:
                product = multiply(ring, element, generator)
                if product not in seen:
                    seen.add(product)
                    if len(seen) > limit:
                        return None
                    next_frontier.append(product)
        frontier = next_frontier
    return len(seen)
