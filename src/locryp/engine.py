from math import isqrt

from .algebra import IntegersMod, NotInvertible, rabin_irreducibility
from .certificates import CertificateError, Prover, verify_certificate
from .ec import INFINITY, WeierstrassCurve
from .matrices import enumerate_group, evaluate, identity, inverse, power
from .numtheory import compositeness_witness, factor
from .result import CheckResult, Outcome, Status
from .spec import SpecError

EFFORT = {
    "low": {"rho_iterations": 20000, "node_budget": 500},
    "normal": {"rho_iterations": 100000, "node_budget": 4000},
    "high": {"rho_iterations": 1000000, "node_budget": 20000},
}
POINT_COUNT_LIMIT = 1 << 20
ENUMERATION_LIMIT = 2000000
UNSETTLED = (Status.NOT_PROVEN, Status.ASSUMED, Status.INDETERMINATE)


class Task:
    def __init__(self, check, subject, statement, requires, run):
        self.check = check
        self.subject = subject
        self.statement = statement
        self.requires = [r for r in requires if r is not None]
        self.run = run

    @property
    def key(self):
        return "%s:%s" % (self.check, self.subject)


def primality_outcome(prover, n):
    if n < 2:
        return Outcome(Status.FAIL, "definition", {"n": str(n)}, "integers below two are not prime")
    witness = compositeness_witness(n)
    if witness is not None:
        return Outcome(
            Status.FAIL,
            "compositeness witness",
            {"n": str(n), "witness": {k: str(v) for k, v in witness.items()}},
            "the witness proves that n is composite",
        )
    certificate = prover.certify(n)
    if certificate is None:
        return Outcome(
            Status.NOT_PROVEN,
            "Baillie-PSW probable prime test",
            {"n": str(n)},
            "n is a probable prime but no primality certificate was found within the search budget",
        )
    try:
        verify_certificate(certificate, n)
    except CertificateError as error:
        return Outcome(Status.INDETERMINATE, "primality certificate", {"n": str(n)}, "certificate rejected: %s" % error)
    return Outcome(
        Status.PASS,
        "primality certificate (%s), checked by the independent verifier" % certificate["method"],
        {"n": str(n), "certificate": certificate},
    )


def _encode_point(ring, point):
    if point is INFINITY:
        return "infinity"
    return {"x": ring.encode(point[0]), "y": ring.encode(point[1])}


def _encode_matrix(ring, matrix):
    return [[ring.encode(v) for v in row] for row in matrix]


class Engine:
    def __init__(self, spec, effort="normal"):
        self.spec = spec
        self.prover = Prover(**EFFORT[effort])
        self.results = {}

    def field_key(self, name):
        decl = self.spec.fields[name]
        return "%s:%s" % ("FIELD-PRIME" if decl.prime is not None else "FIELD-IRREDUCIBLE", name)

    def plan(self):
        tasks = []
        for decl in self.spec.fields.values():
            tasks.extend(self._plan_field(decl))
        for curve in self.spec.curves.values():
            tasks.extend(self._plan_curve(curve))
        for group in self.spec.matrix_groups.values():
            tasks.extend(self._plan_group(group))
        for system in self.spec.constraint_systems.values():
            tasks.extend(self._plan_constraints(system))
        keys = {task.key for task in tasks}
        unknown = sorted(self.spec.assumptions - keys)
        if unknown:
            raise SpecError("assumptions", "no planned check matches %s" % ", ".join(unknown))
        return tasks

    def run(self):
        ordered = []
        for task in self.plan():
            result = self._execute(task)
            self.results[task.key] = result
            ordered.append(result)
        return ordered

    def _execute(self, task):
        conditional = set()
        blocked = []
        for key in task.requires:
            dependency = self.results[key]
            if dependency.status == Status.FAIL:
                blocked.append(key)
            elif dependency.status in UNSETTLED:
                conditional.add(key)
            conditional.update(dependency.conditional_on)
        if task.key in self.spec.assumptions:
            outcome = Outcome(Status.ASSUMED, "declared assumption", detail="not checked by request of the specification")
        elif blocked:
            outcome = Outcome(
                Status.INDETERMINATE, "not run", detail="blocked by failed precondition %s" % ", ".join(blocked)
            )
        else:
            try:
                outcome = task.run()
            except NotInvertible:
                outcome = Outcome(
                    Status.INDETERMINATE,
                    "exact arithmetic",
                    detail="a non-invertible element was encountered, so a declared field is not a field",
                )
        return CheckResult(
            task.check,
            task.subject,
            task.statement,
            outcome.status,
            outcome.method,
            outcome.evidence,
            outcome.detail,
            sorted(conditional),
        )

    def prove_prime(self, n):
        return primality_outcome(self.prover, n)

    def _plan_field(self, decl):
        if decl.prime is not None:
            return [
                Task("FIELD-PRIME", decl.name, "the modulus p of %s is prime" % decl.name, [], lambda: self.prove_prime(decl.prime))
            ]
        statement = "the modulus of %s is irreducible over %s, so %s is a field" % (decl.name, decl.base, decl.name)
        return [Task("FIELD-IRREDUCIBLE", decl.name, statement, [self.field_key(decl.base)], lambda: self._irreducible(decl))]

    def _irreducible(self, decl):
        ring = decl.ring
        outcome = rabin_irreducibility(ring.base, ring.modulus)
        evidence = {"degree": str(ring.degree), "base_order": str(ring.base.order), "field_order": str(ring.order)}
        if outcome["irreducible"]:
            return Outcome(Status.PASS, "Rabin irreducibility test (exact)", evidence)
        evidence["failed_condition"] = outcome["failed"]
        if "factor" in outcome:
            evidence["common_factor"] = outcome["factor"]
        return Outcome(Status.FAIL, "Rabin irreducibility test (exact)", evidence, "the quotient ring has zero divisors")

    def _plan_curve(self, c):
        ring = self.spec.fields[c.field].ring
        curve = WeierstrassCurve(ring, c.a, c.b)
        fk = self.field_key(c.field)
        name = c.name
        tasks = [
            Task(
                "CURVE-NONSINGULAR",
                name,
                "4a^3 + 27b^2 is nonzero in %s, so %s is an elliptic curve" % (c.field, name),
                [fk],
                lambda: self._nonsingular(curve),
            )
        ]
        if c.generator is not None:
            tasks.append(
                Task("CURVE-POINT", name, "the generator G lies on %s" % name, [fk], lambda: self._on_curve(curve, c.generator))
            )
        if c.subgroup_order is None:
            return tasks
        r = c.subgroup_order
        prime_key = None
        if c.prime_order:
            prime_key = "SUBGROUP-PRIME:%s" % name
            tasks.append(Task("SUBGROUP-PRIME", name, "the subgroup order r is prime", [], lambda: self.prove_prime(r)))
        tasks.append(
            Task(
                "CURVE-NOT-ANOMALOUS",
                name,
                "r differs from the characteristic of %s" % c.field,
                [fk],
                lambda: self._not_anomalous(ring, r),
            )
        )
        order_key = None
        if c.generator is not None:
            order_key = "GENERATOR-ORDER:%s" % name
            tasks.append(
                Task(
                    "GENERATOR-ORDER",
                    name,
                    "G has order exactly r",
                    [fk, "CURVE-NONSINGULAR:%s" % name, "CURVE-POINT:%s" % name, prime_key],
                    lambda: self._generator_order(curve, c),
                )
            )
        claimed = c.cardinality if c.cardinality is not None else (c.cofactor * r if c.cofactor is not None else None)
        if c.cardinality is not None:
            if c.cofactor is not None:
                statement = "the declared cardinality N equals the cofactor h times r"
            else:
                statement = "r divides the declared cardinality N"
            tasks.append(Task("CURVE-COFACTOR", name, statement, [], lambda: self._cofactor(c)))
        if claimed is not None:
            tasks.append(
                Task(
                    "CURVE-CARDINALITY",
                    name,
                    "%s has exactly %d points over %s" % (name, claimed, c.field),
                    [fk, "CURVE-NONSINGULAR:%s" % name, order_key],
                    lambda: self._cardinality(curve, c, claimed),
                )
            )
        if c.prime_order:
            if c.embedding_degree is not None:
                statement = "the embedding degree of the order r subgroup is exactly %d" % c.embedding_degree
            else:
                statement = "the embedding degree of the order r subgroup is at least %d" % c.minimum_embedding_degree
            tasks.append(
                Task("CURVE-EMBEDDING-DEGREE", name, statement, [fk, prime_key], lambda: self._embedding_degree(ring, c))
            )
        return tasks

    def _nonsingular(self, curve):
        value = curve.discriminant_factor()
        evidence = {"4a^3+27b^2": curve.ring.encode(value)}
        if curve.ring.is_zero(value):
            return Outcome(Status.FAIL, "exact field arithmetic", evidence, "the cubic has a repeated root")
        return Outcome(Status.PASS, "exact field arithmetic", evidence)

    def _on_curve(self, curve, point):
        ring = curve.ring
        lhs = ring.mul(point[1], point[1])
        rhs = curve.rhs(point[0])
        if lhs == rhs:
            return Outcome(Status.PASS, "exact field arithmetic")
        return Outcome(
            Status.FAIL,
            "exact field arithmetic",
            {"y^2": ring.encode(lhs), "x^3+ax+b": ring.encode(rhs)},
            "y^2 differs from x^3 + ax + b",
        )

    def _not_anomalous(self, ring, r):
        evidence = {"r": str(r), "characteristic": str(ring.characteristic)}
        if r == ring.characteristic:
            return Outcome(
                Status.FAIL, "integer comparison", evidence, "the discrete logarithm is solvable by the Smart-Satoh-Araki-Semaev attack"
            )
        return Outcome(Status.PASS, "integer comparison", evidence)

    def _prime_factorization(self, n, assume_prime):
        if assume_prime:
            return {n: 1}, []
        decomposition = self.prover.factorization(n)
        if not decomposition.complete:
            return None, ["could not fully factor %d" % n]
        unproven = [q for q in decomposition.primes if self.prover.certify(q) is None]
        return decomposition.primes, ["factor %d is only a probable prime" % q for q in unproven]

    def _generator_order(self, curve, c):
        r = c.subgroup_order
        primes, problems = self._prime_factorization(r, c.prime_order)
        if primes is None:
            return Outcome(Status.INDETERMINATE, "scalar multiplication", {"r": str(r)}, "; ".join(problems))
        ring = curve.ring
        g = c.generator
        image = curve.multiply(g, r)
        if image is not INFINITY:
            return Outcome(
                Status.FAIL,
                "scalar multiplication",
                {"[r]G": _encode_point(ring, image)},
                "[r]G is not the point at infinity, so the order of G does not divide r",
            )
        for q in primes:
            if curve.multiply(g, r // q) is INFINITY:
                return Outcome(
                    Status.FAIL,
                    "scalar multiplication",
                    {"prime": str(q)},
                    "[r/%d]G is the point at infinity, so the order of G is a proper divisor of r" % q,
                )
        evidence = {"prime_factors_of_r": {str(q): str(e) for q, e in primes.items()}}
        if problems:
            return Outcome(Status.NOT_PROVEN, "scalar multiplication", evidence, "; ".join(problems))
        return Outcome(Status.PASS, "scalar multiplication with the prime factors of r", evidence)

    def _cofactor(self, c):
        n, r = c.cardinality, c.subgroup_order
        if c.cofactor is not None:
            evidence = {"N": str(n), "h*r": str(c.cofactor * r)}
            if n == c.cofactor * r:
                return Outcome(Status.PASS, "integer arithmetic", evidence)
            return Outcome(Status.FAIL, "integer arithmetic", evidence, "N differs from h times r")
        quotient, remainder = divmod(n, r)
        evidence = {"N": str(n), "r": str(r), "remainder": str(remainder)}
        if remainder:
            return Outcome(Status.FAIL, "integer arithmetic", evidence, "r does not divide N")
        evidence["cofactor"] = str(quotient)
        return Outcome(Status.PASS, "integer arithmetic", evidence)

    def _cardinality(self, curve, c, claimed):
        q = curve.ring.order
        width = isqrt(4 * q)
        low, high = q + 1 - width, q + 1 + width
        interval = {"low": str(low), "high": str(high)}
        if not low <= claimed <= high:
            return Outcome(
                Status.FAIL,
                "Hasse bound",
                {"claimed": str(claimed), "hasse_interval": interval},
                "every elliptic curve over a field of order q has between q + 1 - 2 sqrt(q) and q + 1 + 2 sqrt(q) points",
            )
        if c.generator is not None:
            r = c.subgroup_order
            first = -(-low // r) * r
            multiples = high // r - (low - 1) // r
            if multiples == 1:
                evidence = {"hasse_interval": interval, "cardinality": str(first)}
                method = "Hasse interval contains exactly one multiple of the order of G"
                if first == claimed:
                    return Outcome(Status.PASS, method, evidence)
                return Outcome(Status.FAIL, method, evidence, "the cardinality is %d" % first)
        if isinstance(curve.ring, IntegersMod) and q <= POINT_COUNT_LIMIT:
            count = self._count_points(curve)
            evidence = {"cardinality": str(count)}
            if count == claimed:
                return Outcome(Status.PASS, "exhaustive point count", evidence)
            return Outcome(Status.FAIL, "exhaustive point count", evidence, "the cardinality is %d" % count)
        return Outcome(
            Status.INDETERMINATE,
            "Hasse bound",
            {"hasse_interval": interval},
            "the claim lies in the Hasse interval but the cardinality could not be determined uniquely",
        )

    def _count_points(self, curve):
        p = curve.ring.n
        half = (p - 1) // 2
        total = p + 1
        for x in range(p):
            value = curve.rhs(x)
            if value:
                total += 1 if pow(value, half, p) == 1 else -1
        return total

    def _embedding_degree(self, ring, c):
        r = c.subgroup_order
        q = ring.order
        if q % r == 0:
            return Outcome(Status.NOT_APPLICABLE, "modular exponentiation", {}, "r divides the field order")
        if c.embedding_degree is not None:
            k = c.embedding_degree
            evidence = {"k": str(k)}
            if pow(q, k, r) != 1:
                return Outcome(Status.FAIL, "modular exponentiation", evidence, "q^k is not congruent to 1 modulo r")
            for prime in factor(k).primes:
                if pow(q, k // prime, r) == 1:
                    return Outcome(
                        Status.FAIL,
                        "modular exponentiation",
                        evidence,
                        "q^(k/%d) is congruent to 1 modulo r, so the embedding degree is smaller" % prime,
                    )
            return Outcome(Status.PASS, "modular exponentiation with the prime factors of k", evidence)
        bound = c.minimum_embedding_degree
        value = 1
        for k in range(1, bound):
            value = value * q % r
            if value == 1:
                return Outcome(
                    Status.FAIL,
                    "exhaustive search below the bound",
                    {"embedding_degree": str(k)},
                    "the pairing maps the subgroup into the multiplicative group of a degree %d extension" % k,
                )
        return Outcome(Status.PASS, "exhaustive search below the bound", {"bound": str(bound)})

    def _plan_group(self, g):
        ring = self.spec.fields[g.field].ring
        fk = self.field_key(g.field)
        matrices_key = "GROUP-MATRICES:%s" % g.name
        requires = [fk, matrices_key]
        tasks = [
            Task(
                "GROUP-MATRICES",
                g.name,
                "every generator of %s is an invertible %d by %d matrix over %s" % (g.name, g.size, g.size, g.field),
                [fk],
                lambda: self._invertible(ring, g),
            )
        ]
        for text, tree in g.relators:
            tasks.append(
                Task(
                    "GROUP-RELATOR",
                    "%s[%s]" % (g.name, text),
                    "the relator %s evaluates to the identity" % text,
                    requires,
                    lambda tree=tree, text=text: self._relator(ring, g, tree),
                )
            )
        for text, tree, order in g.element_orders:
            tasks.append(
                Task(
                    "GROUP-ELEMENT-ORDER",
                    "%s[%s]" % (g.name, text),
                    "the element %s has order exactly %d" % (text, order),
                    requires,
                    lambda tree=tree, order=order: self._element_order(ring, g, tree, order),
                )
            )
        if g.order is not None:
            tasks.append(
                Task(
                    "GROUP-ORDER",
                    g.name,
                    "the generated group %s has exactly %d elements" % (g.name, g.order),
                    requires,
                    lambda: self._group_order(ring, g),
                )
            )
        return tasks

    def _invertible(self, ring, g):
        for name, matrix in g.generators.items():
            try:
                inverse(ring, matrix)
            except NotInvertible:
                return Outcome(Status.FAIL, "Gaussian elimination", {"generator": name}, "the generator %s is singular" % name)
        return Outcome(Status.PASS, "Gaussian elimination")

    def _relator(self, ring, g, tree):
        value = evaluate(ring, tree, g.generators, g.size)
        if value == identity(ring, g.size):
            return Outcome(Status.PASS, "exact matrix arithmetic")
        return Outcome(
            Status.FAIL, "exact matrix arithmetic", {"value": _encode_matrix(ring, value)}, "the relator is not the identity"
        )

    def _element_order(self, ring, g, tree, order):
        element = evaluate(ring, tree, g.generators, g.size)
        one = identity(ring, g.size)
        decomposition = factor(order)
        if not decomposition.complete:
            return Outcome(Status.INDETERMINATE, "exact matrix arithmetic", {}, "could not factor the claimed order")
        if power(ring, element, order) != one:
            return Outcome(Status.FAIL, "exact matrix arithmetic", {}, "the element raised to the claimed order is not the identity")
        for q in decomposition.primes:
            if power(ring, element, order // q) == one:
                return Outcome(
                    Status.FAIL,
                    "exact matrix arithmetic",
                    {"prime": str(q)},
                    "the element raised to order/%d is the identity, so its order is smaller" % q,
                )
        return Outcome(Status.PASS, "exact matrix arithmetic with the prime factors of the order")

    def _group_order(self, ring, g):
        if g.order > ENUMERATION_LIMIT:
            return Outcome(
                Status.INDETERMINATE, "enumeration", {}, "the claimed order exceeds the enumeration limit of %d" % ENUMERATION_LIMIT
            )
        count = enumerate_group(ring, list(g.generators.values()), g.size, g.order)
        if count is None:
            return Outcome(Status.FAIL, "exhaustive enumeration", {}, "the group has more than %d elements" % g.order)
        if count == g.order:
            return Outcome(Status.PASS, "exhaustive enumeration", {"order": str(count)})
        return Outcome(Status.FAIL, "exhaustive enumeration", {"order": str(count)}, "the group has %d elements" % count)

    def _plan_constraints(self, system):
        if system.witness is None:
            return []
        ring = self.spec.fields[system.field].ring
        return [
            Task(
                "R1CS-WITNESS",
                system.name,
                "the witness satisfies every constraint of %s" % system.name,
                [self.field_key(system.field)],
                lambda: self._witness(ring, system),
            )
        ]

    def _witness(self, ring, system):
        w = system.witness
        if w[0] != ring.one():
            return Outcome(Status.FAIL, "exact field arithmetic", {}, "witness entry 0 must be the constant one")

        def dot(terms):
            total = ring.zero()
            for index, coefficient in terms:
                total = ring.add(total, ring.mul(coefficient, w[index]))
            return total

        for i, (a, b, c) in enumerate(system.constraints):
            left = ring.mul(dot(a), dot(b))
            right = dot(c)
            if left != right:
                return Outcome(
                    Status.FAIL,
                    "exact field arithmetic",
                    {"constraint": str(i), "a*b": ring.encode(left), "c": ring.encode(right)},
                    "constraint %d is not satisfied" % i,
                )
        return Outcome(Status.PASS, "exact field arithmetic", {"constraints": str(len(system.constraints))})
