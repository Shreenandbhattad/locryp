import hashlib
import json
import re
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

from .algebra import ExtensionField, IntegersMod, NotInvertible
from .matrices import WordError, parse_word

SPEC_VERSION = 1
_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
_INTEGER = re.compile(r"^-?(0x[0-9a-fA-F]+|[0-9]+)$")


class SpecError(ValueError):
    def __init__(self, path, message):
        super().__init__("%s: %s" % (path, message))
        self.path = path
        self.message = message


@dataclass
class FieldDecl:
    name: str
    ring: object
    prime: int = None
    base: str = None


@dataclass
class CurveDecl:
    name: str
    field: str
    a: object
    b: object
    generator: tuple = None
    subgroup_order: int = None
    cofactor: int = None
    cardinality: int = None
    prime_order: bool = True
    embedding_degree: int = None
    minimum_embedding_degree: int = 100


@dataclass
class MatrixGroupDecl:
    name: str
    field: str
    size: int
    generators: dict
    relators: list
    element_orders: list
    order: int = None


@dataclass
class ConstraintSystemDecl:
    name: str
    field: str
    variables: int
    constraints: list
    witness: list = None


@dataclass
class Specification:
    name: str
    sha256: str
    fields: dict = field(default_factory=dict)
    curves: dict = field(default_factory=dict)
    matrix_groups: dict = field(default_factory=dict)
    constraint_systems: dict = field(default_factory=dict)
    assumptions: set = field(default_factory=set)


def parse_integer(value, path, minimum=None):
    if isinstance(value, bool):
        raise SpecError(path, "expected an integer, found a boolean")
    if isinstance(value, int):
        result = value
    elif isinstance(value, str) and _INTEGER.match(value.strip()):
        text = value.strip()
        negative = text.startswith("-")
        body = text[1:] if negative else text
        result = int(body, 16) if body.lower().startswith("0x") else int(body)
        result = -result if negative else result
    else:
        raise SpecError(path, "expected an integer or an integer string, found %r" % (value,))
    if minimum is not None and result < minimum:
        raise SpecError(path, "must be at least %d" % minimum)
    return result


def _element(ring, value, path):
    if isinstance(ring, IntegersMod):
        return ring.from_int(parse_integer(value, path))
    if not isinstance(value, list):
        if isinstance(value, (int, str)) and not isinstance(value, bool):
            return ring.from_int(parse_integer(value, path))
        raise SpecError(path, "expected a list of coefficients for an extension field element")
    if len(value) > ring.degree:
        raise SpecError(path, "element has more than %d coefficients" % ring.degree)
    coefficients = [_element(ring.base, v, "%s[%d]" % (path, i)) for i, v in enumerate(value)]
    coefficients += [ring.base.zero()] * (ring.degree - len(coefficients))
    return tuple(coefficients)


def _table(data, key, path):
    value = data.get(key, {})
    if not isinstance(value, dict):
        raise SpecError("%s.%s" % (path, key) if path else key, "expected a table")
    for name in value:
        if not _NAME.match(name):
            raise SpecError("%s.%s" % (key, name), "names must be identifiers")
    return value


def _known(data, allowed, path):
    unknown = sorted(set(data) - set(allowed))
    if unknown:
        raise SpecError(path, "unknown keys: %s" % ", ".join(unknown))


def _require_dict(value, path):
    if not isinstance(value, dict):
        raise SpecError(path, "expected a table")
    return value


def _parse_fields(data, spec):
    for name, raw in _table(data, "fields", "").items():
        path = "fields.%s" % name
        raw = _require_dict(raw, path)
        if "prime" in raw:
            _known(raw, {"prime"}, path)
            p = parse_integer(raw["prime"], path + ".prime", minimum=2)
            spec.fields[name] = FieldDecl(name, IntegersMod(p), prime=p)
        elif "base" in raw:
            _known(raw, {"base", "modulus"}, path)
            base_name = raw["base"]
            if base_name not in spec.fields:
                raise SpecError(path + ".base", "unknown or later-declared field %r" % base_name)
            base = spec.fields[base_name].ring
            modulus = raw.get("modulus")
            if not isinstance(modulus, list) or len(modulus) < 2:
                raise SpecError(path + ".modulus", "expected a list of at least two coefficients, constant term first")
            coefficients = [_element(base, c, "%s.modulus[%d]" % (path, i)) for i, c in enumerate(modulus)]
            if base.is_zero(coefficients[-1]):
                raise SpecError(path + ".modulus", "leading coefficient must be nonzero")
            try:
                ring = ExtensionField(base, coefficients)
            except NotInvertible:
                raise SpecError(path + ".modulus", "leading coefficient is not invertible in the base")
            spec.fields[name] = FieldDecl(name, ring, base=base_name)
        else:
            raise SpecError(path, "a field needs either 'prime' or 'base' and 'modulus'")


def _field_ref(raw, path, spec):
    name = raw.get("field")
    if name not in spec.fields:
        raise SpecError(path + ".field", "unknown field %r" % (name,))
    return name, spec.fields[name].ring


def _parse_curves(data, spec):
    allowed = {
        "field",
        "a",
        "b",
        "generator",
        "subgroup_order",
        "cofactor",
        "cardinality",
        "prime_order",
        "embedding_degree",
        "minimum_embedding_degree",
    }
    for name, raw in _table(data, "curves", "").items():
        path = "curves.%s" % name
        raw = _require_dict(raw, path)
        _known(raw, allowed, path)
        field_name, ring = _field_ref(raw, path, spec)
        if ring.characteristic in (2, 3):
            raise SpecError(path, "the short Weierstrass model requires characteristic greater than 3")
        for key in ("a", "b"):
            if key not in raw:
                raise SpecError(path, "missing coefficient %r" % key)
        curve = CurveDecl(name, field_name, _element(ring, raw["a"], path + ".a"), _element(ring, raw["b"], path + ".b"))
        if "generator" in raw:
            g = _require_dict(raw["generator"], path + ".generator")
            _known(g, {"x", "y"}, path + ".generator")
            if "x" not in g or "y" not in g:
                raise SpecError(path + ".generator", "generator needs x and y")
            curve.generator = (_element(ring, g["x"], path + ".generator.x"), _element(ring, g["y"], path + ".generator.y"))
        if "subgroup_order" in raw:
            curve.subgroup_order = parse_integer(raw["subgroup_order"], path + ".subgroup_order", minimum=2)
        if "cofactor" in raw:
            curve.cofactor = parse_integer(raw["cofactor"], path + ".cofactor", minimum=1)
        if "cardinality" in raw:
            curve.cardinality = parse_integer(raw["cardinality"], path + ".cardinality", minimum=1)
        if "prime_order" in raw:
            if not isinstance(raw["prime_order"], bool):
                raise SpecError(path + ".prime_order", "expected true or false")
            curve.prime_order = raw["prime_order"]
        if "embedding_degree" in raw:
            curve.embedding_degree = parse_integer(raw["embedding_degree"], path + ".embedding_degree", minimum=1)
        if "minimum_embedding_degree" in raw:
            curve.minimum_embedding_degree = parse_integer(
                raw["minimum_embedding_degree"], path + ".minimum_embedding_degree", minimum=1
            )
        if (curve.cofactor is not None or curve.cardinality is not None) and curve.subgroup_order is None:
            raise SpecError(path, "cofactor and cardinality require subgroup_order")
        if curve.generator is not None and curve.subgroup_order is None:
            raise SpecError(path, "a generator requires subgroup_order")
        spec.curves[name] = curve


def _matrix(ring, raw, size, path):
    if not isinstance(raw, list) or len(raw) != size:
        raise SpecError(path, "expected a %d by %d matrix" % (size, size))
    rows = []
    for i, row in enumerate(raw):
        if not isinstance(row, list) or len(row) != size:
            raise SpecError("%s[%d]" % (path, i), "expected a row of length %d" % size)
        rows.append(tuple(_element(ring, v, "%s[%d][%d]" % (path, i, j)) for j, v in enumerate(row)))
    return tuple(rows)


def _parse_matrix_groups(data, spec):
    allowed = {"field", "size", "generators", "relators", "element_orders", "order"}
    for name, raw in _table(data, "matrix_groups", "").items():
        path = "matrix_groups.%s" % name
        raw = _require_dict(raw, path)
        _known(raw, allowed, path)
        field_name, ring = _field_ref(raw, path, spec)
        size = parse_integer(raw.get("size"), path + ".size", minimum=1)
        generators_raw = _require_dict(raw.get("generators"), path + ".generators")
        if not generators_raw:
            raise SpecError(path + ".generators", "at least one generator is required")
        generators = {}
        for g, matrix in generators_raw.items():
            if not _NAME.match(g):
                raise SpecError(path + ".generators", "generator names must be identifiers")
            generators[g] = _matrix(ring, matrix, size, "%s.generators.%s" % (path, g))
        relators = []
        for i, text in enumerate(raw.get("relators", [])):
            relators.append((text, _word(text, generators, "%s.relators[%d]" % (path, i))))
        orders = []
        element_orders = raw.get("element_orders", {})
        if not isinstance(element_orders, dict):
            raise SpecError(path + ".element_orders", "expected a table from words to orders")
        for text, order in element_orders.items():
            word_path = "%s.element_orders[%r]" % (path, text)
            orders.append((text, _word(text, generators, word_path), parse_integer(order, word_path, minimum=1)))
        group = MatrixGroupDecl(name, field_name, size, generators, relators, orders)
        if "order" in raw:
            group.order = parse_integer(raw["order"], path + ".order", minimum=1)
        spec.matrix_groups[name] = group


def _word(text, generators, path):
    if not isinstance(text, str):
        raise SpecError(path, "expected a word string")
    try:
        return parse_word(text, generators)
    except WordError as error:
        raise SpecError(path, str(error))


def _linear_combination(ring, raw, variables, path):
    raw = _require_dict(raw, path)
    terms = []
    for index, coefficient in raw.items():
        i = parse_integer(index, "%s[%r]" % (path, index), minimum=0)
        if i >= variables:
            raise SpecError(path, "variable index %d is out of range" % i)
        terms.append((i, _element(ring, coefficient, "%s[%r]" % (path, index))))
    return sorted(terms)


def _parse_constraint_systems(data, spec):
    allowed = {"field", "variables", "constraints", "witness"}
    for name, raw in _table(data, "constraint_systems", "").items():
        path = "constraint_systems.%s" % name
        raw = _require_dict(raw, path)
        _known(raw, allowed, path)
        field_name, ring = _field_ref(raw, path, spec)
        variables = parse_integer(raw.get("variables"), path + ".variables", minimum=1)
        constraints_raw = raw.get("constraints")
        if not isinstance(constraints_raw, list):
            raise SpecError(path + ".constraints", "expected a list of constraints")
        constraints = []
        for i, constraint in enumerate(constraints_raw):
            cpath = "%s.constraints[%d]" % (path, i)
            constraint = _require_dict(constraint, cpath)
            _known(constraint, {"a", "b", "c"}, cpath)
            constraints.append(
                tuple(_linear_combination(ring, constraint.get(k, {}), variables, "%s.%s" % (cpath, k)) for k in "abc")
            )
        system = ConstraintSystemDecl(name, field_name, variables, constraints)
        if "witness" in raw:
            witness = raw["witness"]
            if not isinstance(witness, list) or len(witness) != variables:
                raise SpecError(path + ".witness", "expected a list of %d values" % variables)
            system.witness = [_element(ring, v, "%s.witness[%d]" % (path, i)) for i, v in enumerate(witness)]
        spec.constraint_systems[name] = system


def parse_specification(data, sha256="", default_name="specification"):
    if not isinstance(data, dict):
        raise SpecError("specification", "expected a table at the top level")
    _known(data, {"locryp", "name", "fields", "curves", "matrix_groups", "constraint_systems", "assumptions"}, "specification")
    version = data.get("locryp")
    if version != SPEC_VERSION:
        raise SpecError("locryp", "expected specification version %d, found %r" % (SPEC_VERSION, version))
    name = data.get("name", default_name)
    if not isinstance(name, str) or not name:
        raise SpecError("name", "expected a nonempty string")
    spec = Specification(name, sha256)
    _parse_fields(data, spec)
    _parse_curves(data, spec)
    _parse_matrix_groups(data, spec)
    _parse_constraint_systems(data, spec)
    assumptions = data.get("assumptions", [])
    if not isinstance(assumptions, list) or not all(isinstance(a, str) for a in assumptions):
        raise SpecError("assumptions", "expected a list of CHECK:subject strings")
    spec.assumptions = set(assumptions)
    return spec


def load_specification(path):
    path = Path(path)
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    try:
        if path.suffix == ".toml":
            data = tomllib.loads(raw.decode("utf-8"))
        elif path.suffix == ".json":
            data = json.loads(raw.decode("utf-8"))
        else:
            raise SpecError(str(path), "specification must be a .json or .toml file")
    except (json.JSONDecodeError, tomllib.TOMLDecodeError, UnicodeDecodeError) as error:
        raise SpecError(str(path), "could not parse: %s" % error)
    return parse_specification(data, digest, path.stem)
