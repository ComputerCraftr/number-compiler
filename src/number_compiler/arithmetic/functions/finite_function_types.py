"""Source-free, extensional finite functions with canonical higher terminals.

Ordered decisions inspect primitive port bits. Product terminals contain only
canonical constant components; function terminals contain already canonical
functions. No source cells, coordinates of output words, or execution callbacks
enter this arena. Reduced DAG size can still be exponential in the interface.
"""

from __future__ import annotations

from number_compiler.arithmetic.contracts.iterative_queries import finish_postorder

from dataclasses import dataclass, field
from typing import Literal, TypeAlias

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.arithmetic.functions.finite_port_action import PortVariable


@dataclass(frozen=True, slots=True)
class SemanticFunctionID(ArenaHandle):
    """One canonical function in one arena lifetime."""


@dataclass(frozen=True, slots=True)
class FinitePort:
    variable: PortVariable
    cardinality: int

    def __post_init__(self) -> None:
        _ports((self,))

    @property
    def bits(self) -> int:
        return (self.cardinality - 1).bit_length()


@dataclass(frozen=True, slots=True)
class AtomSort:
    name: str
    cardinality: int

    def __post_init__(self) -> None:
        _sort(self)


@dataclass(frozen=True, slots=True, eq=False)
class ProductSort:
    items: tuple[SemanticSort, ...]

    def __post_init__(self) -> None:
        _sort(self)

    def __hash__(self) -> int:
        return _sort_hash(self)

    def __eq__(self, other: object) -> bool:
        return type(other) is ProductSort and _sort_equal(self, other)


@dataclass(frozen=True, slots=True, eq=False)
class FunctionSort:
    inputs: tuple[FinitePort, ...]
    output: SemanticSort

    def __post_init__(self) -> None:
        _sort(self)

    def __hash__(self) -> int:
        return _sort_hash(self)

    def __eq__(self, other: object) -> bool:
        return type(other) is FunctionSort and _sort_equal(self, other)


SemanticSort: TypeAlias = AtomSort | ProductSort | FunctionSort


@dataclass(frozen=True, slots=True)
class FunctionSignature:
    inputs: tuple[FinitePort, ...]
    output: SemanticSort
    _hash: int = field(init=False, compare=False, repr=False)

    def __post_init__(self) -> None:
        _ports(self.inputs)
        output_hash = _sort_hash(self.output)
        object.__setattr__(self, "_hash", hash((self.inputs, output_hash)))

    def __hash__(self) -> int:
        # Many decision nodes share this immutable declaration. Equality still
        # compares the complete port/sort structure; this is not a semantic ID.
        return self._hash


def _ports(ports: tuple[FinitePort, ...]) -> None:
    if type(ports) is not tuple:
        raise TypeError("finite inputs must be an immutable tuple")
    previous: PortVariable | None = None
    for port in ports:
        if type(port) is not FinitePort or type(port.variable) is not PortVariable:
            raise TypeError("finite inputs require typed ports")
        PortVariable.__post_init__(port.variable)
        if (
            port.variable.bit != 0
            or type(port.cardinality) is not int
            or not 1 <= port.cardinality <= 1 << 64
        ):
            raise ValueError(
                "finite port needs a base variable and cardinality in 1..2**64"
            )
        if previous is not None and not previous < port.variable:
            raise ValueError("finite ports must be unique and ordered")
        previous = port.variable


def _sort(sort: SemanticSort) -> None:
    pending = [(sort, False)]
    active: set[int] = set()
    finished: set[int] = set()
    while pending:
        item, ready = pending.pop()
        identity = id(item)
        if ready:
            finish_postorder(active, finished, identity)
            continue
        if identity in finished:
            continue
        if identity in active:
            raise ValueError("cyclic finite semantic sort")
        active.add(identity)
        pending.append((item, True))
        if type(item) is AtomSort:
            if (
                type(item.name) is not str
                or not item.name
                or type(item.cardinality) is not int
                or not 1 <= item.cardinality <= 1 << 64
            ):
                raise ValueError("invalid bounded semantic atom sort")
        elif type(item) is ProductSort:
            if type(item.items) is not tuple or not item.items:
                raise ValueError("product sorts require immutable nonempty components")
            pending.extend((child, False) for child in item.items)
        elif type(item) is FunctionSort:
            _ports(item.inputs)
            pending.append((item.output, False))
        else:
            raise TypeError("unknown finite semantic sort")


def _sort_hash(sort: SemanticSort) -> int:
    """Validate and hash an immutable sort DAG in one iterative traversal."""
    pending = [(sort, False)]
    active: set[int] = set()
    hashes: dict[int, int] = {}
    while pending:
        item, ready = pending.pop()
        identity = id(item)
        if identity in hashes:
            continue
        if ready:
            active.remove(identity)
            if type(item) is ProductSort:
                hashes[identity] = hash(
                    ("product", tuple(hashes[id(child)] for child in item.items))
                )
            elif type(item) is FunctionSort:
                hashes[identity] = hash(
                    ("function", item.inputs, hashes[id(item.output)])
                )
            else:
                raise AssertionError("validated semantic sort has unknown type")
            continue
        if identity in active:
            raise ValueError("cyclic finite semantic sort")
        active.add(identity)
        if type(item) is AtomSort:
            if (
                type(item.name) is not str
                or not item.name
                or type(item.cardinality) is not int
                or not 1 <= item.cardinality <= 1 << 64
            ):
                raise ValueError("invalid bounded semantic atom sort")
            hashes[identity] = hash(("atom", item.name, item.cardinality))
            active.remove(identity)
        elif type(item) is ProductSort:
            if type(item.items) is not tuple or not item.items:
                raise ValueError("product sorts require immutable nonempty components")
            pending.append((item, True))
            pending.extend((child, False) for child in item.items)
        elif type(item) is FunctionSort:
            _ports(item.inputs)
            pending.extend(((item, True), (item.output, False)))
        else:
            raise TypeError("unknown finite semantic sort")
    return hashes[id(sort)]


def _sort_equal(left: SemanticSort, right: SemanticSort) -> bool:
    """Exact structural equality; a matching hash never substitutes for it."""
    _sort(left)
    _sort(right)
    pending = [(left, right)]
    visited: set[tuple[int, int]] = set()
    while pending:
        first, second = pending.pop()
        key = id(first), id(second)
        if key in visited or first is second:
            continue
        visited.add(key)
        if type(first) is AtomSort and type(second) is AtomSort:
            if first.name != second.name or first.cardinality != second.cardinality:
                return False
        elif type(first) is ProductSort and type(second) is ProductSort:
            if len(first.items) != len(second.items):
                return False
            pending.extend(zip(first.items, second.items))
        elif type(first) is FunctionSort and type(second) is FunctionSort:
            if first.inputs != second.inputs:
                return False
            pending.append((first.output, second.output))
        else:
            return False
    return True


def _signature(signature: FunctionSignature) -> None:
    if type(signature) is not FunctionSignature:
        raise TypeError("functions require an explicit semantic signature")
    _ports(signature.inputs)
    output_hash = _sort_hash(signature.output)
    if type(signature._hash) is not int or signature._hash != hash(
        (signature.inputs, output_hash)
    ):
        raise ValueError("semantic signature has a forged or stale cached hash")


@dataclass(frozen=True, slots=True)
class SemanticTerminal:
    kind: Literal["invalid", "atom", "product", "function"]
    value: int = 0
    references: tuple[int, ...] = ()


@dataclass(frozen=True, slots=True)
class SemanticNode:
    signature: FunctionSignature
    variable: PortVariable | None = None
    low: int = -1
    high: int = -1
    terminal: SemanticTerminal | None = None
    # Derived dependency metadata is independently audited. Canonical identity
    # is the typed terminal or (variable, low ID, high ID), never the work of
    # reconstructing this set before a duplicate lookup.
    support: tuple[PortVariable, ...] = field(default=(), compare=False, hash=False)


@dataclass(frozen=True, slots=True)
class SemanticRequest:
    operation: str
    roots: tuple[SemanticFunctionID, ...]
    ports: tuple[FinitePort, ...] = ()


BOOL = AtomSort("boolean", 2)
MAX_PRIMITIVE_ATOMS = 1024


def _union_inputs(*groups: tuple[FinitePort, ...]) -> tuple[FinitePort, ...]:
    found: dict[PortVariable, FinitePort] = {}
    for group in groups:
        for port in group:
            old = found.get(port.variable)
            if old is not None and old != port:
                raise ValueError("one variable has incompatible finite domains")
            found[port.variable] = port
    return tuple(found[key] for key in sorted(found))


def _base(variable: PortVariable) -> PortVariable:
    return PortVariable(variable.time, variable.side, variable.role, 0)
