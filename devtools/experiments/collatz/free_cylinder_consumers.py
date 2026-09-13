"""Guard and publisher records for the source-bound cylinder experiment."""

from __future__ import annotations

from dataclasses import dataclass

from devtools.experiments.collatz.physical_support import PhysicalSupport
from number_compiler.sequences.collatz.hensel_cylinders import (
    HenselAffineBlock,
    HenselCylinder,
)


@dataclass(frozen=True, slots=True)
class FreeCylinderResidualID:
    """Arena-local identity of one canonical free residual function."""

    owner: object
    index: int


@dataclass(frozen=True, slots=True)
class BoundCylinderEndpoint:
    """A bound seam after all source-cylinder predicates were consumed."""

    target: int
    accelerated_events: int
    physical_ticks: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (self.target, self.accelerated_events, self.physical_ticks)
        ):
            raise TypeError("bound Collatz endpoint fields require exact integers")
        if self.target <= 0:
            raise ValueError("bound Collatz endpoint must be positive")
        if self.accelerated_events < 0 or self.physical_ticks < 0:
            raise ValueError(self)


@dataclass(frozen=True, slots=True)
class BoundCylinderAction:
    """Selected whole-block transport after its source predicate is consumed."""

    constant_target: int | None
    transport: HenselAffineBlock | None
    accelerated_events: int
    physical_ticks: int
    support: PhysicalSupport

    def __post_init__(self) -> None:
        self.support.owner.validate(self.support)
        if (self.physical_ticks, self.accelerated_events) != (
            self.support.ticks,
            self.support.odd_ticks,
        ):
            raise ValueError("bound clock disagrees with its support program")
        if (self.constant_target is None) == (self.transport is None):
            raise ValueError("bound action requires one output representation")
        if self.constant_target is not None and self.constant_target <= 0:
            raise ValueError("constant Collatz endpoint must be positive")
        if self.transport is not None:
            if type(self.transport) is not HenselAffineBlock:
                raise TypeError("bound cylinder transport has the wrong type")
            if self.accelerated_events != self.transport.steps:
                raise ValueError("bound action event count disagrees with transport")
            if self.physical_ticks != self.transport.steps + self.transport.divisions:
                raise ValueError(
                    "bound action physical weight disagrees with transport"
                )

    def apply_exact(self, source: int) -> int:
        if self.constant_target is not None:
            return self.constant_target
        if self.transport is None:
            raise AssertionError("bound action has no output representation")
        return int(self.transport.apply_exact(source))


@dataclass(frozen=True, slots=True)
class _ConsumerOutput:
    """Output after a bounded source guard has been consumed."""

    constant_target: int | None = None
    transport: HenselAffineBlock | None = None

    def __post_init__(self) -> None:
        if (self.constant_target is None) == (self.transport is None):
            raise ValueError("consumer output requires one representation")


@dataclass(frozen=True, slots=True)
class _ConsumerAction:
    """The publisher retains ordered support after consuming its source guard."""

    output: _ConsumerOutput
    support: PhysicalSupport

    @property
    def event_weight(self) -> int:
        return self.support.odd_ticks

    @property
    def physical_ticks(self) -> int:
        return self.support.ticks


@dataclass(frozen=True, slots=True)
class _CylinderBranch:
    domain: HenselCylinder
    action: _ConsumerAction


@dataclass(frozen=True, slots=True)
class _FreeCylinderResidual:
    accelerated_events: int | None
    physical_ticks: int | None
    max_source_bits: int
    predicate_bits: int
    decision_root: int
    branches: tuple[_CylinderBranch, ...]


@dataclass(frozen=True, slots=True)
class _GuardTrieNode:
    """One hash-consed low-to-high cylinder-prefix decision."""

    terminal: _ConsumerAction | None
    zero: int | None
    one: int | None


def _bounded_cylinder_nonempty(cylinder: HenselCylinder, bits: int) -> bool:
    """Whether ``C(q,r)`` contains a positive integer below ``2**bits``."""
    limit = 1 << bits
    first_positive = cylinder.residue or 1 << cylinder.bits
    return bool(first_positive < limit)


def _branch_key(branch: _CylinderBranch) -> tuple[int, ...]:
    domain, action = branch.domain, branch.action
    transport = action.output.transport
    return (
        domain.bits,
        domain.residue,
        action.event_weight,
        action.physical_ticks,
        action.support.node_id,
        -1 if action.output.constant_target is None else action.output.constant_target,
        -1 if transport is None else transport.steps,
        -1 if transport is None else transport.divisions,
        -1 if transport is None else transport.offset,
    )


def _consume_guard(branch: _CylinderBranch, source_bits: int) -> _ConsumerAction:
    """Consume a bounded guard into its extensional output and separate weight."""
    domain, action = branch.domain, branch.action
    transport = action.output.transport
    if transport is None:
        return action
    modulus = 1 << domain.bits
    first = domain.residue or modulus
    if first + modulus >= 1 << source_bits:
        numerator = 3**transport.steps * first + transport.offset
        denominator = 1 << transport.divisions
        if numerator % denominator:
            raise AssertionError("singleton guard lost affine integrality")
        output = _ConsumerOutput(constant_target=numerator // denominator)
    else:
        output = _ConsumerOutput(transport=transport)
    return _ConsumerAction(output, action.support)


def _constant_target(action: _ConsumerAction) -> int:
    target = action.output.constant_target
    if target is None:
        raise AssertionError("consumer output is not constant")
    return target


def _coalesce_sibling_guards(
    branches: list[_CylinderBranch],
) -> tuple[_CylinderBranch, ...]:
    """Merge equal consumer leaves across complete sibling cylinders."""
    by_guard: dict[tuple[int, int], _ConsumerAction] = {}
    for branch in branches:
        key = branch.domain.bits, branch.domain.residue
        found = by_guard.get(key)
        if found is not None and found != branch.action:
            raise AssertionError("one cylinder has conflicting consumers")
        by_guard[key] = branch.action
    maximum = max((bits for bits, _residue in by_guard), default=0)
    for bits in range(maximum, 0, -1):
        high_bit = 1 << (bits - 1)
        lows = sorted(
            residue
            for guard_bits, residue in by_guard
            if guard_bits == bits and not residue & high_bit
        )
        for residue in lows:
            left_key = bits, residue
            right_key = bits, residue | high_bit
            left = by_guard.get(left_key)
            right = by_guard.get(right_key)
            if left is None or left != right:
                continue
            del by_guard[left_key]
            del by_guard[right_key]
            parent_key = bits - 1, residue
            parent = by_guard.get(parent_key)
            if parent is not None and parent != left:
                raise AssertionError("coalesced cylinder conflicts with its parent")
            by_guard[parent_key] = left
    return tuple(
        _CylinderBranch(HenselCylinder(bits, residue), action)
        for (bits, residue), action in by_guard.items()
    )
