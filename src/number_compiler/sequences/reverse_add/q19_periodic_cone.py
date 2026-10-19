"""Exact mixed LT/EQ/GT periodic-to-uniform temporal cone certificates.

This is an all-growth-choices *interior* port action, not a whole-integer
macro. A non-EQ reset in every input spatial period localizes both reflected
carry ingresses. If the TWO possible growth outputs agree, and the complete
output period is a uniform, even, non-EQ coefficient, the future is governed
by the ten-state uniform Moore controller for any admissible growth history.

The spatial admission is proved by a mismatch-detecting DFA fold over the
source's Q19 CONCAT/REPEAT DAG. It never trusts a substring from a corpus,
or treats matching output residues as matching decimal pair coefficients.
"""

from __future__ import annotations

from collections.abc import Generator
from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.slp import SLPNode
from number_compiler.arithmetic.automata.slp_interval import (
    fold_slp_dag,
    fold_slp_interval,
)
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.sequences.reverse_add.q19_conditional_stencil import (
    next_quiet_joint_xor_response,
)
from number_compiler.sequences.reverse_add.q19_uniform_cone import (
    UniformConeNotAuthorized,
    _bulk_at,
)

_UNIFORMIZING_CONE_SEAL = object()

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairOutputOccurrence,
        ReversePairQ19OutputOwner,
    )


def _bit(s: int, c: int) -> int:
    return int(s > 9 or (s == 9 and c == 1))


def _digit(s: int, c: int) -> int:
    return s + c - 10 * _bit(s, c)


def _periodic_ingresses(period: tuple[int, ...]) -> tuple[tuple[int, int], ...]:
    first = next((i for i, s in enumerate(period) if s != 9), None)
    if first is None:
        raise UniformConeNotAuthorized("all-EQ core requires exterior carry ports")
    last = next(i for i in range(len(period) - 1, -1, -1) if period[i] != 9)
    left = [0] * len(period)
    right = [0] * len(period)
    c = int(period[last] > 9)
    for i, s in enumerate(period):
        left[i] = c
        if s != 9:
            c = int(s > 9)
    c = int(period[first] > 9)
    for i in range(len(period) - 1, -1, -1):
        right[i] = c
        if period[i] != 9:
            c = int(period[i] > 9)
    return tuple(zip(left, right, strict=True))


def _step(period: tuple[int, ...], growth: int) -> tuple[int, ...]:
    ports = _periodic_ingresses(period)
    result: list[int] = []
    for i, s in enumerate(period):
        low, reflected = ports[i]
        first = _digit(s, low)
        second = (
            _digit(period[(i - 1) % len(period)], _bit(s, reflected))
            if growth
            else _digit(s, reflected)
        )
        target = first + second
        if not 0 <= target <= 18:
            raise AssertionError("mixed periodic carry action escaped Q19")
        result.append(target)
    return tuple(result)


@dataclass(frozen=True, slots=True)
class _Match:
    """Full, non-hashing DFA action for every possible periodic input phase."""

    length: int
    accepts: tuple[bool, ...]

    @staticmethod
    def identity(period: int) -> _Match:
        return _Match(0, (True,) * period)

    def then(self, other: _Match) -> _Match:
        if len(self.accepts) != len(other.accepts):
            raise ValueError("periodic match DFA has incompatible periods")
        size = len(self.accepts)
        return _Match(
            self.length + other.length,
            tuple(
                self.accepts[i] and other.accepts[(i + self.length) % size]
                for i in range(size)
            ),
        )

    def repeat(self, count: int) -> _Match:
        if type(count) is not int or count < 0:
            raise ValueError("periodic spatial repeat must be nonnegative")
        return binary_power(
            self,
            count,
            identity=self.identity(len(self.accepts)),
            compose=lambda first, second: first.then(second),
        ).value


@contextmanager
def _fold_match(
    owner: ReversePairQ19OutputOwner,
    root: int,
    pattern: tuple[int, ...],
) -> Generator[dict[int, _Match], None, None]:
    """Memoize all Q19 SLP nodes under exact periodic *output* matching."""
    node_bound = len(owner.arena.nodes)
    with owner.ledger.reservation(
        owner._scratch_owner,
        entries=4 * (node_bound + 1),
        nodes=8 * (node_bound + 1),
    ):
        visits = operand_bits = 0
        identity = _Match.identity(len(pattern))
        cache: dict[int, _Match] = {}

        def count_pending(node: SLPNode) -> None:
            nonlocal visits, operand_bits
            visits += 1
            operand_bits += node.length.bit_length()

        def terminal_summary(symbol: int) -> _Match:
            if 0 <= symbol <= 18:
                return _Match(
                    1,
                    tuple(symbol == pattern[i] for i in range(len(pattern))),
                )
            if symbol in (19, 20, 21):
                return identity
            raise ValueError("unknown Q19 word terminal")

        try:
            cache = fold_slp_dag(
                owner.arena,
                root,
                empty_value=identity,
                terminal_value=terminal_summary,
                concatenate=lambda left, right: left.then(right),
                repeat=lambda child, count: child.repeat(count),
                on_pending=count_pending,
            )
            owner.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_PERIODIC_GUARD_SLP_NODE_VISITS, visits
            )
            owner.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_PERIODIC_GUARD_OPERAND_BITS,
                operand_bits,
            )
            yield cache
        finally:
            cache.clear()


def _match_region(
    owner: ReversePairQ19OutputOwner,
    root: int,
    lo: int,
    hi: int,
    pattern: tuple[int, ...],
) -> bool:
    if lo == hi:
        return True
    with _fold_match(owner, root, pattern) as cache:
        if not 0 <= lo < hi <= cache[root].length:
            raise ValueError("periodic region exceeds encoded pair SLP")
        report = fold_slp_interval(
            owner.arena,
            root,
            lo,
            hi,
            identity=_Match.identity(len(pattern)),
            length=lambda node_id: cache[node_id].length,
            full_value=lambda node_id, _reverse: cache[node_id],
            compose=lambda left, right: left.then(right),
            repeat=lambda summary, count: summary.repeat(count),
            on_visit=lambda: owner.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_PERIODIC_GUARD_REGION_VISITS
            ),
        )
    return report.accepts[lo % len(pattern)]


def _periodic_guard(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    lo: int,
    hi: int,
    pattern: tuple[int, ...],
) -> bool:
    w = source.pair_width
    half = (w + 1) // 2
    if lo < half and not _match_region(owner, source.root, lo, min(hi, half), pattern):
        return False
    if hi > half:
        mirror = tuple(pattern[(w - 1 - j) % len(pattern)] for j in range(len(pattern)))
        return _match_region(owner, source.root, w - hi, w - max(half, lo), mirror)
    return True


@dataclass(frozen=True, slots=True)
class CertifiedUniformizingCone:
    """Mixed LT/GT input whose two growth branches enter one uniform orbit."""

    source: ReversePairOutputOccurrence
    owner: ReversePairQ19OutputOwner
    coordinate: int
    steps: int
    period: tuple[int, ...]
    uniform_successor: int
    halo: int
    _seal: object = field(init=False, repr=False, compare=False)
    _binding: tuple[object, ...] = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        if getattr(self, "_seal", None) is not _UNIFORMIZING_CONE_SEAL:
            raise ValueError("uniformizing cone records are issued by a Q19 owner")

    @classmethod
    def _issue(
        cls,
        source: ReversePairOutputOccurrence,
        owner: ReversePairQ19OutputOwner,
        coordinate: int,
        steps: int,
        period: tuple[int, ...],
        uniform_successor: int,
        halo: int,
    ) -> CertifiedUniformizingCone:
        record = object.__new__(cls)
        values = (
            source,
            owner,
            coordinate,
            steps,
            period,
            uniform_successor,
            halo,
        )
        for name, value in zip(
            (
                "source",
                "owner",
                "coordinate",
                "steps",
                "period",
                "uniform_successor",
                "halo",
            ),
            values,
            strict=True,
        ):
            object.__setattr__(record, name, value)
        object.__setattr__(record, "_binding", values)
        object.__setattr__(record, "_seal", _UNIFORMIZING_CONE_SEAL)
        return record

    def _validate(self) -> None:
        from number_compiler.sequences.reverse_add.q19_output import (
            ReversePairQ19OutputOwner,
        )

        if self._seal is not _UNIFORMIZING_CONE_SEAL or self._binding != (
            self.source,
            self.owner,
            self.coordinate,
            self.steps,
            self.period,
            self.uniform_successor,
            self.halo,
        ):
            raise ValueError("mixed cell observation was altered or not issued")
        if type(self.owner) is not ReversePairQ19OutputOwner:
            raise TypeError("mixed cell observation requires its Q19 owner")
        self.owner.validate_issued_occurrence(self.source)

    def at(self, depth: int) -> int:
        self._validate()
        if type(depth) is not int or not 0 <= depth <= self.steps:
            raise ValueError("query outside certified mixed temporal cone")
        return (
            self.period[self.coordinate % len(self.period)]
            if depth == 0
            else _bulk_at(
                self.uniform_successor, int(self.uniform_successor > 9), depth - 1
            )
        )

    @property
    def coefficient(self) -> int:
        return self.at(self.steps)

    @property
    def f5(self) -> int:
        return self.coefficient % 5

    def next_quiet_borrow_response(self, offset: int) -> tuple[int, int]:
        """Raw signed borrow transfer if the following reversal is nongrowth."""
        self._validate()
        if type(offset) is not int or not 0 <= offset < self.steps:
            raise ValueError("borrow gate must lie inside the mixed cone")
        if offset == 0:
            phase = self.coordinate % len(self.period)
            carry = _periodic_ingresses(self.period)[phase][0]
            emitted = _digit(self.period[phase], carry)
        else:
            old = self.at(offset)
            carry = int(old > 9)
            emitted = _digit(old, carry)
        future_carry = int(self.at(offset + 1) > 9)
        identity = (emitted == 0 and future_carry == 0) or (
            emitted == 9 and future_carry == 1
        )
        return (0, 1) if identity else (future_carry, future_carry)

    def next_quiet_joint_xor_response(self, offset: int) -> tuple[int, int]:
        return next_quiet_joint_xor_response(self, offset)

    def square(self, owner: ReversePairQ19OutputOwner) -> CertifiedUniformizingCone:
        return authorize_uniformizing_cone(
            owner,
            self.source,
            steps=self.steps * 2,
            coordinate=self.coordinate,
            period_size=len(self.period),
        )


def authorize_uniformizing_cone(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    *,
    steps: int,
    coordinate: int,
    period_size: int = 2,
) -> CertifiedUniformizingCone:
    """Authorize a true time power for a reset-driven mixed periodic *interior*.

    Requires the two possible growth inputs to collapse to the exact same
    uniform successor. No control word, output oracle or temporal occurrence
    label is accepted. The conservative halo protects every admissible border
    continuation; exterior physical integer and global moments remain unknown.
    """
    return _derive_uniformizing_cone(
        owner,
        source,
        steps=steps,
        coordinate=coordinate,
        period_size=period_size,
    )


def _derive_uniformizing_cone(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    *,
    steps: int,
    coordinate: int,
    period_size: int,
) -> CertifiedUniformizingCone:
    owner.validate(source)
    if type(steps) is not int or steps < 1:
        raise ValueError("mixed certificate needs positive temporal duration")
    if type(period_size) is not int or not 2 <= period_size <= 8:
        raise ValueError("mixed periodic source period must be 2..8")
    if type(coordinate) is not int or not 0 <= coordinate < source.pair_width:
        raise IndexError(coordinate)
    halo = (period_size + 2) * (steps + 1) + 2
    w = source.pair_width
    if coordinate - halo < 0 or coordinate + halo >= w:
        raise UniformConeNotAuthorized("insufficient protected mixed-period halo")
    anchor = coordinate - coordinate % period_size
    period = tuple(owner._pair_value_at(source, anchor + j) for j in range(period_size))
    first = _step(period, 0)
    second = _step(period, 1)
    if first != second or len(set(first)) != 1 or first[0] % 2:
        raise UniformConeNotAuthorized(
            "growth alternatives do not enter the same resetting Moore state"
        )
    if not _periodic_guard(
        owner, source, coordinate - halo, coordinate + halo + 1, period
    ):
        raise UniformConeNotAuthorized("mixed-period source SLP guard mismatch")
    owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_AUTHORIZED_MIXED_UNIFORMIZING_CELLS)
    return CertifiedUniformizingCone._issue(
        source, owner, coordinate, steps, period, first[0], halo
    )


__all__ = ["CertifiedUniformizingCone", "authorize_uniformizing_cone"]
