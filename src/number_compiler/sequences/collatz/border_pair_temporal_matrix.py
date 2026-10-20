"""Source-guarded 100x100 Collatz decimal-pair and F5 temporal matrices.

A Boolean pair relation without its upper inlet is *not* a deterministic
Collatz successor.  Local even and odd-half matrices are parameterized by the
upper parity; a whole border macro is represented by its exact affine action
and the original-source congruences on each nonzero pair entry.  Rows are
expanded only on demand (at most 100 entries, regardless of cylinder width).

The upper-numerator F5 matrix applies only to certified uninterrupted 3->3
6305 returns.  A path through an 8/9 border must not use that coordinate.
Nothing in this module grants a parity word or an unproved next-tail guard.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from math import gcd
from typing import cast

from number_compiler.arithmetic.fields.boolean_transfer import (
    BooleanMatrix,
    BooleanStateSpace,
)
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.fields.weighted_transfer import (
    WeightedTransfer,
    WeightedTransferLaw,
)
from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.source_closed_port_action import (
    MacroTraceGrammar,
    SourceClosedPortAction,
    SourceCongruence,
)

_PAIR_MODULUS = 100
_ALL_PAIRS = (1 << _PAIR_MODULUS) - 1
_COLLATZ_PAIR_STATE_SPACE = BooleanStateSpace(
    "collatz.decimal-pair-index", tuple(range(_PAIR_MODULUS))
)
_COLLATZ_PAIR_WEIGHT_LAW = WeightedTransferLaw(
    "collatz.decimal-pair-carries", ("tens-carry", "hundreds-carry")
)


@dataclass(frozen=True, slots=True, init=False)
class BooleanPairMatrix:
    """Boolean transfer owned by the Collatz decimal-pair index space."""

    _relation: BooleanMatrix[int]

    def __init__(self, rows: tuple[int, ...]) -> None:
        object.__setattr__(
            self, "_relation", BooleanMatrix(_COLLATZ_PAIR_STATE_SPACE, rows)
        )

    @classmethod
    def _from_relation(cls, relation: BooleanMatrix[int]) -> BooleanPairMatrix:
        if (
            type(relation) is not BooleanMatrix
            or relation.state_space is not _COLLATZ_PAIR_STATE_SPACE
        ):
            raise TypeError("Collatz matrix needs its decimal-pair state space")
        result = object.__new__(cls)
        object.__setattr__(result, "_relation", relation)
        return result

    @property
    def rows(self) -> tuple[int, ...]:
        return self._relation.rows

    @property
    def state_space(self) -> BooleanStateSpace[int]:
        return self._relation.state_space

    @classmethod
    def even(cls, upper_parity: int) -> BooleanPairMatrix:
        if type(upper_parity) is not int or upper_parity not in (0, 1):
            raise ValueError("even half-step upper inlet must be a parity bit")
        return cls(
            tuple(
                (1 << (pair // 2 + 50 * upper_parity)) if pair % 2 == 0 else 0
                for pair in range(100)
            )
        )

    @classmethod
    def odd_half(cls, upper_parity: int, *, inlet: int = 1) -> BooleanPairMatrix:
        """(3*x+inlet)/2; Collatz uses inlet=1 and *odd* source rows.

        The upper two-digit block H contributes (H mod 2), while carry from
        the low block contributes floor((3*C+inlet)/100) mod 2.
        """
        if type(upper_parity) is not int or upper_parity not in (0, 1):
            raise ValueError("odd half-step upper inlet must be a parity bit")
        if type(inlet) is not int or inlet not in (0, 1, 2):
            raise ValueError("decimal low-block carry inlet is outside 0..2")
        rows: list[int] = []
        for pair in range(100):
            numerator = 3 * pair + inlet
            if numerator & 1:
                rows.append(0)
                continue
            remainder = numerator % 100
            carry = numerator // 100
            result = remainder // 2 + 50 * ((upper_parity + carry) & 1)
            rows.append(1 << result)
        return cls(tuple(rows))

    def successors(self, pair: int) -> tuple[int, ...]:
        if type(pair) is not int or not 0 <= pair < 100:
            raise ValueError("decimal pair is outside 00..99")
        bits = self.rows[pair]
        return tuple(i for i in range(100) if bits >> i & 1)

    def then(self, after: BooleanPairMatrix) -> BooleanPairMatrix:
        """Unweighted Boolean product; caller still needs source guard joins."""
        if type(after) is not BooleanPairMatrix:
            raise TypeError("pair matrix multiplication requires two matrices")
        return self._from_relation(self._relation.then(after._relation))

    def power(self, count: int) -> BooleanPairMatrix:
        """Power this local relation; it does not certify inlet repetition."""
        return self._from_relation(self._relation.power(count))

    def image(self, source_bitset: int) -> int:
        """Apply this relation to a set of low-pair states."""
        return self._relation.image(source_bitset)


@dataclass(frozen=True, slots=True, init=False)
class WeightedPairMatrix:
    """100x100 local Boolean matrix with (tens,hundreds) carry weights.

    This is a semiring of *possible* weighted paths.  Entries can be summed
    and binary-powered under an independently certified repeating *upper
    inlet program*.  It is NOT itself a certificate that a given upper
    parity repeats; source guards must be joined by the caller.
    """

    _transfer: WeightedTransfer[int]

    def __init__(self, rows: tuple[tuple[tuple[int, int, int], ...], ...]) -> None:
        if type(rows) is not tuple or len(rows) != 100:
            raise ValueError("weighted decimal matrix requires 100 rows")
        for row in rows:
            if type(row) is not tuple or any(
                type(value) is not tuple
                or len(value) != 3
                or any(type(x) is not int for x in value)
                or not 0 <= value[0] < 100
                or value[1] < 0
                or value[2] < 0
                for value in row
            ):
                raise ValueError("invalid weighted decimal pair transition")
        object.__setattr__(
            self,
            "_transfer",
            WeightedTransfer(_COLLATZ_PAIR_STATE_SPACE, _COLLATZ_PAIR_WEIGHT_LAW, rows),
        )

    @property
    def rows(self) -> tuple[tuple[tuple[int, int, int], ...], ...]:
        return cast(tuple[tuple[tuple[int, int, int], ...], ...], self._transfer.rows)

    @classmethod
    def _from_transfer(cls, transfer: WeightedTransfer[int]) -> WeightedPairMatrix:
        if (
            type(transfer) is not WeightedTransfer
            or transfer.state_space is not _COLLATZ_PAIR_STATE_SPACE
            or transfer.law is not _COLLATZ_PAIR_WEIGHT_LAW
        ):
            raise TypeError("weighted pair result has foreign algebra authority")
        result = object.__new__(cls)
        object.__setattr__(result, "_transfer", transfer)
        return result

    @classmethod
    def identity(cls) -> WeightedPairMatrix:
        return cls(tuple(((i, 0, 0),) for i in range(100)))

    @classmethod
    def even(cls, upper_parity: int) -> WeightedPairMatrix:
        if type(upper_parity) is not int or upper_parity not in (0, 1):
            raise ValueError("even half-step upper inlet must be a parity bit")
        return cls._even_cached(upper_parity)

    @classmethod
    @lru_cache(maxsize=4)
    def _even_cached(cls, upper_parity: int) -> WeightedPairMatrix:
        transfer = BooleanPairMatrix.even(upper_parity)
        return cls(
            tuple(
                tuple((out, 0, 0) for out in transfer.successors(pair))
                for pair in range(100)
            )
        )

    @classmethod
    def odd_half(cls, upper_parity: int, *, inlet: int = 1) -> WeightedPairMatrix:
        if type(upper_parity) is not int or upper_parity not in (0, 1):
            raise ValueError("odd half-step upper inlet must be a parity bit")
        if type(inlet) is not int or inlet not in (0, 1, 2):
            raise ValueError("decimal low-block carry inlet is outside 0..2")
        return cls._odd_half_cached(upper_parity, inlet=inlet)

    @classmethod
    @lru_cache(maxsize=12)
    def _odd_half_cached(cls, upper_parity: int, *, inlet: int) -> WeightedPairMatrix:
        transfer = BooleanPairMatrix.odd_half(upper_parity, inlet=inlet)
        return cls(
            tuple(
                tuple(
                    (out, *mul3_two_digit_carries(pair, inlet=inlet))
                    for out in transfer.successors(pair)
                )
                for pair in range(100)
            )
        )

    def successors(self, pair: int) -> tuple[tuple[int, int, int], ...]:
        if type(pair) is not int or not 0 <= pair < 100:
            raise ValueError("weighted matrix input pair must be 00..99")
        return self.rows[pair]

    def then(
        self, after: WeightedPairMatrix, *, max_row_entries: int = 512
    ) -> WeightedPairMatrix:
        if type(after) is not WeightedPairMatrix:
            raise TypeError("weighted multiplication requires matching matrices")
        return self._from_transfer(
            self._transfer.then(after._transfer, max_row_entries=max_row_entries)
        )

    def power(self, exponent: int, *, max_row_entries: int = 512) -> WeightedPairMatrix:
        matrix, _, _ = self.power_with_work(exponent, max_row_entries=max_row_entries)
        return matrix

    def power_with_work(
        self, exponent: int, *, max_row_entries: int = 512
    ) -> tuple[WeightedPairMatrix, int, int]:
        """Return the exact number of matrix products used by binary powering.

        The first count includes result multiplications and squarings; the
        second isolates squarings. These count successful ``then`` calls,
        rather than estimating from the exponent's bit length.
        """
        transfer, compositions, squarings = self._transfer.power_with_work(
            exponent, max_row_entries=max_row_entries
        )
        return self._from_transfer(transfer), compositions, squarings

    def support(self) -> BooleanPairMatrix:
        return BooleanPairMatrix(
            tuple(
                sum(1 << target for target in {entry[0] for entry in row})
                for row in self.rows
            )
        )


@dataclass(frozen=True, slots=True)
class UpperNumeratorF5Matrix:
    """Two-dimensional homogeneous matrix on (s mod 5, 1)."""

    scale: int = 1
    offset: int = 0
    returns: int = 0

    def __post_init__(self) -> None:
        if (
            type(self.scale) is not int
            or not 1 <= self.scale < 5
            or type(self.offset) is not int
            or not 0 <= self.offset < 5
            or type(self.returns) is not int
            or self.returns < 0
        ):
            raise ValueError("invalid F5 numerator phase matrix")

    @classmethod
    def tail(cls, zero_tail: int) -> UpperNumeratorF5Matrix:
        if type(zero_tail) is not int or not 0 <= zero_tail < 160:
            raise ValueError("6305 tail is outside the certified trace alphabet")
        return cls(pow(2, -zero_tail, 5), 4, 1)

    @classmethod
    def from_trace(cls, trace: MacroTraceGrammar) -> UpperNumeratorF5Matrix:
        """Fold the SLP once per unique node; do not materialize its word."""
        if type(trace) is not MacroTraceGrammar:
            raise TypeError("upper phase needs an issued return trace grammar")
        memo: dict[int, UpperNumeratorF5Matrix] = {}
        pending: list[tuple[MacroTraceGrammar, bool]] = [(trace, False)]
        while pending:
            node, ready = pending.pop()
            key = id(node)
            if key in memo:
                continue
            if node.left is None:
                result = cls()
                for tail in node.letters:
                    result = result.then(cls.tail(tail))
                memo[key] = result
            elif ready:
                assert node.right is not None
                memo[key] = memo[id(node.left)].then(memo[id(node.right)])
            else:
                assert node.right is not None
                pending.extend(((node, True), (node.right, False), (node.left, False)))
        return memo[id(trace)]

    def then(self, after: UpperNumeratorF5Matrix) -> UpperNumeratorF5Matrix:
        if type(after) is not UpperNumeratorF5Matrix:
            raise TypeError("F5 upper phase needs a matching matrix")
        return UpperNumeratorF5Matrix(
            after.scale * self.scale % 5,
            (after.scale * self.offset + after.offset) % 5,
            self.returns + after.returns,
        )

    def power(self, copies: int) -> UpperNumeratorF5Matrix:
        if type(copies) is not int or copies < 0:
            raise ValueError("upper phase power needs a natural exponent")
        return binary_power(
            self,
            copies,
            identity=UpperNumeratorF5Matrix(),
            compose=lambda first, after: first.then(after),
        ).value

    @property
    def entries(self) -> tuple[tuple[int, int], tuple[int, int]]:
        return ((self.scale, self.offset), (0, 1))

    def apply(self, value: int) -> int:
        if type(value) is not int:
            raise TypeError("F5 phase requires exact source residue")
        return (self.scale * value + self.offset) % 5


def upper_numerator_f5(source: int) -> int:
    """Numerator s=3*((x-3)/10)+1, defined only on a 3-border."""
    if type(source) is not int or source <= 0 or source % 10 != 3:
        raise ValueError("upper numerator phase requires a 3-ending source")
    return (3 * ((source - 3) // 10) + 1) % 5


def mul3_two_digit_carries(pair: int, *, inlet: int = 1) -> tuple[int, int]:
    """Exact per-position output carries of the 3*x+inlet decimal odd step.

    These are *spatial* carry arrivals at the tens and hundreds boundaries.
    They can be added along an authenticated temporal path, but never inferred
    from a naked F5 state or an unguarded pair-matrix product.
    """
    if type(pair) is not int or not 0 <= pair < 100:
        raise ValueError("decimal pair is outside 00..99")
    if type(inlet) is not int or inlet not in (0, 1, 2):
        raise ValueError("decimal carry inlet is outside 0..2")
    units, tens = pair % 10, pair // 10
    c1 = (3 * units + inlet) // 10
    c2 = (3 * tens + c1) // 10
    return c1, c2


@dataclass(frozen=True, slots=True)
class GuardedPairEntry:
    """One 100x100 nonzero, authorized by its ORIGINAL source cylinder."""

    input_pair: int
    output_pair: int
    guard: SourceCongruence
    inlet: CollatzTwoSidedCylinder
    target: CollatzTwoSidedCylinder

    @property
    def count(self) -> int:
        return self.inlet.count


@dataclass(frozen=True, slots=True)
class GuardedDecimalPairTransfer:
    """Lazy, exact 100x100 relation for a certified macro and its source.

    All entries contain the *same* original-source action guard.  Refining a
    requested output pair pulls its congruence back through the full affine
    denominator, then intersects with the source cylinder.  An arbitrary
    Boolean matrix product is not allowed to authorize a future parity word.
    """

    port: SourceClosedPortAction

    def __post_init__(self) -> None:
        if type(self.port) is not SourceClosedPortAction:
            raise TypeError("pair transfer requires a certified guarded action")
        self.port.verify_issued()

    def entry(
        self,
        source: CollatzTwoSidedCylinder,
        input_pair: int,
        output_pair: int,
    ) -> GuardedPairEntry | None:
        if type(source) is not CollatzTwoSidedCylinder:
            raise TypeError("pair entry requires an exact two-sided cylinder")
        if any(
            type(pair) is not int or not 0 <= pair < 100
            for pair in (input_pair, output_pair)
        ):
            raise ValueError("pair matrix indices must be 00..99")
        admitted = self.port.guard.meet(SourceCongruence(input_pair, 100))
        if admitted is None:
            return None
        pulled = SourceCongruence(output_pair, 100).pullback(self.port.action)
        if pulled is None:
            return None
        admitted = admitted.meet(pulled)
        if admitted is None:
            return None
        inlet = source.intersect_congruence(admitted.residue, admitted.modulus)
        if inlet is None:
            return None
        if inlet.first < admitted.minimum_source:
            inlet = inlet.intersect_interval(admitted.minimum_source, inlet.upper)
            if inlet is None:
                return None
        target = inlet.transport(self.port.action)
        if (
            target.forced_residue(100) != output_pair
            or inlet.forced_residue(100) != input_pair
        ):
            raise ArithmeticError("guarded pair matrix lost its source/end pair")
        return GuardedPairEntry(input_pair, output_pair, admitted, inlet, target)

    def pointed_entry(self, source: int) -> GuardedPairEntry:
        if not self.port.admits(source):
            raise ValueError("pointed source fails issued pair-transfer guard")
        endpoint = self.port.endpoint(source)
        singleton = CollatzTwoSidedCylinder(source, source, 0, 1)
        entry = self.entry(singleton, source % 100, endpoint % 100)
        if entry is None or entry.count != 1 or entry.target.first != endpoint:
            raise ArithmeticError("pointed decimal pair violates source certificate")
        return entry

    def row(
        self,
        source: CollatzTwoSidedCylinder,
        input_pair: int,
        *,
        max_entries: int = 100,
    ) -> tuple[GuardedPairEntry, ...]:
        """Enumerate at most 100 *nonempty* guarded output entries in a row."""
        if type(source) is not CollatzTwoSidedCylinder:
            raise TypeError("pair row needs an exact source cylinder")
        if type(input_pair) is not int or not 0 <= input_pair < 100:
            raise ValueError("input pair must be 00..99")
        if type(max_entries) is not int or not 1 <= max_entries <= 100:
            raise ValueError("pair row expansion budget must be in 1..100")
        matched = source.intersect_congruence(input_pair, 100)
        if matched is None:
            return ()
        in_port = matched.intersect_congruence(
            self.port.guard.residue, self.port.guard.modulus
        )
        if in_port is None:
            return ()
        if in_port.first < self.port.guard.minimum_source:
            in_port = in_port.intersect_interval(
                self.port.guard.minimum_source, in_port.upper
            )
            if in_port is None:
                return ()
        target = in_port.transport(self.port.action)
        period = 100 // gcd(target.modulus, 100)
        choices = min(period, target.count)
        if choices > max_entries:
            raise ValueError(
                "source pair has more alternatives than the requested budget"
            )
        entries = tuple(
            entry
            for k in range(choices)
            if (
                entry := self.entry(
                    source, input_pair, (target.first + target.modulus * k) % 100
                )
            )
            is not None
        )
        if sum(entry.count for entry in entries) != in_port.count:
            raise ArithmeticError("guarded decimal pair row lost source alternatives")
        return entries

    def support_matrix(
        self,
        source: CollatzTwoSidedCylinder,
        *,
        max_entries: int = 10000,
    ) -> BooleanPairMatrix:
        """Demand a 100x100 support matrix only when explicitly requested."""
        if type(max_entries) is not int or not 1 <= max_entries <= 10000:
            raise ValueError("pair matrix entry budget must be 1..10000")
        rows: list[int] = []
        count = 0
        conserved = 0
        for pair in range(100):
            entries = self.row(source, pair, max_entries=min(100, max_entries))
            count += len(entries)
            if count > max_entries:
                raise ValueError("guarded pair support exceeds expansion budget")
            conserved += sum(entry.count for entry in entries)
            rows.append(sum(1 << entry.output_pair for entry in entries))
        admitted = source.intersect_congruence(
            self.port.guard.residue, self.port.guard.modulus
        )
        if admitted is not None and admitted.first < self.port.guard.minimum_source:
            admitted = admitted.intersect_interval(
                self.port.guard.minimum_source, admitted.upper
            )
        expected = 0 if admitted is None else admitted.count
        if conserved != expected:
            raise ArithmeticError("guarded pair matrix fails source conservation")
        return BooleanPairMatrix(tuple(rows))

    def then(self, after: GuardedDecimalPairTransfer) -> GuardedDecimalPairTransfer:
        """Compose macro actions with guard *pullbacks*, not naked Booleans."""
        if type(after) is not GuardedDecimalPairTransfer:
            raise TypeError("guarded pair transfer requires another transfer")
        joined = self.port.then(after.port)
        if joined is None:
            raise ValueError("pair-transfer actions have incompatible source guards")
        return GuardedDecimalPairTransfer(joined)


__all__ = [
    "BooleanPairMatrix",
    "GuardedDecimalPairTransfer",
    "GuardedPairEntry",
    "UpperNumeratorF5Matrix",
    "WeightedPairMatrix",
    "mul3_two_digit_carries",
    "upper_numerator_f5",
]


@dataclass(frozen=True, slots=True)
class PointedLowBorderCertificate:
    """A demanded, guarded 100x100 entry and optional 3-border F5 phase."""

    pair: GuardedPairEntry
    phase: UpperNumeratorF5Matrix | None


def validate_pointed_pair_action(
    pair: GuardedPairEntry,
    source: int,
    action: DyadicTerminalFieldAction,
) -> int:
    """Authenticate a previously built pair row against its exact action.

    This lets the source/carry join consume the same point row instead of
    reconstructing it through a second puncture evaluation.
    """
    if (
        type(pair) is not GuardedPairEntry
        or type(pair.input_pair) is not int
        or not 0 <= pair.input_pair < _PAIR_MODULUS
        or type(pair.output_pair) is not int
        or not 0 <= pair.output_pair < _PAIR_MODULUS
        or type(pair.guard) is not SourceCongruence
        or type(pair.inlet) is not CollatzTwoSidedCylinder
        or type(pair.target) is not CollatzTwoSidedCylinder
        or type(source) is not int
        or source <= 0
        or type(action) is not DyadicTerminalFieldAction
        or not action.producer_issued
        or not action.certifies(source)
    ):
        raise ValueError("pointed pair/action authentication has invalid authority")
    endpoint = action.endpoint(source)
    source_guard = SourceCongruence(action.source_residue, action.source_modulus).meet(
        SourceCongruence(source % 10, 10)
    )
    input_guard = (
        None
        if source_guard is None
        else source_guard.meet(SourceCongruence(source % 100, 100))
    )
    output_guard = SourceCongruence(endpoint % 100, 100).pullback(action)
    expected_guard = (
        None
        if input_guard is None or output_guard is None
        else input_guard.meet(output_guard)
    )
    if (
        expected_guard is None
        or pair.guard != expected_guard
        or pair.input_pair != source % 100
        or pair.output_pair != endpoint % 100
        or pair.inlet.count != 1
        or pair.inlet.first != source
        or pair.inlet.last != source
        or not pair.inlet.contains(source)
        or pair.target.count != 1
        or pair.target.first != endpoint
        or pair.target.last != endpoint
        or not pair.target.contains(endpoint)
        or pair.count != 1
    ):
        raise ArithmeticError("pointed pair row belongs to another source/action")
    return endpoint


def certify_pointed_low_border(
    source: int,
    endpoint: int,
    action: object,
    odd_events: int,
    *,
    tails: tuple[int, ...] = (),
) -> PointedLowBorderCertificate:
    """Attach matrix checks to an *already issued* named or 6305 macro.

    Does not select an action, scan future digits or expand a dense matrix.
    Only a continuous 3->3 return tape has an upper-numerator phase matrix.
    """
    from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
        DyadicTerminalFieldAction,
    )

    if (
        type(action) is not DyadicTerminalFieldAction
        or not action.producer_issued
        or type(source) is not int
        or source <= 0
        or type(endpoint) is not int
        or endpoint <= 0
        or type(odd_events) is not int
        or odd_events < 0
        or type(tails) is not tuple
        or any(type(j) is not int or not 0 <= j < 160 for j in tails)
    ):
        raise ValueError("pointed low border requires a producer-issued exact action")
    if not action.certifies(source) or action.endpoint(source) != endpoint:
        raise ValueError("low pair witness differs from issued parity action")
    base_guard = SourceCongruence(action.source_residue, action.source_modulus)
    guard = base_guard.meet(SourceCongruence(source % 10, 10))
    if guard is None or not guard.admits(source):
        raise ArithmeticError("decimal border admission lost source class")
    port = SourceClosedPortAction(
        action, guard, odd_events, None, MacroTraceGrammar.leaf(tails)
    )
    pair = GuardedDecimalPairTransfer(port).pointed_entry(source)
    phase: UpperNumeratorF5Matrix | None = None
    if (
        tails
        and source % 10 == 3
        and endpoint % 10 == 3
        and odd_events == 2 * len(tails)
        and action.steps == sum(j + 2 for j in tails)
    ):
        phase = UpperNumeratorF5Matrix.from_trace(MacroTraceGrammar.leaf(tails))
        if phase.apply(upper_numerator_f5(source)) != upper_numerator_f5(endpoint):
            raise ArithmeticError("border macro matrix violates upper-numerator phase")
    return PointedLowBorderCertificate(pair, phase)


@dataclass(frozen=True, slots=True)
class PointedCarryCountVector:
    """Source-certified bounded temporal count of two spatial carry wires."""

    first_wire: int
    second_wire: int
    odd_updates: int
    endpoint: int


def demanded_trace_carry_counts(
    source: int, trace: MacroTraceGrammar, *, max_returns: int = 256
) -> PointedCarryCountVector:
    """Count true 3x+1 decimal carry arrivals on a finite selected trace.

    This is intentionally a *bounded diagnostic*, not a logarithmic-time
    powered count for arbitrary guarded inputs: the two-digit count is not
    determined by the F5 phase alone.  No unfounded temporal periodicity is
    assumed; over-budget requests explicitly refuse rather than approximate.
    """
    if type(trace) is not MacroTraceGrammar or type(source) is not int or source <= 0:
        raise ValueError("carry counts need a positive pointed source and exact trace")
    if type(max_returns) is not int or not 0 <= max_returns <= 4096:
        raise ValueError("carry count budget is outside 0..4096")
    tails = trace.materialize(max_labels=max_returns)
    x = source
    c1 = c2 = 0
    for j in tails:
        if x % 10 != 3:
            raise ValueError("count trace exits the 3-border before its next return")
        a, b = mul3_two_digit_carries(x % 100)
        c1 += a
        c2 += b
        after_first = (3 * x + 1) // 2
        if after_first % (1 << j):
            raise ValueError("count trace has a nonadmitted zero-tail valuation")
        next_odd = after_first >> j
        if not (next_odd & 1):
            raise ValueError("count trace tries a second odd action on an even source")
        a, b = mul3_two_digit_carries(next_odd % 100)
        c1 += a
        c2 += b
        x = (3 * next_odd + 1) // 2
    return PointedCarryCountVector(c1, c2, 2 * len(tails), x)


__all__ += [
    "PointedCarryCountVector",
    "PointedLowBorderCertificate",
    "certify_pointed_low_border",
    "demanded_trace_carry_counts",
    "validate_pointed_pair_action",
]
