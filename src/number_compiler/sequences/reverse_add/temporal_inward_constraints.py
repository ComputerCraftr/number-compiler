"""Finite, two-ended reverse/add digit and carry constraint propagation.

The external width/border trace must come from an issued Q19 certificate.
This constraint engine **does not** authorize the trace or temporal REPEAT.
It intersects decimal addition, both reflected carry directions, moduli,
five-band/F5 pairs and optional *hypothetical* pair-period relationships.
It is arc consistency, not a proof that all surviving domains have a global
joint realization; in particular a consistent period is NOT an orbit theorem.

Separate from the `2rev10` relation: reverse/add has an ID carry response at
pair sum 9 and its radix-10 growth appends a real high digit 1.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from itertools import pairwise
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.carry.carry_monoid import CarryFn, apply_carry_fn
from number_compiler.arithmetic.fields.decimal_pair_partition import (
    DECIMAL_PAIR_BANDS,
    DecimalPairBand,
    decimal_pair_band_members,
)

from .outer_center_residue99 import constrain_center_from_outer_pairs
from .temporal_carry_wire import MiddleCarryWire, restrict_middle_carry_wire

if TYPE_CHECKING:
    from .border_carry_safety import ConditionalBorderCycle

_FULL = (1 << 10) - 1
_NONZERO = _FULL ^ 1


def _members(mask: int) -> tuple[int, ...]:
    return tuple(i for i in range(10) if mask & (1 << i))


def _bits(mask: int) -> tuple[int, ...]:
    return tuple(i for i in (0, 1) if mask & (1 << i))


class InconsistentReverseConstraints(ValueError):
    """The input safety restrictions have no arc-consistent completion."""


@dataclass(frozen=True, slots=True)
class ReverseInwardSummary:
    widths: tuple[int, ...]
    rounds: int
    forced_digits: tuple[int, ...]
    forced_carries: tuple[int, ...]
    forced_borrows: tuple[int, ...]
    pair_domains: tuple[tuple[tuple[str, ...], ...], ...]
    period_hypotheses: tuple[tuple[int, int, int, str], ...]
    complete_integer_certified: bool = False
    temporal_repeat_certified: bool = False


class ReverseInwardConstraints:
    """Arc-consistent reverse/add factors across a *certified* finite width tape.

    Indices of digits are MSD first; carry boundaries are LSD first. Pair
    coordinates are from the low end, so their reflected partner is at the
    high end. Unknown digits/carries are domains, never filled from an oracle.
    """

    def __init__(
        self,
        widths: tuple[int, ...],
        *,
        max_cells: int = 16384,
        on_middle_filter_visit: Callable[[], None] | None = None,
    ) -> None:
        if (
            type(widths) is not tuple
            or not 1 <= len(widths) <= 513
            or type(max_cells) is not int
            or not 1 <= max_cells <= 16384
            or any(type(w) is not int or w < 1 for w in widths)
            or sum(widths) > max_cells
            or any(b - a not in (0, 1) for a, b in pairwise(widths))
        ):
            raise ValueError("requires finite, positive, nonshrinking width tape")
        self.widths = widths
        self._domains = [[_NONZERO] + [_FULL] * (w - 1) for w in widths]
        self._carries = [
            [1] + [3] * (w - 1) + [1 << (widths[t + 1] - w)]
            for t, w in enumerate(widths[:-1])
        ]
        self._borrows = [
            [1] + [3] * max(w, widths[t + 1]) for t, w in enumerate(widths[:-1])
        ]
        self._residues: dict[tuple[int, int], int] = {}
        self._pairs: dict[tuple[int, int], frozenset[int]] = {}
        self._middle_transfers: dict[tuple[int, int], tuple[CarryFn, ...]] = {}
        self._middle_projections: dict[tuple[int, int], MiddleCarryWire] = {}
        self._exterior_mod99: dict[int, int] = {}
        self._xor: dict[tuple[int, int], int] = {}
        self._period: list[tuple[int, int, int, str]] = []
        if on_middle_filter_visit is not None and not callable(on_middle_filter_visit):
            raise TypeError("middle-filter work counter must be callable")
        self._on_middle_filter_visit = on_middle_filter_visit
        self.rounds = 0

    def _shrink(self, domains: list[int], i: int, mask: int, label: str) -> bool:
        old = domains[i]
        new = old & mask
        if not new:
            raise InconsistentReverseConstraints(f"{label} at index {i}")
        domains[i] = new
        return new != old

    def constrain_digit(self, t: int, i: int, value: int | tuple[int, ...]) -> None:
        if not 0 <= t < len(self.widths) or not 0 <= i < self.widths[t]:
            raise IndexError((t, i))
        if type(value) not in (int, tuple):
            raise ValueError("decimal digit domain requires an integer or tuple")
        options = (value,) if type(value) is int else cast(tuple[int, ...], value)
        if not options or any(type(v) is not int or not 0 <= v <= 9 for v in options):
            raise ValueError("decimal digit domain must be nonempty")
        mask = sum(1 << v for v in set(options))
        self._shrink(self._domains[t], i, mask, f"digit row {t}")

    def constrain_prefix(self, t: int, digits: str) -> None:
        if not digits.isascii() or not digits.isdigit() or len(digits) > self.widths[t]:
            raise ValueError("invalid leading digits")
        for i, d in enumerate(digits):
            self.constrain_digit(t, i, int(d))

    def constrain_suffix(self, t: int, digits: str) -> None:
        if not digits.isascii() or not digits.isdigit() or len(digits) > self.widths[t]:
            raise ValueError("invalid trailing digits")
        for i, d in enumerate(digits, self.widths[t] - len(digits)):
            self.constrain_digit(t, i, int(d))

    def constrain_residue(self, t: int, modulus: int, residue: int) -> None:
        if (
            not 0 <= t < len(self.widths)
            or type(modulus) is not int
            or not 2 <= modulus <= 512
            or type(residue) is not int
        ):
            raise ValueError("invalid modular port")
        pending = [(t, modulus, residue % modulus)]
        while pending:
            row, current_modulus, value = pending.pop()
            key = row, current_modulus
            previous = self._residues.get(key)
            if previous is not None and previous != value:
                raise InconsistentReverseConstraints("modular ports disagree")
            self._residues[key] = value
            if current_modulus != 198:
                continue
            # CRT(99, 2) is exact. Carrying a second width-long mod-198
            # automaton would recheck the same 99 residues and one parity
            # bit at O(width * 198) per fixed-point round. Use the shared
            # mod-99 factor and the literal LSD parity instead.
            pending.append((row, 99, value % 99))
            low = self.widths[row] - 1
            options = tuple(
                digit for digit in self.digit_domain(row, low) if digit % 2 == value % 2
            )
            if not options:
                raise InconsistentReverseConstraints("mod198 parity contradicts LSD")
            self.constrain_digit(row, low, options)

    def constrain_pair(
        self,
        t: int,
        i: int,
        allowed: DecimalPairBand | int | tuple[DecimalPairBand | int, ...],
    ) -> None:
        if not 0 <= t < len(self.widths) or not 0 <= i < (self.widths[t] + 1) // 2:
            raise IndexError((t, i))
        inputs = allowed if type(allowed) is tuple else (allowed,)
        values: set[int] = set()
        for x in inputs:
            if type(x) is int and 0 <= x <= 18:
                values.add(x)
            elif type(x) is DecimalPairBand:
                values.update(decimal_pair_band_members(x))
            else:
                raise ValueError("invalid symmetric pair domain")
        if not values:
            raise ValueError("empty pair domain")
        key = t, i
        retained = self._pairs.get(key, frozenset(range(19))) & values
        if not retained:
            raise InconsistentReverseConstraints("incompatible pair masks")
        self._pairs[key] = frozenset(retained)

    def _restrict_pair(
        self,
        t: int,
        i: int,
        allowed: DecimalPairBand | int | tuple[DecimalPairBand | int, ...],
    ) -> bool:
        """Intersect one pair domain and report whether its mask changed."""
        previous = self._pairs.get((t, i))
        self.constrain_pair(t, i, allowed)
        return previous != self._pairs[(t, i)]

    def constrain_middle_transfer(
        self, t: int, border_digits: int, allowed: tuple[CarryFn, ...]
    ) -> None:
        """Constrain the symmetric interior between two admitted border tiles.

        Pair positions are outside-in. The factor consumes every remaining
        pair and the optional even-valued center coefficient. It is a local
        carry constraint, not a future-repeat or global-source assertion.
        """
        if (
            type(t) is not int
            or not 0 <= t < len(self.widths)
            or type(border_digits) is not int
            or border_digits < 1
            or self.widths[t] < 2 * border_digits + 1
        ):
            raise ValueError("border tile leaves no admitted symmetric middle")
        if (
            type(allowed) is not tuple
            or not allowed
            or any(type(function) is not CarryFn for function in allowed)
        ):
            raise ValueError("middle transfer requires admitted carry functions")
        key = t, border_digits
        prior = self._middle_transfers.get(key)
        retained = tuple(function for function in CarryFn if function in allowed)
        if prior is not None:
            retained = tuple(function for function in retained if function in prior)
        if not retained:
            raise InconsistentReverseConstraints("middle transfer masks disagree")
        self._middle_transfers[key] = retained

    def constrain_bilateral_port(self, t: int, port: object) -> None:
        """Install the whole authenticated K-border carry transfer as one factor.

        This is a conditional digit-domain intersection, not authorization to
        repeat the border. The Q19 issuer authenticates the port provenance.
        """
        from .border_carry_safety import BilateralCyclePort, border_carry_port

        if type(port) is not BilateralCyclePort:
            raise TypeError("bilateral border port required")
        if type(t) is not int or not 0 <= t < len(self._carries):
            raise IndexError("bilateral port outside temporal tape")
        w, k = self.widths[t], port.source.k
        if w < 2 * k + 1 or self.widths[t + 1] != w + port.growth:
            raise InconsistentReverseConstraints("border port width/growth conflict")
        self.constrain_carry(t, k, port.low_carry)
        self.constrain_middle_transfer(t, k, port.admitted_middle)
        possible_high = {
            apply_carry_fn(fn, port.low_carry) for fn in port.admitted_middle
        }
        if len(possible_high) == 1:
            self.constrain_carry(t, w - k, next(iter(possible_high)))
        leading = border_carry_port(port.source)
        if leading.forced_msd_ingress is not None:
            self.constrain_carry(t, w - 1, leading.forced_msd_ingress)

    def middle_transfer_domain(self, t: int, border_digits: int) -> tuple[CarryFn, ...]:
        """All middle maps surviving the shared two-ended fixed point."""
        return self._middle_transfers[t, border_digits]

    def middle_carry_wire(self, t: int, border_digits: int) -> MiddleCarryWire:
        """Retain the entire correlated interior Q19/F5/carry witness."""
        return self._middle_projections[t, border_digits]

    def constrain_exterior_residue99(self, t: int, residue: int) -> None:
        """Intersect an externally supplied exact ordered *exterior* residue.

        This low-level constraint is an assumption, just like constrain_digit.
        A physical publisher must derive it from certified outer digits/SLP;
        guessing it from Q19 pair sums is unsound at even width.
        """
        if (
            type(t) is not int
            or not 0 <= t < len(self.widths)
            or type(residue) is not int
            or not 0 <= residue < 99
        ):
            raise ValueError("invalid exterior residue port")
        previous = self._exterior_mod99.get(t)
        if previous is not None and previous != residue:
            raise InconsistentReverseConstraints("exterior residue seam mismatch")
        self._exterior_mod99[t] = residue

    def center_domain(self, t: int) -> tuple[int, ...]:
        """Middle 1/2-digit values, with fixed width retained by the caller."""
        w = self.widths[t]
        if w % 2:
            return self.digit_domain(t, w // 2)
        lo = w // 2
        return tuple(
            sorted(
                {
                    10 * a + b
                    for a in self.digit_domain(t, lo - 1)
                    for b in self.digit_domain(t, lo)
                    if a + b in self.pair_domain(t, lo - 1)
                }
            )
        )

    def global_residue99(self, t: int) -> int | None:
        return self._residues.get((t, 99))

    def global_residue198(self, t: int) -> int | None:
        return self._residues.get((t, 198))

    def admitted_temporal_span(self, start: int, duration: int) -> range:
        """Validate and expose a finite span of represented transitions."""
        if (
            type(start) is not int
            or type(duration) is not int
            or start < 0
            or duration < 1
            or start + duration > len(self._carries)
        ):
            raise ValueError("temporal span is outside the represented carry tape")
        return range(start, start + duration)

    def raw_borrow_domain(self, t: int, position: int) -> tuple[int, ...]:
        """Read one raw innovation-borrow domain without exposing storage."""
        if (
            type(t) is not int
            or not 0 <= t < len(self._borrows)
            or type(position) is not int
            or not 0 <= position < len(self._borrows[t])
        ):
            raise IndexError((t, position))
        return _bits(self._borrows[t][position])

    def represented_middle_constraint_keys(self, t: int) -> tuple[int, ...]:
        """List border widths with retained middle constraints at transition t."""
        if type(t) is not int or not 0 <= t < len(self.widths):
            raise IndexError(t)
        return tuple(
            sorted(
                border_digits
                for row, border_digits in self._middle_transfers
                if row == t
            )
        )

    def _middle_constraints(self) -> bool:
        """Intersect low carry, one whole symmetric reset map, high ingress.

        Individual pair domains cannot be read as independent carry choices:
        the first non-EQ coefficient selects a shared RESET0/ID/RESET1 map.
        """
        changed = False
        for (t, k), allowed in sorted(self._middle_transfers.items()):
            width = self.widths[t]
            pairs = tuple(self.pair_domain(t, i) for i in range(k, (width + 1) // 2))
            projection = self._middle_projections.get((t, k))
            if not (
                projection is not None
                and projection.source_width == width
                and projection.outer_pairs == k
                and projection.pair_domains == pairs
                and projection.transfers == allowed
            ):
                try:
                    projection = restrict_middle_carry_wire(
                        width,
                        k,
                        pairs,
                        allowed,
                        on_value_visit=self._on_middle_filter_visit,
                    )
                except ValueError as exc:
                    raise InconsistentReverseConstraints(str(exc)) from exc
            assert projection is not None
            low = self._carries[t][k]
            high = self._carries[t][width - k]
            supported = {
                (carry, fn, apply_carry_fn(fn, carry))
                for fn in projection.transfers
                for carry in _bits(low)
                if high & (1 << apply_carry_fn(fn, carry))
            }
            if not supported:
                raise InconsistentReverseConstraints(
                    "inconsistent correlated middle carry"
                )
            surviving = tuple(
                fn for fn in CarryFn if any(s[1] is fn for s in supported)
            )
            if surviving != allowed:
                self._middle_transfers[t, k] = surviving
                changed = True
                projection = restrict_middle_carry_wire(
                    width,
                    k,
                    pairs,
                    surviving,
                    on_value_visit=self._on_middle_filter_visit,
                )
            changed |= self._shrink(
                self._carries[t],
                k,
                sum(1 << v for v in {s[0] for s in supported}),
                f"coupled lower carry {t}",
            )
            changed |= self._shrink(
                self._carries[t],
                width - k,
                sum(1 << v for v in {s[2] for s in supported}),
                f"coupled upper carry {t}",
            )
            for i, values in enumerate(projection.pair_domains, start=k):
                changed |= self._restrict_pair(t, i, values)
            self._middle_projections[t, k] = projection
        return changed

    def constrain_carry(self, t: int, i: int, bit: int) -> None:
        if not 0 <= t < len(self._carries) or not 0 <= i < len(self._carries[t]):
            raise IndexError((t, i))
        if bit not in (0, 1) or type(bit) is not int:
            raise ValueError("carry port must be Boolean")
        self._shrink(self._carries[t], i, 1 << bit, f"carry row {t}")

    def constrain_reflected_xor(self, t: int, i: int, bit: int) -> None:
        if not 0 <= t < len(self._carries) or not 0 <= i < self.widths[t] // 2:
            raise IndexError((t, i))
        if type(bit) is not int or bit not in (0, 1):
            raise ValueError("XOR mask must be Boolean")
        key = t, i
        if key in self._xor and self._xor[key] != bit:
            raise InconsistentReverseConstraints("reflected XOR contradicts source")
        self._xor[key] = bit

    def constrain_macro_cycle(
        self, cycle: ConditionalBorderCycle, *, start: int = 0
    ) -> None:
        """Intersect a *finite* reverse/add border macro at every phase.

        A complete border phase forces both physical end digits, the lower
        carry born there, and any required MSD ingress.  EQ/GT/LT/F5 and
        signed borrow relations then propagate through the same time system.
        This never asserts that the macro repeats after its last phase.
        """
        from .border_carry_safety import ConditionalBorderCycle

        if type(cycle) is not ConditionalBorderCycle or type(start) is not int:
            raise ValueError("source-derived conditional border cycle required")
        if start < 0 or start + cycle.steps >= len(self.widths):
            raise ValueError("macro exceeds the finite certified width tape")
        for j, (pair, growth, port) in enumerate(
            zip(cycle.states, cycle.growth, cycle.incoming, strict=True)
        ):
            t = start + j
            w = self.widths[t]
            if w < 3 or self.widths[t + 1] != w + growth:
                raise InconsistentReverseConstraints("macro width/growth seam")
            a, b = pair
            self.constrain_digit(t, 0, a)
            self.constrain_digit(t, w - 1, b)
            # Physical LSD-first carry born at the bottom pair.
            self.constrain_carry(t, 1, int(a + b >= 10))
            if port is not None:
                self.constrain_carry(t, w - 1, port)
        a, b = cycle.states[0]
        end = start + cycle.steps
        self.constrain_digit(end, 0, a)
        self.constrain_digit(end, self.widths[end] - 1, b)

    def constrain_raw_borrow(self, t: int, i: int, bit: int) -> None:
        if not 0 <= t < len(self._borrows) or not 0 <= i < len(self._borrows[t]):
            raise IndexError((t, i))
        if type(bit) is not int or bit not in (0, 1):
            raise ValueError("raw borrow port must be Boolean")
        self._shrink(self._borrows[t], i, 1 << bit, f"borrow row {t}")

    def constrain_innovation_sign(self, t: int, sign: int) -> None:
        """Intersect a separately authenticated sign of rev(next)-rev(source).

        A terminal raw borrow identifies negative versus nonnegative. Zero
        additionally forces equality of all padded reversal digits; it is
        never inferred from merely observing a terminal borrow of zero.
        """
        if type(sign) is not int or sign not in (-1, 0, 1):
            raise ValueError("innovation sign must be -1, 0 or 1")
        self.constrain_raw_borrow(t, len(self._borrows[t]) - 1, int(sign == -1))
        if sign == 0:
            a, b = self._domains[t], self._domains[t + 1]
            for i in range(max(len(a), len(b))):
                ma = a[i] if i < len(a) else 1
                mb = b[i] if i < len(b) else 1
                intersection = ma & mb
                if not intersection:
                    raise InconsistentReverseConstraints(
                        "zero innovation contradicts digit"
                    )
                if i < len(a):
                    self._shrink(a, i, intersection, "zero innovation source")
                if i < len(b):
                    self._shrink(b, i, intersection, "zero innovation target")

    def hypothesize_pair_period(
        self,
        start: int,
        period: int,
        depth: int,
        *,
        end: int | None = None,
        channel: str = "coefficient",
    ) -> None:
        """Add a period as a *conditional hypothesis*, never as authority.

        The 2rev10 period list can be tried here. It is NOT the reverse/add
        transition monoid; agreement of these factors cannot issue a power.
        """
        stop = len(self.widths) if end is None else end
        if channel not in ("coefficient", "five_band", "ordered_digits"):
            raise ValueError("period channel must preserve exact output semantics")
        if (
            type(start) is not int
            or type(period) is not int
            or type(depth) is not int
            or not 0 <= start < stop <= len(self.widths)
            or period < 1
            or start + period >= stop
            or depth < 1
            or any(2 * depth > w for w in self.widths[start:stop])
        ):
            raise ValueError("period comparison exceeds the active pair bands")
        for t in range(start, stop - period):
            for i in range(depth):
                self._period.append((t, t + period, i, channel))

    def test_period_candidates(
        self,
        periods: tuple[int, ...],
        *,
        start: int,
        depth: int,
        channel: str = "ordered_digits",
        max_rounds: int = 96,
    ) -> dict[int, str]:
        """Probe 2rev10 harmonic candidates against *reverse/add* factors.

        A contradiction soundly rejects a candidate. An arc-consistent
        completion is only `conditional`: it neither authenticates the
        period nor asserts that it continues for unbounded future time.
        The original source/widths/residues remain untouched.
        """
        import copy

        result: dict[int, str] = {}
        for period in periods:
            if type(period) is not int or period < 1:
                raise ValueError("candidate period must be positive")
            if start + period >= len(self.widths):
                result[period] = "outside_certified_horizon"
                continue
            trial = copy.deepcopy(self)
            trial.hypothesize_pair_period(
                start,
                period,
                depth,
                channel=channel,
            )
            try:
                trial.propagate(max_rounds=max_rounds)
            except InconsistentReverseConstraints:
                result[period] = "contradicted"
            else:
                result[period] = "conditional_not_authorized"
        return result

    def _addition(self, t: int) -> bool:
        """Rev-add column factor: two source digits plus one shared carry."""
        src, dst = self._domains[t], self._domains[t + 1]
        w, w_next = len(src), len(dst)
        changed = False
        if w_next == w + 1:
            changed |= self._shrink(dst, 0, 1 << 1, f"growth prefix {t}")
        for i in range(w):
            li, hi, out_i = w - 1 - i, i, w_next - 1 - i
            ca, cb = self._carries[t][i : i + 2]
            low_digits = _members(src[li])
            high_digits = () if li == hi else _members(src[hi])
            incoming_carries = _bits(ca)
            keep_lo = keep_hi = keep_out = keep_ca = keep_cb = 0
            for a in low_digits:
                for b in (a,) if li == hi else high_digits:
                    for c in incoming_carries:
                        total = a + b + c
                        carry = int(total >= 10)
                        digit = total % 10
                        if (cb & (1 << carry)) and (dst[out_i] & (1 << digit)):
                            keep_lo |= 1 << a
                            keep_hi |= 1 << b
                            keep_out |= 1 << digit
                            keep_ca |= 1 << c
                            keep_cb |= 1 << carry
            changed |= self._shrink(src, li, keep_lo, f"source low {t}")
            if li != hi:
                changed |= self._shrink(src, hi, keep_hi, f"source high {t}")
            changed |= self._shrink(dst, out_i, keep_out, f"successor {t}")
            changed |= self._shrink(self._carries[t], i, keep_ca, f"ingress {t}")
            changed |= self._shrink(self._carries[t], i + 1, keep_cb, f"egress {t}")
        return changed

    def _pair_constraints(self) -> bool:
        changed = False
        # Middle-transfer support is handled once, in _middle_constraints,
        # where the same symmetric filter is joined with both carry endpoints.
        # Re-running filter_symmetric_transfer here duplicated a full inward
        # pass on every propagation round and used a weaker projection that
        # ignored those endpoint carries.
        for (t, i), allowed_pair_sums in self._pairs.items():
            row = self._domains[t]
            a, b = len(row) - 1 - i, i
            low_keep = high_keep = 0
            for d in _members(row[a]):
                for e in (d,) if a == b else _members(row[b]):
                    if d + e in allowed_pair_sums:
                        low_keep |= 1 << d
                        high_keep |= 1 << e
            changed |= self._shrink(row, a, low_keep, f"pair low {t}")
            if a != b:
                changed |= self._shrink(row, b, high_keep, f"pair high {t}")
        for (t, i), bit in self._xor.items():
            w = self.widths[t]
            a, b = i, w - 1 - i
            left, right = self._carries[t][a], self._carries[t][b]
            l_keep = r_keep = 0
            for ca in _bits(left):
                for cb in _bits(right):
                    if ca ^ cb == bit:
                        l_keep |= 1 << ca
                        r_keep |= 1 << cb
            changed |= self._shrink(self._carries[t], a, l_keep, f"XOR low {t}")
            changed |= self._shrink(self._carries[t], b, r_keep, f"XOR high {t}")
        for t, u, i, channel in self._period:
            rt, ru = self._domains[t], self._domains[u]
            at, bt = len(rt) - 1 - i, i
            au, bu = len(ru) - 1 - i, i
            if channel == "ordered_digits":
                # A 2rev10 pair period refers to ordered *digits*, not sums.
                for ii, jj in ((at, au), (bt, bu)):
                    overlap = rt[ii] & ru[jj]
                    changed |= self._shrink(rt, ii, overlap, f"period row {t}")
                    changed |= self._shrink(ru, jj, overlap, f"period row {u}")
                continue
            sums_t = {
                a + b
                for a in _members(rt[at])
                for b in ((a,) if at == bt else _members(rt[bt]))
            }
            sums_u = {
                a + b
                for a in _members(ru[au])
                for b in ((a,) if au == bu else _members(ru[bu]))
            }
            if channel == "five_band":
                shared_bands = {
                    band
                    for band in DECIMAL_PAIR_BANDS
                    if any(value in decimal_pair_band_members(band) for value in sums_t)
                    and any(
                        value in decimal_pair_band_members(band) for value in sums_u
                    )
                }
                shared = {
                    value
                    for band in shared_bands
                    for value in decimal_pair_band_members(band)
                }
            else:
                shared = sums_t & sums_u
            if not shared:
                raise InconsistentReverseConstraints(
                    f"pair-period hypothesis fails at t={t}, t={u}, i={i}"
                )
            key_t, key_u = (t, i), (u, i)
            old_t, old_u = self._pairs.get(key_t), self._pairs.get(key_u)
            self.constrain_pair(t, i, tuple(shared))
            self.constrain_pair(u, i, tuple(shared))
            changed |= old_t != self._pairs[key_t] or old_u != self._pairs[key_u]
        return changed

    def _raw_borrow(self, t: int) -> bool:
        """Raw subtraction of reversed successors, sign kept separately."""
        source, target = self._domains[t], self._domains[t + 1]
        borrows = self._borrows[t]
        changed = False
        for j in range(len(borrows) - 1):
            src = (0,) if j >= len(source) else _members(source[j])
            dst = (0,) if j >= len(target) else _members(target[j])
            old, new = borrows[j : j + 2]
            incoming_borrows = _bits(old)
            keep_src = keep_dst = keep_old = keep_new = 0
            for a in dst:
                for b in src:
                    for beta in incoming_borrows:
                        bit = int(a < b + beta)
                        if new & (1 << bit):
                            keep_src |= 1 << b
                            keep_dst |= 1 << a
                            keep_old |= 1 << beta
                            keep_new |= 1 << bit
            if j < len(source):
                changed |= self._shrink(source, j, keep_src, f"borrow src {t}")
            if j < len(target):
                changed |= self._shrink(target, j, keep_dst, f"borrow dst {t}")
            changed |= self._shrink(borrows, j, keep_old, f"borrow in {t}")
            changed |= self._shrink(borrows, j + 1, keep_new, f"borrow out {t}")
        return changed

    def _residue(self, t: int, modulus: int, value: int) -> bool:
        row = self._domains[t]
        # Domain membership is stable until the final pruning sweep below.
        # Materialize each digit set once per column instead of recomputing it
        # for every reachable residue state in the forward/backward passes.
        digit_options = tuple(_members(mask) for mask in row)
        forward: list[set[int]] = [{0}]
        for options in digit_options:
            forward.append(
                {(10 * r + d) % modulus for r in forward[-1] for d in options}
            )
        if value not in forward[-1]:
            raise InconsistentReverseConstraints(f"mod {modulus} at row {t}")
        future: list[set[int]] = [set() for _ in range(len(row) + 1)]
        future[-1] = {value}
        for j in range(len(row) - 1, -1, -1):
            options = digit_options[j]
            following = future[j + 1]
            future[j] = {
                r
                for r in range(modulus)
                if any((10 * r + d) % modulus in following for d in options)
            }
        changed = False
        for j in range(len(row)):
            allowed = sum(
                1 << d
                for d in digit_options[j]
                if any((10 * r + d) % modulus in future[j + 1] for r in forward[j])
            )
            changed |= self._shrink(row, j, allowed, f"modular row {t}")
        return changed

    def propagate(
        self,
        *,
        max_rounds: int = 96,
        on_round: Callable[[], None] | None = None,
    ) -> ReverseInwardSummary:
        if type(max_rounds) is not int or not 1 <= max_rounds <= 512:
            raise ValueError("invalid propagation budget")
        for n in range(1, max_rounds + 1):
            if on_round is not None:
                on_round()
            changed = False
            for t in range(len(self._carries)):
                changed |= self._addition(t)
            changed |= self._pair_constraints()
            changed |= self._middle_constraints()
            for t in range(len(self._borrows)):
                changed |= self._raw_borrow(t)
            for (t, mod), residue in sorted(self._residues.items()):
                if mod == 198:  # decomposed exactly into mod99 and LSD parity
                    continue
                if mod in (9, 11) and (t, 99) in self._residues:
                    if self._residues[t, 99] % mod != residue:
                        raise InconsistentReverseConstraints("CRT residue mismatch")
                    continue
                changed |= self._residue(t, mod, residue)
            for t in range(len(self.widths)):
                if (t, 99) in self._residues:
                    changed |= constrain_center_from_outer_pairs(
                        self, t, self._residues[t, 99], self._exterior_mod99.get(t)
                    )
            # Iterate all shared temporal carry factors in both directions.
            for t in range(len(self._carries) - 1, -1, -1):
                changed |= self._addition(t)
            changed |= self._pair_constraints()
            changed |= self._middle_constraints()
            if not changed:
                self.rounds = n
                return self.summary()
        raise ValueError("reverse/add inward constraints did not stabilize")

    def digit_domain(self, t: int, i: int) -> tuple[int, ...]:
        return _members(self._domains[t][i])

    def carry_domain(self, t: int, i: int) -> tuple[int, ...]:
        return _bits(self._carries[t][i])

    def pair_domain(self, t: int, i: int) -> tuple[int, ...]:
        row = self._domains[t]
        a, b = len(row) - 1 - i, i
        allowed = self._pairs.get((t, i), frozenset(range(19)))
        return tuple(
            sorted(
                {
                    v + u
                    for v in _members(row[a])
                    for u in ((v,) if a == b else _members(row[b]))
                    if v + u in allowed
                }
            )
        )

    def f5_domain(self, t: int, i: int) -> tuple[int, ...]:
        """F5 lifts of all still-admissible radix-19 symmetric coefficients."""
        return tuple(sorted({s % 5 for s in self.pair_domain(t, i)}))

    def bank_mask_domain(
        self, t: int, start: int, count: int, channel: DecimalPairBand
    ) -> tuple[int | None, ...]:
        """Return 0/1 only for five-band bits forced in every completion."""
        if type(channel) is not DecimalPairBand or not 1 <= count <= 64:
            raise ValueError("invalid five-band mask/window")
        if start < 0 or start + count > (self.widths[t] + 1) // 2:
            raise IndexError("mask window reaches the moving center")
        members = decimal_pair_band_members(channel)
        row: list[int | None] = []
        for i in range(start, start + count):
            domain = self.pair_domain(t, i)
            bits = {int(s in members) for s in domain}
            row.append(next(iter(bits)) if len(bits) == 1 else None)
        return tuple(row)

    def walsh64_mod5(
        self, t: int, start: int, channel: DecimalPairBand
    ) -> tuple[int, ...]:
        """Demand a true spatial Walsh64 packet; reject unresolved lanes."""
        lanes = self.bank_mask_domain(t, start, 64, channel)
        if any(lane is None for lane in lanes):
            raise ValueError("Walsh input contains conditional five-band lanes")
        from number_compiler.arithmetic.fields.walsh import walsh64_mod5

        forced_lanes = cast(tuple[int, ...], lanes)
        return walsh64_mod5(sum(lane << i for i, lane in enumerate(forced_lanes)))

    def carry_borrow_xor_domain(self, t: int, boundary: int) -> tuple[int, ...]:
        """Joint accumulator-carry / RAW innovation-borrow radix boundary."""
        if not 0 <= t < len(self._carries) or not 0 <= boundary < min(
            len(self._carries[t]), len(self._borrows[t])
        ):
            raise IndexError((t, boundary))
        return tuple(
            sorted(
                {
                    a ^ b
                    for a in _bits(self._carries[t][boundary])
                    for b in _bits(self._borrows[t][boundary])
                }
            )
        )

    def summary(self) -> ReverseInwardSummary:
        pairs: list[tuple[tuple[str, ...], ...]] = []
        for t, width in enumerate(self.widths):
            bands: list[tuple[str, ...]] = []
            for i in range((width + 1) // 2):
                dom = self.pair_domain(t, i)
                bands.append(
                    tuple(
                        band.value
                        for band in DECIMAL_PAIR_BANDS
                        if any(x in decimal_pair_band_members(band) for x in dom)
                    )
                )
            pairs.append(tuple(bands))
        return ReverseInwardSummary(
            self.widths,
            self.rounds,
            tuple(sum(mask.bit_count() == 1 for mask in row) for row in self._domains),
            tuple(sum(mask.bit_count() == 1 for mask in row) for row in self._carries),
            tuple(sum(mask.bit_count() == 1 for mask in row) for row in self._borrows),
            tuple(pairs),
            tuple(self._period),
            False,
            False,
        )


__all__ = [
    "InconsistentReverseConstraints",
    "ReverseInwardConstraints",
    "ReverseInwardSummary",
]
