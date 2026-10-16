"""Source-authenticated multiradix refinement of dyadic-three interior bits.

The finite 5/10 residue clocks are *observers*, not a binary-digit oracle.
Binary positions are authenticated separately by the dyadic 2-adic counter.
Each signed Fermat correction is explicitly partial unless the complete
transition has an independent all-position coverage certificate.

The finite Moore-style audit below searches actual source trajectories for
future-output conflicts.  Elimination by singleton keys is not compression,
and no finite-corpus result is promoted to a primality theorem.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass, field
from typing import TYPE_CHECKING
from weakref import ReferenceType, ref

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.walsh import WalshH5, walsh_h5_at_offset
from number_compiler.hashlife.execution.source_image_seals import _typed_equal
from number_compiler.sequences.power_numbers.source_matrix import (
    FermatMultiradixPort,
    demand_three_power_multiradix_port,
)
from number_compiler.sequences.power_numbers.three_dyadic_boolean_counter import (
    MAX_COUNTER_PRECISION,
    MAX_COUNTER_WINDOW_BATCH,
    DyadicBooleanCounterWindow,
    demand_dyadic_boolean_counter,
    demand_dyadic_boolean_counter_windows,
)

if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.three_dyadic_radial_counter_tape import (
        DyadicCertifiedTape,
    )
    from number_compiler.sequences.power_numbers.three_power_bilateral_border import (
        ThreePowerBilateralInteriorQuotient,
    )

MAX_ADAPTIVE_WINDOWS = MAX_COUNTER_WINDOW_BATCH
MAX_ADAPTIVE_RADICES = 8
DEFAULT_ADAPTIVE_RADICES = ((2, 6), (5, 4), (10, 4))
_ADAPTIVE_ISSUER = object()


@dataclass(frozen=True, slots=True)
class _AdaptiveProvenance:
    issuer: object
    record: ReferenceType[object]
    snapshot: tuple[object, ...]


def _port_snapshot(port: FermatMultiradixPort) -> tuple[object, ...]:
    return (
        port.index,
        port.level,
        port.base,
        port.places,
        port.modulus,
        port.source_residue,
        port.previous_residue,
        port.next_residue,
        tuple(
            (
                item.places,
                item.source_remainder,
                item.tripling_carry,
                item.doubling_carry,
                item.tripling_add_carry,
                item.tripling_sub_borrow,
                item.innovation_carry,
                item.innovation_borrow,
                item.successive_innovation_borrow,
            )
            for item in port.boundaries
        ),
        port.carry_transition_steps,
        port.carry_monoid_sizes,
        tuple(
            (
                item.modulus,
                item.factor_trial_candidates,
                item.scalar_power_compositions,
                item.matrix_power_compositions,
            )
            for item in port.work
        ),
    )


def _adaptive_snapshot(action: AdaptiveInteriorAction) -> tuple[object, ...]:
    return (
        action.index,
        action.level,
        tuple((id(port), _port_snapshot(port)) for port in action.radix_ports),
        tuple((id(window), window._snapshot()) for window in action.windows),
    )


def _seal_adaptive(action: AdaptiveInteriorAction) -> None:
    object.__setattr__(
        action,
        "_issuer",
        _AdaptiveProvenance(_ADAPTIVE_ISSUER, ref(action), _adaptive_snapshot(action)),
    )


def _checked_candidate(index: int, level: int) -> int:
    if type(index) is not int or not 1 <= index <= 16:
        raise ValueError("adaptive Fermat index outside the bounded source API")
    if type(level) is not int or not 1 <= level < (1 << index):
        raise ValueError("adaptive source level is not in Fermat's inner horizon")
    return 1 << index


@dataclass(frozen=True, slots=True, weakref_slot=True)
class AdaptiveInteriorAction:
    """The *observed* signed action of disjoint authenticated counter windows.

    The class vector covers just these positions, not all high source bits.
    No caller may convert this packet into a prime certificate without a
    separately established complete-coverage theorem.
    """

    index: int
    level: int
    radix_ports: tuple[FermatMultiradixPort, ...]
    windows: tuple[DyadicBooleanCounterWindow, ...]
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        w = _checked_candidate(self.index, self.level)
        if (
            type(self.radix_ports) is not tuple
            or not 1 <= len(self.radix_ports) <= MAX_ADAPTIVE_RADICES
        ):
            raise ValueError("invalid adaptive radix port list")
        if len({(p.base, p.places) for p in self.radix_ports}) != len(self.radix_ports):
            raise ValueError("duplicate adaptive radix port")
        for port in self.radix_ports:
            if type(port) is not FermatMultiradixPort or (port.index, port.level) != (
                self.index,
                self.level,
            ):
                raise ValueError("foreign adaptive radix observation")
            if not port.producer_verified:
                raise ValueError(
                    "foreign or unauthenticated adaptive radix observation"
                )
        if (
            type(self.windows) is not tuple
            or not 1 <= len(self.windows) <= MAX_ADAPTIVE_WINDOWS
        ):
            raise ValueError("invalid adaptive Boolean window list")
        previous_end = self.level + 1
        for win in self.windows:
            if (
                type(win) is not DyadicBooleanCounterWindow
                or win.level != self.level
                or win.fermat_width != w
                or win.start < previous_end
            ):
                raise ValueError("overlapping or foreign counter windows")
            win.verify()
            previous_end = win.start + win.width

    @property
    def producer_verified(self) -> bool:
        issuer = self._issuer
        return (
            type(issuer) is _AdaptiveProvenance
            and issuer.issuer is _ADAPTIVE_ISSUER
            and issuer.record() is self
            and _typed_equal(issuer.snapshot, _adaptive_snapshot(self))
            and all(port.producer_verified for port in self.radix_ports)
            and all(window.producer_verified for window in self.windows)
        )

    def _require_verified(self) -> None:
        if not self.producer_verified:
            raise ValueError("adaptive interior has no verified source provenance")

    def bilateral_source_constraints(
        self,
        *,
        decimal_windows: tuple[tuple[int, int], ...] = (),
        phase_binary_places: int | None = None,
        phase_decimal_places: int | None = None,
        low_binary_places: int = 12,
        low_decimal_places: int = 4,
        high_binary_places: int = 8,
        high_decimal_places: int = 4,
    ) -> ThreePowerBilateralInteriorQuotient:
        """Push this authenticated normalized-unit source into BOTH borders.

        The adaptive counter windows describe u_t, so their bits occupy
        X_t positions t+2+start. Their source words are independently checked
        against the binary radix orbit. Decimal islands use a separate exact
        10^j orbit, while the upper digits come from the certified radial
        clock. No source/target clocks or Walsh channels are conflated.
        """
        from number_compiler.sequences.power_numbers.three_power_bilateral_border import (
            demand_three_power_bilateral_interior,
        )

        self._require_verified()
        source_positions = tuple(
            (self.level + 2 + window.start, window.width) for window in self.windows
        )
        result = demand_three_power_bilateral_interior(
            self.index,
            self.level,
            binary_windows=source_positions,
            decimal_windows=decimal_windows,
            phase_binary_places=phase_binary_places,
            phase_decimal_places=phase_decimal_places,
            low_binary_places=low_binary_places,
            low_decimal_places=low_decimal_places,
            high_binary_places=high_binary_places,
            high_decimal_places=high_decimal_places,
        )
        for window, (start, width) in zip(self.windows, source_positions, strict=True):
            known = next(
                (
                    item
                    for item in result.binary_middle.windows
                    if item.start <= start and start + width <= item.start + item.width
                ),
                None,
            )
            if known is None:
                raise ArithmeticError("adaptive source island lost during phase join")
            extracted = (known.radix_value >> (start - known.start)) & (
                (1 << width) - 1
            )
            if extracted != window.source_bits:
                raise ArithmeticError(
                    "normalized-unit and binary border source disagree"
                )
        for port in self.radix_ports:
            active = (
                result.bilateral.binary
                if port.base == 2
                else (result.bilateral.decimal if port.base == 10 else None)
            )
            if active is None:
                continue
            modulus = min(port.modulus, active.base**active.low_places)
            if port.source_residue % modulus != active.low_source % modulus:
                raise ArithmeticError("adaptive and bilateral CRT sources disagree")
        return result

    @property
    def signed_classes(self) -> tuple[tuple[int, int], ...]:
        """Complete signed totals *within the requested windows*, modulo w."""
        self._require_verified()
        counts: dict[int, int] = defaultdict(int)
        for window in self.windows:
            for residue, value in window.absolute_signed_classes:
                counts[residue] += value
        return tuple(sorted((r, c) for r, c in counts.items() if c))

    @property
    def partial_fermat_correction(self) -> int:
        self._require_verified()
        mod = (1 << (1 << self.index)) + 1
        summed = sum(win.signed_fermat_correction for win in self.windows) % mod
        from_classes = sum((1 << r) * c for r, c in self.signed_classes) % mod
        if summed != from_classes:
            raise ArithmeticError("merged signed classes differ from window folds")
        return summed

    @property
    def changed_bit_count(self) -> int:
        self._require_verified()
        return sum(window.xor_mask.bit_count() for window in self.windows)

    @property
    def harmonic(self) -> WalshH5:
        """Absolute-position H5 of disjoint XOR masks, not the full word."""
        self._require_verified()
        packets = tuple(win.absolute_walsh_h5 for win in self.windows)
        return WalshH5(
            0,
            sum(p.phi2 for p in packets) % 5,
            sum(p.phi3_a for p in packets) % 5,
            sum(p.phi3_b for p in packets) % 5,
        )

    @property
    def unresolved_high_positions(self) -> bool:
        """Fail closed except for a single provably complete pivot-to-end span."""
        self._require_verified()
        return not (
            len(self.windows) == 1 and self.windows[0].covers_complete_unit_transition
        )

    @property
    def terminal_status(self) -> str:
        # This is a source transition, not an authorized Fermat terminal bit.
        self._require_verified()
        return "UNKNOWN"


def demand_three_power_adaptive_interior(
    index: int,
    level: int,
    windows: tuple[tuple[int, int], ...],
    *,
    radix_demands: tuple[tuple[int, int], ...] = DEFAULT_ADAPTIVE_RADICES,
) -> AdaptiveInteriorAction:
    """Demand finite interior positions, radix-5/10 orbits and signed folds.

    Window offsets are relative to the true unit pivot t+1; every requested
    bit is certified with the *source-derived* 2-adic formula.  Radix-5/10
    ports constrain the same source but cannot invent unrequested binary bits.
    """
    w = _checked_candidate(index, level)
    if (
        type(windows) is not tuple
        or not 1 <= len(windows) <= MAX_ADAPTIVE_WINDOWS
        or type(radix_demands) is not tuple
        or not 1 <= len(radix_demands) <= MAX_ADAPTIVE_RADICES
    ):
        raise ValueError("invalid adaptive demand tuple")
    if len(set(radix_demands)) != len(radix_demands):
        raise ValueError("duplicate adaptive radix request")
    for demand in radix_demands:
        if type(demand) is not tuple or len(demand) != 2:
            raise TypeError("radix demand is an exact (base, places) tuple")
        require_integer(demand[0], "radix base", 2)
        require_integer(demand[1], "radix places", 1)
    previous_end = level + 1
    for item in windows:
        if type(item) is not tuple or len(item) != 2:
            raise TypeError("window is an (offset,width) tuple")
        offset, width = item
        offset = require_integer(offset, "interior window offset", 0)
        width = require_integer(width, "interior window width", 1)
        start = level + 1 + offset
        if start < previous_end or start + width > MAX_COUNTER_PRECISION:
            raise ValueError("overlapping or over-budget adaptive window")
        previous_end = start + width
    # Authenticate radix observations first; they do not set Boolean values.
    ports = tuple(
        demand_three_power_multiradix_port(index, level, b, j) for b, j in radix_demands
    )
    blocks = demand_dyadic_boolean_counter_windows(level, windows, fermat_width=w)
    action = AdaptiveInteriorAction(index, level, ports, blocks)
    _seal_adaptive(action)
    return action


@dataclass(frozen=True, slots=True)
class FiniteMooreStage:
    """A finite right-language collision census, never a global proof."""

    key_name: str
    classes: int
    repeated_classes: int
    singleton_classes: int
    future_conflicts: int
    first_conflict: tuple[tuple[int, int, int], tuple[int, int, int]] | None

    @property
    def nonreconstructive_closed_on_sample(self) -> bool:
        return self.future_conflicts == 0 and self.repeated_classes > 0


def audit_adaptive_fermat_moore(
    index: int, *, output_width: int = 12
) -> tuple[FiniteMooreStage, ...]:
    """Check actual F_n source times against NEXT pivot/fold output.

    The observed sample is t=2..2**n-2 (so the next level remains in the
    Fermat inner horizon).  Keys exclude t: using the clock itself would make
    all rows trivially distinct.  No source integer or candidate residue is
    materialized; only small-radix source ports and finite-precision XOR masks.
    """
    w = _checked_candidate(index, 2)
    if index > 5 or type(output_width) is not int or not 1 <= output_width <= 32:
        raise ValueError("bounded Moore audit only supports F2..F5")
    rows = []
    for t in range(2, w - 1):
        next_action = demand_dyadic_boolean_counter(t + 1, output_width, fermat_width=w)
        next_output = (next_action.xor_mask, next_action.signed_fermat_correction)
        current = demand_dyadic_boolean_counter(t, output_width, fermat_width=w)
        # Demand only precision actually needed at each stage; the base-10
        # source already contains its 2-primary projection through CRT.
        source = tuple(
            demand_three_power_multiradix_port(index, t, 10, j).source_residue
            for j in range(1, 5)
        )
        five = tuple(
            demand_three_power_multiradix_port(index, t, 5, j).source_residue
            for j in range(1, 5)
        )
        h5 = current.absolute_walsh_h5
        rows.append((t, source, five, (h5.phi2, h5.phi3_a, h5.phi3_b), next_output))
    stages = (
        ("10^1 + 5^1", lambda r: (r[1][0], r[2][0])),
        ("10^2 + 5^2", lambda r: (r[1][1], r[2][1])),
        ("10^3 + 5^3", lambda r: (r[1][2], r[2][2])),
        ("10^2 + 5^2 + current H5", lambda r: (r[1][1], r[2][1], r[3])),
        ("10^3 + 5^3 + current H5", lambda r: (r[1][2], r[2][2], r[3])),
        ("10^4 + 5^4", lambda r: (r[1][3], r[2][3])),
    )
    result = []
    for name, selector in stages:
        classes = defaultdict(list)
        for row in rows:
            classes[selector(row)].append(row)
        repeat = sum(len(group) > 1 for group in classes.values())
        conflicting = [
            group
            for group in classes.values()
            if len({entry[4] for entry in group}) > 1
        ]
        example = None
        if conflicting:
            first = conflicting[0]
            other = next(item for item in first[1:] if item[4] != first[0][4])
            example = (
                (first[0][0], *first[0][4]),
                (other[0], *other[4]),
            )
        result.append(
            FiniteMooreStage(
                name,
                len(classes),
                repeat,
                sum(len(group) == 1 for group in classes.values()),
                len(conflicting),
                example,
            )
        )
    return tuple(result)


__all__ = [
    "DEFAULT_ADAPTIVE_RADICES",
    "AdaptiveInteriorAction",
    "FiniteMooreStage",
    "audit_adaptive_fermat_moore",
    "demand_three_power_adaptive_interior",
]


@dataclass(frozen=True, slots=True)
class AdaptiveRefinedTape:
    """Low/radial 0/1 tape extended by certified interior counter windows.

    The radial clock controls only the leading prefix.  This wrapper uses
    source-derived dyadic windows for selected genuine middle bits, without
    filling uncovered intervals from the finite base-5/10 orbit.
    """

    base_tape: DyadicCertifiedTape
    action: AdaptiveInteriorAction

    def _base_chunks_unchecked(self) -> tuple[tuple[int, int, int], ...]:
        return (
            (0, self.base_tape.low_bits, self.base_tape.low_value),
            (
                self.base_tape.high_start,
                self.base_tape.word_bits,
                self.base_tape.high_value,
            ),
        )

    def _validate_binding(self) -> None:
        from number_compiler.sequences.power_numbers.three_dyadic_radial_counter_tape import (
            DyadicCertifiedTape,
        )

        if (
            type(self.base_tape) is not DyadicCertifiedTape
            or type(self.action) is not AdaptiveInteriorAction
        ):
            raise TypeError(
                "adaptive tape needs authenticated radial and interior owners"
            )
        if not self.base_tape.producer_verified or not self.action.producer_verified:
            raise ValueError("adaptive tape inputs lack verified source provenance")
        if (
            self.base_tape.source_level != self.action.level
            or self.base_tape.fermat_width != (1 << self.action.index)
        ):
            raise ValueError("radial and multiradix source occurrences disagree")
        # The counter is on u_(t+1). In 3**(2**(t+1)), those bits begin
        # at position t+3 after the 1 + 2**(t+3)*u_(t+1) normalization.
        base_chunks = self._base_chunks_unchecked()
        for win in self.action.windows:
            start = self.action.level + 3 + win.start
            stop = start + win.width
            if stop > self.base_tape.word_bits:
                raise ValueError("counter window extends above certified source width")
            for other_start, other_stop, other_value in base_chunks:
                overlap_lo = max(start, other_start)
                overlap_hi = min(stop, other_stop)
                if overlap_lo < overlap_hi:
                    mask = (1 << (overlap_hi - overlap_lo)) - 1
                    source_overlap = (win.result_bits >> (overlap_lo - start)) & mask
                    other_overlap = (other_value >> (overlap_lo - other_start)) & mask
                    if source_overlap != other_overlap:
                        raise ArithmeticError(
                            "certified interior and radial/binary bits disagree"
                        )

    def __post_init__(self) -> None:
        self._validate_binding()

    def _certified_chunks_unchecked(self) -> tuple[tuple[int, int, int], ...]:
        added = tuple(
            (
                self.action.level + 3 + win.start,
                self.action.level + 3 + win.start + win.width,
                win.result_bits,
            )
            for win in self.action.windows
        )
        return tuple(sorted((*self._base_chunks_unchecked(), *added)))

    @property
    def certified_chunks(self) -> tuple[tuple[int, int, int], ...]:
        self._validate_binding()
        return self._certified_chunks_unchecked()

    @property
    def missing_intervals(self) -> tuple[tuple[int, int], ...]:
        missing = []
        cursor = 0
        for start, stop, _ in self.certified_chunks:
            if start > cursor:
                missing.append((cursor, start))
            cursor = max(cursor, stop)
        if cursor < self.base_tape.word_bits:
            missing.append((cursor, self.base_tape.word_bits))
        return tuple(missing)

    @property
    def complete(self) -> bool:
        return not self.missing_intervals

    def output_window(self, start: int, width: int) -> int:
        """Read any contiguous union of authenticated source intervals."""
        self._validate_binding()
        if type(start) is not int or type(width) is not int or start < 0 or width <= 0:
            raise ValueError("invalid adaptive tape read")
        stop = start + width
        if stop > self.base_tape.word_bits:
            raise ValueError("adaptive tape window exceeds source width")
        output = 0
        cursor = start
        segments = self._certified_chunks_unchecked()
        while cursor < stop:
            covering = [part for part in segments if part[0] <= cursor < part[1]]
            if not covering:
                raise ValueError(
                    ("middle-source-bit-not-certified", cursor, self.missing_intervals)
                )
            begin, end, contents = max(covering, key=lambda p: p[1])
            take = min(end, stop) - cursor
            mask = (1 << take) - 1
            output |= ((contents >> (cursor - begin)) & mask) << (cursor - start)
            cursor += take
        return output

    def output_tape(self, start: int, width: int, *, msb_first: bool = False) -> str:
        written = format(self.output_window(start, width), f"0{width}b")
        return written if msb_first else written[::-1]

    def output_h5(self, start: int, width: int) -> WalshH5:
        return walsh_h5_at_offset(self.output_window(start, width), width, start)

    def complete_signed_fold(self) -> int:
        if not self.complete:
            raise ValueError(("global-0-1-tape-not-certified", self.missing_intervals))
        from number_compiler.sequences.power_numbers.fermat_signed_reducer import (
            fold_signed_fermat,
        )

        full = self.output_window(0, self.base_tape.word_bits)
        return fold_signed_fermat(full, self.base_tape.fermat_width)


__all__.append("AdaptiveRefinedTape")
