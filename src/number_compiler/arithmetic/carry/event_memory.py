"""Exact bounded-temporal-memory theorem for reverse-and-add carry forcing.

This module is algebra/proof support, not an independently cached semantic root.
Its exact H-row reconstruction is a proof certificate.  It does not implement
the output-complete interface quotient required by production field images;
retaining these rows, even as packed columns, would retain exact future history.

For base ``b>=3`` let ``w=bit_length(2b-2)`` and ``H=4w``.  The previously
established outer-coefficient growth-run bound implies every H-step interval
contains at least w no-growth doublings.  In

    S_(t+1) = A_g S_t + E_t,   A_0=2, A_1=1+z,

where ``A_1`` is the exact shift of the reversal frame when the symmetric
pair width grows; it is not an independent extra-digit forcing coordinate.

the old source contribution is therefore zero modulo ``2**w`` after H steps.
Since every exact pair coefficient lies in ``[0,2b-2] < 2**w``, the previous H
forcing fields reconstruct the endpoint pair exactly.  Event widths encode the
intervening growth bits because ``len(E_t)=len(S_(t+1))``.

The signed event field is itself a deterministic function of one *forward*
binary carry track; the reflected carry is only an index view.  Thus decimal
reverse/add has an exact order-20 nonlinear recurrence on binary carry fields.
"""

from __future__ import annotations

import itertools
from collections.abc import Callable, Iterable, Sequence

from number_compiler.arithmetic.formula.skew_residue_laws import (
    pair_growth_edge,
    pair_growth_interior,
    pair_no_growth,
)


def pair_plane_bits(base: int) -> int:
    base = int(base)
    if base < 3:
        raise ValueError("bounded event-memory theorem currently requires base>=3")
    return (2 * (base - 1)).bit_length()


def event_memory_horizon(base: int) -> int:
    return 4 * pair_plane_bits(base)


def forcing_event_alphabet(base: int) -> tuple[int, ...]:
    """Coefficient alphabet of beta in S' = A_g S + beta.

    This is not the alphabet of (1-z) beta or of the centered forcing term.
    Those changes of basis must retain differences and boundary corrections.
    """
    base = int(base)
    if base < 2:
        raise ValueError(base)
    return tuple(sorted({-2 * base, -2 * base + 1, -2 * base + 2, 1 - base, 0, 1, 2}))


def forcing_difference_alphabet(base: int) -> tuple[int, ...]:
    """Sound finite cover for (1-z) beta, including its terminal boundary.

    Zero belongs to the forcing alphabet, so zero extension at both ends is
    included. This is a difference-set cover, not an assertion that every
    pair of adjacent alphabet symbols occurs on an admitted trajectory.
    """
    alphabet = forcing_event_alphabet(base)
    return tuple(sorted({a - b for a in alphabet for b in alphabet}))


def _forward_carry_field(
    source: tuple[int, ...], base: int, *, incoming: int = 0
) -> tuple[int, ...]:
    """Canonical forward carry scan shared by transition and theorem views."""
    if type(incoming) is not int or incoming not in (0, 1):
        raise ValueError("incoming carry must be zero or one")
    carry = [0] * (len(source) + 1)
    carry[0] = incoming
    for i, value in enumerate(source):
        carry[i + 1] = int(value + carry[i] >= base)
    return tuple(carry)


def pair_step_with_carry(
    source: Sequence[int],
    base: int,
    *,
    incoming: int = 0,
) -> tuple[tuple[int, ...], int, tuple[int, ...]]:
    """Internal transition returning the already-computed carry certificate too."""
    source = tuple(map(int, source))
    base = int(base)
    if not source or source != source[::-1]:
        raise ValueError("pair source must be nonempty and symmetric")
    d = len(source)
    carry = _forward_carry_field(source, base, incoming=incoming)
    growth = carry[d]
    reverse = tuple(reversed(carry))
    if not growth:
        out = tuple(
            pair_no_growth(
                source[i], carry[i], carry[i + 1], reverse[i + 1], reverse[i], base
            )
            for i in range(d)
        )
    else:
        edge = pair_growth_edge(source[0], carry[1], base)
        out = (
            (edge,)
            + tuple(
                pair_growth_interior(
                    source[i],
                    source[i - 1],
                    carry[i],
                    carry[i + 1],
                    reverse[i],
                    reverse[i - 1],
                    base,
                )
                for i in range(1, d)
            )
            + (edge,)
        )
    if any(not 0 <= value <= 2 * (base - 1) for value in out):
        raise AssertionError((base, source, out))
    if out != out[::-1]:
        raise AssertionError("pair recurrence lost symmetry")
    return out, growth, carry


def pair_step(source: Sequence[int], base: int) -> tuple[tuple[int, ...], int]:
    """Canonical exact pair-field transition used by theorem/bootstrap compilers."""
    out, growth, _carry = pair_step_with_carry(source, base)
    return out, growth


def carry_field(source: Sequence[int], *, base: int = 10) -> tuple[int, ...]:
    """Forward carry boundaries ``C_0..C_d`` with ``C_0=0``."""
    source = tuple(map(int, source))
    base = int(base)
    if not source:
        raise ValueError("empty pair source")
    return _forward_carry_field(source, base)


def forcing_event(
    source: Sequence[int], target: Sequence[int], growth: int
) -> tuple[int, ...]:
    """Return the signed nonlinear field ``E_t`` in ``S' = A_g S + E``."""
    source = tuple(map(int, source))
    target = tuple(map(int, target))
    growth = int(growth)
    if growth not in (0, 1) or len(target) != len(source) + growth:
        raise ValueError((len(source), len(target), growth))
    if growth:
        d = len(source)
        bulk = tuple(
            (source[i] if i < d else 0) + (source[i - 1] if 0 <= i - 1 < d else 0)
            for i in range(d + 1)
        )
    else:
        bulk = tuple(2 * value for value in source)
    return tuple(y - x for x, y in zip(bulk, target, strict=True))


def forcing_event_from_carry(
    carry: Sequence[int], *, base: int = 10
) -> tuple[int, ...]:
    """Recover ``E`` from the sole forward binary carry field.

    For no growth,

        E_i = C_i + C_(d-i-1) - b(C_(i+1)+C_(d-i)).

    For growth, both edges are ``1-b*C_1`` and interior positions satisfy

        E_i = C_i + C_(d-i) - b(C_(i+1)+C_(d-i+1)).
    """
    c = tuple(map(int, carry))
    base = int(base)
    if len(c) < 2 or c[0] != 0 or any(v not in (0, 1) for v in c):
        raise ValueError("invalid forward carry track")
    width = len(c) - 1
    if not c[-1]:
        return tuple(
            pair_no_growth(
                0, c[index], c[index + 1], c[width - index - 1], c[width - index], base
            )
            for index in range(width)
        )
    edge = pair_growth_edge(0, c[1], base)
    return (
        (edge,)
        + tuple(
            pair_growth_interior(
                0,
                0,
                c[index],
                c[index + 1],
                c[width - index],
                c[width - index + 1],
                base,
            )
            for index in range(1, width)
        )
        + (edge,)
    )


def growths_from_event_widths(events: Sequence[Sequence[int]]) -> tuple[int, ...]:
    """Recover every *later* branch bit from event widths.

    ``E_j`` has the width of ``S_(j+1)``, hence consecutive width differences
    are exactly the growth bits following the first event in the window.
    """
    widths = tuple(len(row) for row in events)
    if any(width <= 0 for width in widths):
        raise ValueError("event fields must be nonempty")
    growths = tuple(b - a for a, b in itertools.pairwise(widths))
    if any(g not in (0, 1) for g in growths):
        raise ValueError(
            "event widths do not encode a valid reverse/add growth schedule"
        )
    return growths


def endpoint_width_from_event_window(events: Sequence[Sequence[int]]) -> int:
    """Exact endpoint pair width represented by an event window."""
    if not events or not events[-1]:
        raise ValueError("event window must be nonempty")
    return len(events[-1])


class _ForcingFold:
    """One coefficient image and a saturated zero-forcing multiplier.

    Lanes have two spare bits: 2*a+b and a+shift(a)+b never spill.
    This is an arithmetic action, not a cache of previous temporal rows.
    """

    def __init__(self, bits: int) -> None:
        self.bits = bits
        self.coefficient_mask = (1 << bits) - 1
        self.lane_bytes = (bits + 9) // 8
        self.lane_bits = 8 * self.lane_bytes
        self.width = 0
        self.image = 0
        self.pending = 0
        self.mask = 0
        self.lanes = 0

    def _resize(self, width: int) -> None:
        self.width = width
        self.lanes = ((1 << (self.lane_bits * width)) - 1) // (
            (1 << self.lane_bits) - 1
        )
        self.mask = self.coefficient_mask * self.lanes

    def quiet(self, duration: int) -> None:
        """Compose (2**duration, 0); duration >= bits is the same action."""
        if self.image:
            self.pending = min(self.bits, self.pending + duration)
            if self.pending == self.bits:
                self.image = self.pending = 0

    def _flush(self) -> None:
        if self.pending:
            # Mask the lanes before a multi-bit shift. The two guard bits
            # suffice for one affine sum, not an arbitrary pending power.
            keep = self.lanes * (self.coefficient_mask >> self.pending)
            self.image = (self.image & keep) << self.pending
            self.pending = 0

    def append(self, row: tuple[int, ...] | None, width: int) -> None:
        if not width or (row is not None and len(row) != width):
            raise ValueError("event fields must be nonempty")
        growth = width - self.width if self.width else 0
        if growth not in (0, 1):
            raise ValueError(
                "event widths do not encode a valid reverse/add growth schedule"
            )
        if self.width != width:
            self._flush()
            self._resize(width)
        if row is None or not any(row):
            if growth:
                self.image = (self.image + (self.image << self.lane_bits)) & self.mask
            else:
                self.quiet(1)
            return
        self._flush()
        if self.lane_bytes == 1:
            payload = bytes(value & self.coefficient_mask for value in row)
        else:
            payload = b"".join(
                (value & self.coefficient_mask).to_bytes(self.lane_bytes, "little")
                for value in row
            )
        forcing = int.from_bytes(payload, "little")
        homogeneous = (
            self.image + (self.image << self.lane_bits) if growth else self.image << 1
        )
        self.image = (homogeneous + forcing) & self.mask

    def finish(self) -> tuple[int, ...]:
        if not self.width:
            raise ValueError("a forcing fold requires nonempty event rows")
        self._flush()
        if not self.image:
            return (0,) * self.width
        raw = self.image.to_bytes(self.width * self.lane_bytes, "little")
        if self.lane_bytes == 1:
            return tuple(raw)
        return tuple(
            int.from_bytes(raw[i : i + self.lane_bytes], "little")
            for i in range(0, len(raw), self.lane_bytes)
        )


def _live_event_start(events: Sequence[Sequence[int]], bits: int) -> int:
    """Validate the complete geometry; find the first surviving contribution.

    This only reads widths. It does not construct a history of growth bits.
    """
    quiet = 0
    start = 0
    later_width = 0
    for i in range(len(events) - 1, -1, -1):
        width = len(events[i])
        if not width:
            raise ValueError("event fields must be nonempty")
        if later_width:
            growth = later_width - width
            if growth not in (0, 1):
                raise ValueError(
                    "event widths do not encode a valid reverse/add growth schedule"
                )
            quiet = min(bits, quiet + 1 - growth)
        if quiet == bits and not start:
            start = i + 1
        later_width = width
    return start


def fold_forcing_events(
    events: Iterable[Sequence[int]],
    *,
    base: int = 10,
    record_updates: Callable[[int], None] | None = None,
) -> tuple[int, ...]:
    """Fold only the live modular forcing action, with zero initial field.

    Supplied sequences permit algebraic elimination of an extinct prefix
    *before* coefficient arithmetic. A streaming producer instead retains
    only the current image. Zero rows compose a saturated homogeneous
    multiplier, not another full-width carry field. The update counter
    counts coefficients supplied to the retained fold (including zeros),
    not Python iterations or the work of validating the discarded input.
    Neither route authenticates a trajectory or infers its future forcing.
    """
    bits = pair_plane_bits(base)
    fold = _ForcingFold(bits)
    updates = 0
    try:
        start = _live_event_start(events, bits) if isinstance(events, Sequence) else 0
        for i, event in enumerate(events):
            if i < start:
                # Keep the former integer-conversion contract on untrusted
                # extinct inputs, but do not build or apply their fields.
                for value in event:
                    if type(value) is not int:
                        int(value)
                continue
            row = tuple(map(int, event))
            fold.append(row, len(row))
            updates += len(row)
        return fold.finish()
    finally:
        if record_updates is not None:
            record_updates(updates)


def forcing_image_from_certified_carry_suffix(
    carries: Iterable[Sequence[int]], *, source_width: int, base: int = 10
) -> tuple[int, ...]:
    """Recover a pair field from authenticated contiguous carry actions.

    All supplied rows must satisfy the original binary and width guard.
    For a sequence, discard annihilated forcing *before* constructing any
    of its events. An all-zero carry track issues the homogeneous action
    directly, with no event-row allocation. Unknown future rows are not
    inferred. Iterators use the same action in a single streaming pass.
    """
    if type(source_width) is not int or source_width < 1:
        raise ValueError("positive exact initial coefficient width required")
    if type(base) is not int:
        raise TypeError("base must be an exact integer")
    bits = pair_plane_bits(base)
    fold = _ForcingFold(bits)

    def validate(row: Sequence[int], width: int) -> int:
        if any(type(bit) is not int for bit in row):
            raise TypeError("carry bits must be exact integers")
        if not row or row[0] != 0 or any(bit not in (0, 1) for bit in row):
            raise ValueError("invalid forward carry geometry")
        if len(row) != width + 1:
            raise ValueError("carry suffix has inconsistent consecutive widths")
        return row[-1]

    def consume(row: Sequence[int]) -> None:
        width = len(row) - 1 + row[-1]
        # Zero carries imply no growth and zero nonlinear forcing. There is
        # no need to construct a row of zeros in the coefficient alphabet.
        event = forcing_event_from_carry(row, base=base) if any(row) else None
        fold.append(event, width)

    quiet = 0
    width = source_width
    if isinstance(carries, Sequence):
        for row in carries:
            growth = validate(row, width)
            width += growth
            quiet = min(bits, quiet + 1 - growth)
        if quiet < bits:
            raise ValueError("carry suffix has not annihilated its unknown source")
        later_quiet = 0
        start = len(carries)
        while later_quiet < bits:
            start -= 1
            later_quiet += 1 - carries[start][-1]
        for i in range(start, len(carries)):
            consume(carries[i])
    else:
        for carry in carries:
            row = tuple(carry)
            growth = validate(row, width)
            width += growth
            quiet = min(bits, quiet + 1 - growth)
            consume(row)
        if quiet < bits:
            raise ValueError("carry suffix has not annihilated its unknown source")
    image = fold.finish()
    pair_max = 2 * (base - 1)
    if image != image[::-1] or any(not 0 <= value <= pair_max for value in image):
        raise ValueError("certified suffix does not reconstruct a canonical pair field")
    return image


def reconstruct_pair_from_event_window(
    events: Sequence[Sequence[int]], *, base: int = 10
) -> tuple[int, ...]:
    """Recover an endpoint from H source-admitted events.

    Row shape and output-range checks alone do not authenticate a trajectory
    or prove its homogeneous-source erasure premise. This compiler/test
    helper must not issue production source authority.
    """
    base = int(base)
    horizon = event_memory_horizon(base)
    rows = tuple(tuple(map(int, event)) for event in events)
    if len(rows) != horizon:
        raise ValueError(f"expected exactly {horizon} event fields, got {len(rows)}")
    target_width = endpoint_width_from_event_window(rows)
    result = fold_forcing_events(rows, base=base)
    if len(result) != target_width:
        raise AssertionError((len(result), target_width))
    pair_max = 2 * (base - 1)
    if any(value > pair_max for value in result):
        raise ValueError("event window is not a valid canonical pair trajectory window")
    if result != result[::-1]:
        raise ValueError("event window reconstructed a nonsymmetric pair field")
    return result


def next_event_from_window(
    events: Sequence[Sequence[int]], *, base: int = 10
) -> tuple[int, ...]:
    """Exact bounded-order generator ``E_t=F(E_(t-H)..E_(t-1))``."""
    source = reconstruct_pair_from_event_window(events, base=base)
    target, growth = pair_step(source, base)
    return forcing_event(source, target, growth)


def reconstruct_pair_from_carry_window(
    carries: Sequence[Sequence[int]], *, base: int = 10
) -> tuple[int, ...]:
    """Exact endpoint pair from the previous H forward carry tracks only."""
    rows = tuple(tuple(map(int, row)) for row in carries)
    horizon = event_memory_horizon(base)
    if len(rows) != horizon:
        raise ValueError(f"expected exactly {horizon} carry fields, got {len(rows)}")
    return forcing_image_from_certified_carry_suffix(
        rows, source_width=len(rows[0]) - 1, base=base
    )


def next_carry_from_window(
    carries: Sequence[Sequence[int]], *, base: int = 10
) -> tuple[int, ...]:
    """Exact bounded-order binary generator ``C_t=G(C_(t-H)..C_(t-1))``."""
    source = reconstruct_pair_from_carry_window(carries, base=base)
    return carry_field(source, base=base)


__all__ = [
    "carry_field",
    "endpoint_width_from_event_window",
    "event_memory_horizon",
    "fold_forcing_events",
    "forcing_difference_alphabet",
    "forcing_event",
    "forcing_event_alphabet",
    "forcing_event_from_carry",
    "forcing_image_from_certified_carry_suffix",
    "growths_from_event_widths",
    "next_carry_from_window",
    "next_event_from_window",
    "pair_plane_bits",
    "pair_step",
    "reconstruct_pair_from_carry_window",
    "reconstruct_pair_from_event_window",
]
