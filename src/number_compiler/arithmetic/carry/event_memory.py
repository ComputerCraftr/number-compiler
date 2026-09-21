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
from collections.abc import Sequence
from math import comb


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


def _pair_step_with_carry(
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
            2 * source[i]
            + carry[i]
            + reverse[i + 1]
            - base * (carry[i + 1] + reverse[i])
            for i in range(d)
        )
    else:
        values = [0] * (d + 1)
        values[0] = source[0] + 1 - base * carry[1]
        values[d] = values[0]
        for i in range(1, d):
            values[i] = (
                source[i]
                + source[i - 1]
                + carry[i]
                + reverse[i]
                - base * (carry[i + 1] + reverse[i - 1])
            )
        out = tuple(values)
    if any(not 0 <= value <= 2 * (base - 1) for value in out):
        raise AssertionError((base, source, out))
    if out != out[::-1]:
        raise AssertionError("pair recurrence lost symmetry")
    return out, growth, carry


def pair_step(source: Sequence[int], base: int) -> tuple[tuple[int, ...], int]:
    """Canonical exact pair-field transition used by theorem/bootstrap compilers."""
    out, growth, _carry = _pair_step_with_carry(source, base)
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
    d = len(c) - 1
    growth = c[d]
    if not growth:
        return tuple(
            c[i] + c[d - i - 1] - base * (c[i + 1] + c[d - i]) for i in range(d)
        )
    out = [0] * (d + 1)
    out[0] = out[d] = 1 - base * c[1]
    for i in range(1, d):
        out[i] = c[i] + c[d - i] - base * (c[i + 1] + c[d - i + 1])
    return tuple(out)


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


def _transport_event(
    event: Sequence[int], *, growths_after_birth: Sequence[int], modulus: int
) -> tuple[int, ...]:
    event = tuple(map(int, event))
    growths = tuple(map(int, growths_after_birth))
    if any(g not in (0, 1) for g in growths):
        raise ValueError(growths)
    r = sum(growths)
    q = len(growths) - r
    scalar = pow(2, q, modulus)
    kernel = tuple((scalar * comb(r, m)) % modulus for m in range(r + 1))
    out = [0] * (len(event) + r)
    for i, value in enumerate(event):
        value %= modulus
        for m, coefficient in enumerate(kernel):
            out[i + m] = (out[i + m] + value * coefficient) % modulus
    return tuple(out)


def reconstruct_pair_from_event_window(
    events: Sequence[Sequence[int]], *, base: int = 10
) -> tuple[int, ...]:
    """Reconstruct the exact endpoint pair field from the previous H events."""
    base = int(base)
    horizon = event_memory_horizon(base)
    rows = tuple(tuple(map(int, event)) for event in events)
    if len(rows) != horizon:
        raise ValueError(f"expected exactly {horizon} event fields, got {len(rows)}")
    later_growths = growths_from_event_widths(rows)
    modulus = 1 << pair_plane_bits(base)
    target_width = endpoint_width_from_event_window(rows)
    out = [0] * target_width
    for j, event in enumerate(rows):
        tail = later_growths[j:]
        transported = _transport_event(event, growths_after_birth=tail, modulus=modulus)
        if len(transported) != target_width:
            raise AssertionError((j, len(transported), target_width))
        for i, value in enumerate(transported):
            out[i] = (out[i] + value) % modulus
    pair_max = 2 * (base - 1)
    if any(value > pair_max for value in out):
        raise ValueError("event window is not a valid canonical pair trajectory window")
    result = tuple(out)
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
    events = tuple(forcing_event_from_carry(row, base=base) for row in rows)
    return reconstruct_pair_from_event_window(events, base=base)


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
    "forcing_difference_alphabet",
    "forcing_event",
    "forcing_event_alphabet",
    "forcing_event_from_carry",
    "growths_from_event_widths",
    "next_carry_from_window",
    "next_event_from_window",
    "pair_plane_bits",
    "pair_step",
    "reconstruct_pair_from_carry_window",
    "reconstruct_pair_from_event_window",
]
