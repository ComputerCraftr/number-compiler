"""Sound, bounded low-2-adic *negative* filter for odd-macro discovery.

The eight-event production selector only admits motifs repeated among its
first eight *actual* odd events. Those exponents are determined by a finite
2-adic suffix whenever their consumed precision is below the precision of
that suffix. Proving no repetition in that suffix rules out a macro for every
source sharing it. An unresolved carry/valuation always returns ``True`` and
leaves the full exact issuer authoritative.

This filter never publishes an action, a period, or a successor, and does not
apply to explicit longer-motif discovery (which uses the regular issuer).
"""

from __future__ import annotations

PREFILTER_BITS = 64
PREFILTER_EVENTS = 8


def _may_repeat_low_suffix(
    low: int,
    bits: int,
    max_events: int,
    remaining_steps: int | None,
    max_residual_steps: int | None,
) -> bool:
    mask = (1 << bits) - 1
    r = low & mask
    precision = bits
    # An incoming centered source may be even. The exact selector consumes
    # its initial homogeneous even run before testing odd-to-odd motifs.
    if not (r & 1):
        if r == 0:
            return True  # v2(source) >= bits, no certified prefix
        shift = (r & -r).bit_length() - 1
        precision -= shift
        r = (pow(3, shift, 1 << precision) * (r >> shift)) % (1 << precision)
        if not r & 1:
            raise ArithmeticError("known even-prefix image did not become odd")

    first_odd = r
    prefix_steps = bits - precision
    available = (
        min(remaining_steps - prefix_steps, 4096)
        if remaining_steps is not None
        else None
    )
    if available is not None and available < 2:
        return False
    word: list[int] = []
    states: list[tuple[int, int]] = [(r, precision)]
    elapsed = 0
    for _ in range(max_events):
        modulus = 1 << precision
        numerator = (3 * r + 1) & (modulus - 1)
        if numerator == 0:
            return True  # next exponent needs a higher source bit
        exponent = (numerator & -numerator).bit_length() - 1
        if exponent <= 0 or exponent >= precision:
            return True
        word.append(exponent)
        elapsed += exponent
        if available is not None and elapsed > available:
            # The physical selector will not issue this complete event.
            # Conservatively leave cases with partial lookahead to the issuer.
            return True
        precision -= exponent
        modulus = 1 << precision
        # One odd event D -> 3**(a-1) * ((3D+1) >> a).
        r = (pow(3, exponent - 1, modulus) * ((3 * r + 1) >> exponent)) % modulus
        states.append((r, precision))
    # All candidate periods in the eight-event issuer are now determined.
    # A repeated prefix is necessary but not sufficient; its Hensel capacity
    # and the bounded residual must also permit two complete copies.
    for period in range(1, min(4, max_events // 2) + 1):
        if word[:period] != word[period : 2 * period]:
            continue
        if remaining_steps is None or max_residual_steps is None:
            return True
        if available is None:
            return True
        motif_extent = sum(word[:period])
        if motif_extent * 2 > available:
            continue
        after, known = states[period]
        difference = (first_odd - after) & ((1 << known) - 1)
        if difference == 0:
            return True  # v2(defect) is not determined by the low suffix
        v2difference = (difference & -difference).bit_length() - 1
        capacity = (motif_extent + v2difference - 1) // motif_extent
        copies = min(capacity, available // motif_extent)
        if copies >= 2 and (
            remaining_steps - prefix_steps - copies * motif_extent <= max_residual_steps
        ):
            return True
    return False


def might_have_odd_macro_low_suffix(
    centered_low: int,
    *,
    bits: int = PREFILTER_BITS,
    max_events: int = PREFILTER_EVENTS,
    remaining_steps: int | None = None,
    max_residual_steps: int | None = None,
) -> bool:
    """False is a *proof* of a selector miss; True demands exact discovery.

    The input is only the lowest ``bits`` of the complete centered source.
    No finite harmonic or residue class is promoted to a branch certificate.
    """
    if (
        type(centered_low) is not int
        or centered_low < 0
        or type(bits) is not int
        or not 8 <= bits <= 256
        or type(max_events) is not int
        or not 2 <= max_events <= 8
        or (
            remaining_steps is not None
            and (type(remaining_steps) is not int or remaining_steps < 0)
        )
        or (
            max_residual_steps is not None
            and (type(max_residual_steps) is not int or max_residual_steps < 0)
        )
    ):
        raise ValueError("invalid exact low-suffix prefilter input")
    return _may_repeat_low_suffix(
        centered_low & ((1 << bits) - 1),
        bits,
        max_events,
        remaining_steps,
        max_residual_steps,
    )


def source_might_have_odd_macro(source: int) -> bool:
    """Convenient full-source facade for independent tests and diagnostics."""
    if type(source) is not int or source <= 0:
        raise ValueError("odd macro source must be a positive integer")
    return might_have_odd_macro_low_suffix(source & ((1 << PREFILTER_BITS) - 1))


__all__ = (
    "PREFILTER_BITS",
    "PREFILTER_EVENTS",
    "might_have_odd_macro_low_suffix",
    "source_might_have_odd_macro",
)
