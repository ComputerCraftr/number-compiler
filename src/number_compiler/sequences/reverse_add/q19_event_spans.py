"""First-positive palindrome summaries over adjacent, exact Q19 spans."""

from __future__ import annotations

from typing import Final

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.process_cache import (
    MISSING,
    CacheLease,
    get_process_cache,
)
from number_compiler.sequences.reverse_add.q19_broadword_publisher import PackedQ19
from number_compiler.sequences.reverse_add.temporal_port_quotient import (
    decimal_width_upper_bound,
    q19_transition_scratch_nodes,
)

_EVENT_CACHE_KIND: Final[str] = "q19-first-palindrome-v1"
_ISSUER = object()
_LEAF_TICKS = 16
DEFAULT_EVENT_STEP_BUDGET = 4096


# A positive offset settles a hit. Only complete absence carries a successor.
_Coverage = int | PackedQ19


def scan_palindrome_span(source: PackedQ19, span: int) -> _Coverage:
    """Return the first positive hit or the full Q19 endpoint after an absent span."""
    if type(span) is not int or span < 0:
        raise ValueError("invalid palindrome span")
    frame = source
    for offset in range(1, span + 1):
        if frame.next_is_palindrome():
            return offset
        frame, _ = frame.advance()
    return frame


def _published(lease: CacheLease, source: PackedQ19, span: int) -> _Coverage | None:
    value = lease.get_issued((source.pairs, source.count, source.center, span), _ISSUER)
    if value is MISSING:
        return None
    if type(value) is int and 1 <= value <= span:
        return value
    return PackedQ19.from_record(value)


def _resolve(lease: CacheLease, source: PackedQ19, horizon: int) -> _Coverage:
    # The explicit stack visits the right child only after left absence. It
    # never discovers either child of an already-published parent.
    work: list[tuple[PackedQ19, int, int]] = [(source, horizon, 0)]
    result: _Coverage = source
    while work:
        frame, span, phase = work.pop()
        half = span // 2
        if phase == 0:
            found = _published(lease, frame, span)
            if found is not None:
                result = found
                continue
            if span > _LEAF_TICKS:
                work.append((frame, span, 1))
                work.append((frame, half, 0))
                continue
            result = scan_palindrome_span(frame, span)
        elif phase == 1 and isinstance(result, PackedQ19):
            work.append((frame, span, 2))
            work.append((result, span - half, 0))
            continue
        elif phase == 2 and isinstance(result, int):
            result += half
        lease.put_issued(
            (frame.pairs, frame.count, frame.center, span),
            result
            if isinstance(result, int)
            else (result.pairs, result.count, result.center),
            _ISSUER,
        )
    return result


def earliest_palindrome(
    source: PackedQ19, horizon: int, *, shared_cache: bool
) -> int | None:
    if type(horizon) is not int or horizon < 0:
        raise ValueError("invalid palindrome horizon")
    if not shared_cache or horizon <= _LEAF_TICKS:
        result = scan_palindrome_span(source, horizon)
    else:
        with get_process_cache().acquire(
            "reverse-add", _EVENT_CACHE_KIND, (10,)
        ) as lease:
            result = _resolve(lease, source, horizon)
    return result if isinstance(result, int) else None


def search_physical_prefix(
    seed: int, horizon: int, ledger: ResourceLedger, *, shared_cache: bool
) -> int | None:
    """Search an admitted decimal source within the event budget."""
    if horizon == 0:
        return None
    covered = min(horizon, DEFAULT_EVENT_STEP_BUDGET)
    owner = ledger.register("reverse-palindrome-search", "scratch")
    with ledger.reservation(
        owner,
        nodes=q19_transition_scratch_nodes(
            decimal_width_upper_bound(seed) + covered + 1
        ),
    ):
        frame = PackedQ19.from_digits(digits_lsd(seed, 10))
        hit = earliest_palindrome(frame, covered, shared_cache=shared_cache)
    if hit is None and covered < horizon:
        from number_compiler.arithmetic.contracts.unresolved_term import (
            UnresolvedSequenceTerm,
        )

        raise UnresolvedSequenceTerm(
            horizon,
            covered,
            "decimal-q19-first-palindrome",
            "palindrome search reached its bounded physical prefix",
        )
    return hit
