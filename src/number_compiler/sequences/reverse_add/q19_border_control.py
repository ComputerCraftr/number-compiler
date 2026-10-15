"""Source-certified finite reverse/add growth tapes from edge relations.

The k-digit prefix/suffix relation nondeterministically includes *both*
interior carry values after its first exact source transition. Whenever all
outcomes have the same growth bit, that bit is universally certified without
constructing any intermediate Q19 pair occurrence. The original input uses
its exact source digits; a later issued pair root supplies the already-issued
width transition and exact normalized output digits for the next edge step.

This theorem gives FINITE, source-bound control prefixes; it is not a proof
that the observed word continues periodically or controls arbitrary depths.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Literal

from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

from ._q19_issuance import issue_q19_record

if TYPE_CHECKING:
    from .q19_occurrence import ReversePairOutputOccurrence
    from .q19_output import ReversePairQ19OutputOwner

_ISSUER = object()


class BoundaryControlNotAuthorized(ValueError):
    """The finite boundary relation cannot certify every requested event."""


def _reverse_fixed(word: int, width: int) -> int:
    reverse = 0
    for _ in range(width):
        reverse = reverse * 10 + word % 10
        word //= 10
    return reverse


@dataclass(frozen=True, slots=True)
class CertifiedBorderGrowth:
    """Exact physical growth word universally forced by the k-digit relation."""

    owner: ReversePairQ19OutputOwner
    source: ReversePairOutputOccurrence
    growth_word: tuple[int, ...]
    window_digits: int
    max_visited_states: int
    source_pair_inspections: int = 0
    physical_growth_certified: Literal[True] = True
    full_integer_certified: Literal[False] = False
    _seal: object = field(default=None, repr=False, compare=False)
    _binding: tuple[object, ...] = field(default=(), repr=False, compare=False)

    def _snapshot(self) -> tuple[object, ...]:
        return (
            self.owner,
            self.source,
            self.growth_word,
            self.window_digits,
            self.max_visited_states,
            self.source_pair_inspections,
            self.physical_growth_certified,
            self.full_integer_certified,
        )

    def __post_init__(self) -> None:
        if (
            self._seal is not _ISSUER
            or self._binding != self._snapshot()
            or type(self.max_visited_states) is not int
            or self.max_visited_states < 1
            or type(self.source_pair_inspections) is not int
            or self.source_pair_inspections < 0
            or self.physical_growth_certified is not True
            or self.full_integer_certified is not False
        ):
            raise ValueError(
                "border growth certificate must be issued by a live Q19 owner"
            )
        self.owner._issuance_registry.validate_border(self)

    @property
    def final_width(self) -> int:
        """Exact future integer width for the finite certified growth tape."""
        self.validate(self.owner, self.source)
        return self.source.pair_width + sum(self.growth_word)

    def validate(
        self, owner: ReversePairQ19OutputOwner, source: ReversePairOutputOccurrence
    ) -> None:
        if owner is not self.owner or source is not self.source:
            raise ValueError("border growth certificate belongs to a different source")
        if self._seal is not _ISSUER or self._binding != self._snapshot():
            raise ValueError("border growth certificate was changed")
        owner._issuance_registry.validate_border(self)
        owner.validate_issued_occurrence(source)


def certify_border_growth(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    *,
    steps: int,
    window_digits: int = 2,
    max_states: int = 8192,
) -> CertifiedBorderGrowth:
    """Certify one finite growth itinerary without future source evaluation.

    For the original Q19 pair source, the known original digits authorize the
    first growth event. For any later issued pair source S_n, the pair carry
    terminal authorizes the first growth event and Q19's pointed digit fold
    reconstructs the exact X_(n+1) border. Subsequent events are proved by
    the same all-interior-carry finite edge relation, not by enumerating the
    intermediate source words.
    """
    owner.validate_issued_occurrence(source)
    if type(steps) is not int or not 1 <= steps <= 65536:
        raise ValueError("positive bounded finite edge horizon required")
    if type(window_digits) is not int or not 1 <= window_digits <= 12:
        raise ValueError("edge windows must have width 1..12")
    if type(max_states) is not int or not 1 <= max_states <= 1000000:
        raise ValueError("invalid bounded boundary-state budget")
    cached = owner._issuance_registry.lookup_border(source, steps, window_digits)
    if cached is not None:
        cached.validate(owner, source)
        if max(cached.max_visited_states, cached.source_pair_inspections) > max_states:
            raise BoundaryControlNotAuthorized(
                "retained certificate exceeds the requested state budget"
            )
        return cached
    if steps == 1:
        owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_ATTEMPTS)
        growth = source.output_width - source.pair_width
        if growth not in (0, 1):
            raise BoundaryControlNotAuthorized(
                "issued Q19 root has no exact one-bit width transition"
            )
        return _issue_border(owner, source, (growth,), window_digits, 1)
    # Reserve the maximum live frontier, the current frontier, the finite
    # output word, and the source scan before allocating any of them.  This is
    # temporary scratch: all sets and the word builder die before the scope
    # releases their charge, including on an undecidable/refused edge.
    width = len(owner._digits) if source is owner.initial else source.output_width
    owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_ATTEMPTS)
    # Live edge/frontier memory depends on the state budget and the actual
    # inspected reset suffix, not the potentially gigantic virtual SLP width.
    scratch_nodes = 2 * max_states + steps + 6 * window_digits + min(width, max_states)
    with owner.ledger.reservation(owner._scratch_owner, nodes=scratch_nodes):
        return _certify_reserved(
            owner,
            source,
            steps=steps,
            window_digits=window_digits,
            max_states=max_states,
        )


def _certify_reserved(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    *,
    steps: int,
    window_digits: int,
    max_states: int,
) -> CertifiedBorderGrowth:
    digits = owner._digits if source is owner.initial else None
    # A later issued pair root S_n emits the digits of X_(n+1), not X_n.
    # Its first growth is already the *terminal carry* of S_n, which is
    # authenticated by the Q19 source metadata. Certify the remaining
    # `steps-1` decisions from the emitted successor's exact edge digits.
    first_growth = (
        () if digits is not None else (source.output_width - source.pair_width,)
    )
    width = len(digits) if digits is not None else source.output_width
    k = window_digits
    if len(first_growth) == steps:
        return _issue_border(owner, source, first_growth, k, 1)
    if width < 2 * k + 1:
        raise BoundaryControlNotAuthorized(
            "source too narrow for independent edge tiles"
        )
    base = 10**k
    # Original digits and later Q19-issued digits are both LSD-first.
    # Random-access Q19 digits do not materialize an enormous source word.
    digit_at = (
        (lambda i: digits[i])
        if digits is not None
        else (lambda i: owner.digit(source, i))
    )
    prefix = 0
    for i in range(width - 1, width - k - 1, -1):
        prefix = 10 * prefix + digit_at(i)
    suffix = sum(digit_at(i) * 10**i for i in range(k))
    if not base // 10 <= prefix < base:
        raise BoundaryControlNotAuthorized(
            "source prefix does not fit an active k-digit tile"
        )
    # Carry c_(w-k) is the most recent non-EQ reset in the actual source.
    # Scan *backwards* only to the first decisive pair.  A long 9-wire
    # remains exact and the scan is counted, never guessed from the border.
    incoming = 0
    source_pair_inspections = 0
    for examined, i in enumerate(range(width - k - 1, -1, -1)):
        if examined >= max_states:
            raise BoundaryControlNotAuthorized(
                "unresolved source 9-wire exceeds the reset probe budget"
            )
        owner.ledger.bump(
            _reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_SOURCE_PAIR_INSPECTIONS
        )
        source_pair_inspections += 1
        pair = digit_at(i) + digit_at(width - 1 - i)
        if pair != 9:
            incoming = int(pair > 9)
            break

    tiles: set[tuple[int, int]] = {(prefix, suffix)}
    bits: list[int] = []
    visited = 1
    for tick in range(steps - len(first_growth)):
        owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_STEPS)
        future: set[tuple[int, int]] = set()
        possibilities: set[int] = set()
        for high_tile, low_tile in tiles:
            owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_STATE_VISITS)
            reflected_high = _reverse_fixed(high_tile, k)
            reflected_low = _reverse_fixed(low_tile, k)
            new_low = (low_tile + reflected_high) % base
            for carry in (incoming,) if tick == 0 else (0, 1):
                owner.ledger.bump(
                    _reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_EDGE_TRANSITIONS
                )
                high = high_tile + reflected_low + carry
                growth = int(high >= base)
                next_high = high // 10 if growth else high
                if not base // 10 <= next_high < base:
                    raise BoundaryControlNotAuthorized(
                        f"unresolved leading width at border step {tick}"
                    )
                possibilities.add(growth)
                future.add((next_high, new_low))
                if len(future) > max_states:
                    raise BoundaryControlNotAuthorized(
                        f"boundary state budget exceeded at step {tick}"
                    )
        visited = max(visited, len(future))
        if len(possibilities) != 1:
            raise BoundaryControlNotAuthorized(
                f"interior carry alternatives disagree on growth at step {tick}; "
                f"certified prefix={''.join(map(str, bits))}"
            )
        bits.append(possibilities.pop())
        tiles = future
    return _issue_border(
        owner,
        source,
        first_growth + tuple(bits),
        k,
        visited,
        source_pair_inspections=source_pair_inspections,
    )


def _issue_border(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    word: tuple[int, ...],
    k: int,
    visited: int,
    *,
    source_pair_inspections: int = 0,
) -> CertifiedBorderGrowth:
    record = object.__new__(CertifiedBorderGrowth)
    attrs = {
        "owner": owner,
        "source": source,
        "growth_word": word,
        "window_digits": k,
        "max_visited_states": visited,
        "source_pair_inspections": source_pair_inspections,
        "physical_growth_certified": True,
        "full_integer_certified": False,
    }
    issue_q19_record(record, attrs, _ISSUER)
    retained = owner._issuance_registry.retain_border(record)
    try:
        retained.__post_init__()
    except BaseException:
        owner._issuance_registry.discard_border(record)
        raise
    owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_CERTIFICATES)
    return retained


__all__ = [
    "BoundaryControlNotAuthorized",
    "CertifiedBorderGrowth",
    "certify_border_growth",
]
