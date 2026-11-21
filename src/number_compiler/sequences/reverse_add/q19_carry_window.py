"""Apply the source-certified H12 forcing image to an exact Q19 continuation."""

from collections.abc import Callable, Generator
from contextlib import contextmanager, nullcontext
from typing import Final

from number_compiler.arithmetic.carry.event_memory import pair_plane_bits
from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.owned_memo import LedgerReservation
from number_compiler.resources.process_cache import (
    MISSING,
    CacheLease,
    get_process_cache,
)
from number_compiler.sequences.reverse_add.q19_broadword_publisher import PackedQ19

DECIMAL_CARRY_WINDOW = 12


def physical_carry_image(
    source: PackedQ19, before_step: Callable[[int, int], None] | None = None
) -> PackedQ19:
    """Evaluate reverse_q19_twelve_image_exact on its packed source representative."""
    image = source.advance_repeated(DECIMAL_CARRY_WINDOW, before_step=before_step)
    # Each physical step grows by zero or one. The total width change counts
    # births, so the annihilation guard needs neither carry rows nor a trace.
    _image_guard(source, image)
    return image


_CONTINUATION_KIND: Final[str] = "q19-complete-pair-continuation-v2"
_CONTINUATION_ISSUER = object()


def _record(source: PackedQ19) -> tuple[int, int, int | None]:
    return source.pairs, source.count, source.center


def _frontier_record(value: object) -> tuple[int, tuple[object, object, object]]:
    if not is_exact_object_tuple(value) or len(value) != 4:
        raise ValueError("invalid issued Q19 frontier")
    age, pairs, count, center = value
    if type(age) is not int or age < 1:
        raise ValueError("invalid issued Q19 frontier duration")
    return age, (pairs, count, center)


def _image_guard(source: PackedQ19, target: PackedQ19) -> None:
    # An exact cached endpoint, even one issued by the direct route, must not
    # inherit H12 authority unless this physical birth guard holds.
    births = target.width - source.width
    if DECIMAL_CARRY_WINDOW - births < pair_plane_bits(10):
        raise ValueError("carry suffix has not annihilated its unknown source")


def _dyadic_durations(steps: int) -> Generator[int, None, None]:
    power = 1 << (steps.bit_length() - 1)
    while power:
        yield power
        power >>= 1


@contextmanager
def _segment(
    lease: CacheLease | None,
    source: PackedQ19,
    steps: int,
    before_step: Callable[[int, int], None],
    *,
    carry_window: bool = False,
    scratch: LedgerReservation | None = None,
) -> Generator[tuple[PackedQ19, int], None, None]:
    """Issue exact source-selected endpoints, never an inferred temporal period.

    A single furthest frontier and O(log N) dyadic landmarks are retained per
    complete Q19 source. A query can restart at a previously certified prefix;
    for a cold query no physical generation is skipped. Cache publications
    happen only after the receiving context exits successfully. Neither
    digit/occurrence history nor an unproved weighted period is retained.
    """
    source_key = _record(source)
    key = (*source_key, steps)
    prior = MISSING if lease is None else lease.get_issued(key, _CONTINUATION_ISSUER)
    if prior is not MISSING:
        target = PackedQ19.from_record(prior)
        if carry_window:
            _image_guard(source, target)
        yield target, steps
        return

    reused = 0
    pending: list[tuple[int, tuple[int, int, int | None]]] = []
    try:
        if carry_window:
            # This guard must not be replaced by a bare same-residue or carry-mask
            # return. Its source-to-image certificate is genuinely physical.
            target = physical_carry_image(source, before_step)
        elif lease is None or steps == 0:
            target = source.advance_repeated(steps, before_step=before_step)
        else:
            frontier = lease.get_issued((*source_key, -1), _CONTINUATION_ISSUER)
            start = 0
            frame = source
            if frontier is not MISSING:
                age, state = _frontier_record(frontier)
                if age <= steps:
                    frame = PackedQ19.from_record(state)
                    start = age
            # When asking for a smaller horizon than the furthest retained state,
            # use the largest stored binary landmark that fits. These are full
            # semantic Q19 states, not materialized physical occurrence histories.
            if start == 0:
                for age in _dyadic_durations(steps):
                    known = lease.get_issued((*source_key, age), _CONTINUATION_ISSUER)
                    if known is not MISSING:
                        frame = PackedQ19.from_record(known)
                        start = age
                        break
            reused = start
            position = start
            while position < steps:
                next_power = 1 << position.bit_length()
                stop = min(steps, next_power)
                frame = frame.advance_repeated(stop - position, before_step=before_step)
                position = stop
                if position & (position - 1) == 0 and scratch is not None:
                    scratch.reserve(
                        entries=1, nodes=4 + (frame.pairs.bit_length() + 63) // 64
                    )
                    pending.append((position, _record(frame)))
            target = frame

        yield target, reused
        if lease is not None:
            for duration, payload in pending:
                lease.put_issued((*source_key, duration), payload, _CONTINUATION_ISSUER)
            lease.put_issued(key, _record(target), _CONTINUATION_ISSUER)
            if steps > 0:
                # Atomic max-frontier update under the source-qualified lease. A
                # later shorter request cannot overwrite a longer certified state.
                def advance_frontier(old: object) -> tuple[object, None]:
                    if old is MISSING:
                        return (steps, *_record(target)), None
                    previous, _ = _frontier_record(old)
                    if previous >= steps:
                        return MISSING, None
                    return (steps, *_record(target)), None

                lease.update_issued(
                    (*source_key, -1), _CONTINUATION_ISSUER, advance_frontier
                )
    finally:
        pending.clear()


@contextmanager
def completed_continuation(
    source: PackedQ19,
    steps: int,
    *,
    carry_window: bool = False,
    shared_cache: bool,
    before_step: Callable[[int, int], None],
    ledger: ResourceLedger | None = None,
    scratch_owner: int | None = None,
) -> Generator[tuple[PackedQ19, int], None, None]:
    """Compose the source-to-image binding with the unique image continuation.

    A complete direct action can answer immediately. On the H12 route the
    prefix is reusable across horizons, and its continuation across sources.
    Publish misses after the receiving consumer succeeds.
    """
    if type(source) is not PackedQ19 or type(steps) is not int or steps < 0:
        raise ValueError(
            "a continuation requires a complete Q19 state and finite duration"
        )
    if carry_window and steps < DECIMAL_CARRY_WINDOW:
        raise ValueError("a carry-window continuation needs twelve physical steps")
    if (ledger is None) != (scratch_owner is None):
        raise ValueError("checkpoint reservation requires a ledger and owner")
    with (
        (
            LedgerReservation(ledger, scratch_owner)
            if ledger is not None and scratch_owner is not None
            else nullcontext(None)
        ) as scratch,
        (
            get_process_cache().acquire("reverse-add", _CONTINUATION_KIND, (10,))
            if shared_cache
            else nullcontext(None)
        ) as lease,
    ):
        if not carry_window or steps == DECIMAL_CARRY_WINDOW:
            with _segment(
                lease,
                source,
                steps,
                before_step,
                carry_window=carry_window,
                scratch=scratch,
            ) as result:
                yield result
            return
        if lease is not None:
            key = (source.pairs, source.count, source.center, steps)
            whole = lease.get_issued(key, _CONTINUATION_ISSUER)
            if whole is not MISSING:
                yield PackedQ19.from_record(whole), steps
                return

        with _segment(
            lease,
            source,
            DECIMAL_CARRY_WINDOW,
            before_step,
            carry_window=True,
            scratch=scratch,
        ) as (image, prefix_reused):
            remaining = steps - DECIMAL_CARRY_WINDOW
            if remaining == DECIMAL_CARRY_WINDOW and image == source:
                yield image, prefix_reused + remaining
                return
            with _segment(lease, image, remaining, before_step, scratch=scratch) as (
                target,
                suffix_reused,
            ):
                yield target, prefix_reused + suffix_reused
