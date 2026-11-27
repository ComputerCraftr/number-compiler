"""Apply the source-certified H12 forcing image to an exact Q19 continuation."""

from collections.abc import Callable, Generator
from contextlib import contextmanager, nullcontext
from heapq import merge
from typing import Final, cast

from number_compiler.arithmetic.carry.event_memory import pair_plane_bits
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
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
    """Evaluate the guarded H12 image using the packed homogeneous quotient.

    The zero source has a closed all-horizon action. Nonzero unknown carry
    rows still require their exact transition; the packed executor consumes
    any admitted carry-free prefix without constructing those rows.
    """
    if source.count == 0 and source.center == 0:
        _image_guard(source, source)
        return source
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


def _physical_landmarks(
    value: object, offset: int
) -> tuple[tuple[int, tuple[int, int, int | None]], ...]:
    """Read one issuer-owned bundle of physical dyadic checkpoints."""
    if value is MISSING:
        return ()
    if not is_exact_object_tuple(value):
        raise ValueError("invalid issued Q19 physical landmarks")
    previous = 0
    for item in value:
        if not is_exact_object_tuple(item) or len(item) != 2:
            raise ValueError("invalid issued Q19 physical landmark")
        age, raw = item
        if (
            type(age) is not int
            or age <= previous
            or (age + offset) & (age + offset - 1)
        ):
            raise ValueError("invalid issued Q19 physical landmark age")
        if not is_exact_object_tuple(raw) or len(raw) != 3:
            raise ValueError("invalid issued Q19 physical landmark payload")
        pairs, count, center = raw
        if (
            type(pairs) is not int
            or pairs < 0
            or type(count) is not int
            or count < 0
            or pairs.bit_length() > 6 * count
            or (
                center is not None and (type(center) is not int or not 0 <= center <= 9)
            )
            or (count == 0 and center is None)
            or (count > 0 and pairs & 63 == 0)
        ):
            raise ValueError("invalid issued Q19 physical landmark payload")
        previous = age
    return cast(tuple[tuple[int, tuple[int, int, int | None]], ...], value)


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
def _continuation_scratch(
    ledger: ResourceLedger | None, owner: int | None, shared_cache: bool
) -> Generator[LedgerReservation | None, None, None]:
    """Charge staged checkpoints even when the caller has no ledger."""
    temporary = ledger is None and shared_cache
    if temporary:
        ledger = ResourceLedger()
        owner = ledger.register("q19-continuation", "checkpoint-scratch")
    if ledger is None:
        yield None
        return
    assert owner is not None
    try:
        with LedgerReservation(ledger, owner) as scratch:
            yield scratch
    finally:
        if temporary:
            ledger.mark_disposed(owner)


@contextmanager
def _segment(
    lease: CacheLease | None,
    source: PackedQ19,
    steps: int,
    before_step: Callable[[int, int], None],
    *,
    carry_window: bool = False,
    scratch: LedgerReservation | None = None,
    landmark_offset: int = 0,
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
    pending: list[tuple[int, tuple[int, int, int | None], bool, int]] = []
    landmark_key = (*source_key, -2, landmark_offset)
    raw_physical: object = MISSING
    physical_landmarks: tuple[tuple[int, tuple[int, int, int | None]], ...] = ()
    try:
        if carry_window:
            # This guard must not be replaced by a bare same-residue or carry-mask
            # return. Its source-to-image certificate is genuinely physical.
            target = physical_carry_image(source, before_step)
        elif lease is None or steps == 0:
            target = source.advance_repeated(steps, before_step=before_step)
        else:
            raw_physical = (
                lease.get_issued(landmark_key, _CONTINUATION_ISSUER)
                if landmark_offset
                else MISSING
            )
            physical_landmarks = _physical_landmarks(raw_physical, landmark_offset)
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
                # Both local dyadic steps and physical dyadic checkpoints
                # after the authenticated H12 prefix are valid.  The latter
                # lets a warm N+delta query answer physical N=2^k without
                # replaying a non-power-of-two suffix from the H12 boundary.
                physical_powers = (
                    (
                        age - landmark_offset
                        for age in _dyadic_durations(steps + landmark_offset)
                        if landmark_offset < age <= steps + landmark_offset
                    )
                    if landmark_offset
                    else ()
                )
                for age in merge(
                    _dyadic_durations(steps), physical_powers, reverse=True
                ):
                    known = lease.get_issued((*source_key, age), _CONTINUATION_ISSUER)
                    if known is MISSING:
                        known = next(
                            (
                                payload
                                for item_age, payload in physical_landmarks
                                if item_age == age
                            ),
                            MISSING,
                        )
                    if known is not MISSING:
                        frame = PackedQ19.from_record(known)
                        start = age
                        break
            reused = start
            position = start
            while position < steps:
                next_power = 1 << position.bit_length()
                next_physical_power = (
                    (1 << (position + landmark_offset).bit_length()) - landmark_offset
                    if landmark_offset
                    else next_power
                )
                stop = min(steps, next_power, next_physical_power)
                frame = frame.advance_repeated(stop - position, before_step=before_step)
                position = stop
                local = position & (position - 1) == 0
                physical = bool(
                    landmark_offset
                    and (position + landmark_offset) & (position + landmark_offset - 1)
                    == 0
                )
                if local or physical:
                    # Retain source-authenticated local and physical dyadic
                    # landmarks. The image is a complete checked Q19 state,
                    # not an occurrence history or a future period guess.
                    assert scratch is not None
                    nodes = 4 + (frame.pairs.bit_length() + 63) // 64
                    try:
                        scratch.reserve(entries=1, nodes=nodes)
                    except BlockContextBudgetExceeded:
                        if not local:
                            continue
                        discarded = tuple(item for item in pending if item[2])
                        if not discarded:
                            raise
                        scratch.release(
                            entries=len(discarded),
                            nodes=sum(item[3] for item in discarded),
                        )
                        pending[:] = (item for item in pending if not item[2])
                        scratch.reserve(entries=1, nodes=nodes)
                    pending.append((position, _record(frame), not local, nodes))
            target = frame

        yield target, reused
        if lease is not None:
            for duration, payload, is_optional, _nodes in pending:
                if not is_optional:
                    lease.put_issued(
                        (*source_key, duration), payload, _CONTINUATION_ISSUER
                    )
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
            staged_landmarks = tuple(
                (age, payload)
                for age, payload, is_optional, _ in pending
                if is_optional
            )
            if staged_landmarks and not carry_window:
                assert scratch is not None
                try:
                    scratch.reserve(
                        entries=len(physical_landmarks) + len(staged_landmarks) + 1,
                        nodes=len(physical_landmarks) + len(staged_landmarks) + 1,
                    )
                except BlockContextBudgetExceeded:
                    pass
                else:
                    merged = dict(physical_landmarks)
                    merged.update(staged_landmarks)
                    bundle = tuple(sorted(merged.items()))

                    def update_landmarks(old: object) -> tuple[object, None]:
                        # Do not overwrite a concurrent receiving source's
                        # longer set of already-issued landmarks.
                        if old != raw_physical:
                            return MISSING, None
                        return bundle, None

                    lease.update_issued(
                        landmark_key, _CONTINUATION_ISSUER, update_landmarks
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
    if source.count == 0 and source.center == 0:
        # Exact self-loop, not a discovered occurrence/frontier. Report its
        # represented span as reused rather than charging physical ticks.
        yield source, steps
        return
    with (
        _continuation_scratch(ledger, scratch_owner, shared_cache) as scratch,
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
            with _segment(
                lease,
                image,
                remaining,
                before_step,
                scratch=scratch,
                landmark_offset=DECIMAL_CARRY_WINDOW,
            ) as (
                target,
                suffix_reused,
            ):
                yield target, prefix_reused + suffix_reused
