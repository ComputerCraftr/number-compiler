"""Apply the source-certified H12 forcing image to an exact Q19 continuation."""

from collections.abc import Callable, Generator
from contextlib import contextmanager, nullcontext
from typing import Final

from number_compiler.arithmetic.carry.event_memory import pair_plane_bits
from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
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
    births = image.width - source.width
    if DECIMAL_CARRY_WINDOW - births < pair_plane_bits(10):
        raise ValueError("carry suffix has not annihilated its unknown source")
    return image


_CONTINUATION_KIND: Final[str] = "q19-complete-pair-continuation-v1"
_CONTINUATION_ISSUER = object()


def _frontier_record(record: object) -> tuple[int, PackedQ19]:
    if not is_exact_object_tuple(record) or len(record) != 4:
        raise ValueError("malformed Q19 continuation frontier")
    steps, pairs, count, center = record
    if type(steps) is not int or steps < 0:
        raise ValueError("malformed Q19 continuation duration")
    return steps, PackedQ19.from_record((pairs, count, center))


@contextmanager
def _frontier(
    lease: CacheLease | None,
    source: PackedQ19,
    steps: int,
    before_step: Callable[[int, int], None],
) -> Generator[tuple[PackedQ19, int], None, None]:
    """Resume the latest completed continuation of this exact Q19 image."""
    if lease is None:
        yield source.advance_repeated(steps, before_step=before_step), 0
        return
    key = (source.pairs, source.count, source.center, "frontier")
    prior = lease.get_issued(key, _CONTINUATION_ISSUER)
    reused = 0
    start = source
    if prior is not MISSING:
        prior_steps, prior_target = _frontier_record(prior)
        if prior_steps <= steps:
            reused, start = prior_steps, prior_target
    target = (
        start
        if reused == steps
        else start.advance_repeated(steps - reused, before_step=before_step)
    )
    yield target, reused

    def update(previous: object) -> tuple[object, None]:
        if previous is not MISSING:
            prior_steps, _ = _frontier_record(previous)
            if prior_steps >= steps:
                return MISSING, None
        return (steps, target.pairs, target.count, target.center), None

    lease.update_issued(key, _CONTINUATION_ISSUER, update)


@contextmanager
def _segment(
    lease: CacheLease | None,
    source: PackedQ19,
    steps: int,
    before_step: Callable[[int, int], None],
    *,
    carry_window: bool = False,
) -> Generator[tuple[PackedQ19, int], None, None]:
    key = (source.pairs, source.count, source.center, steps)
    prior = MISSING if lease is None else lease.get_issued(key, _CONTINUATION_ISSUER)
    if prior is not MISSING:
        yield PackedQ19.from_record(prior), steps
        return
    target = (
        physical_carry_image(source, before_step)
        if carry_window
        else source.advance_repeated(steps, before_step=before_step)
    )
    yield target, 0
    if lease is not None:
        lease.put_issued(
            key, (target.pairs, target.count, target.center), _CONTINUATION_ISSUER
        )


@contextmanager
def completed_continuation(
    source: PackedQ19,
    steps: int,
    *,
    carry_window: bool = False,
    shared_cache: bool,
    before_step: Callable[[int, int], None],
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
    with (
        get_process_cache().acquire("reverse-add", _CONTINUATION_KIND, (10,))
        if shared_cache
        else nullcontext(None)
    ) as lease:
        if not carry_window or steps == DECIMAL_CARRY_WINDOW:
            with _segment(
                lease, source, steps, before_step, carry_window=carry_window
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
            lease, source, DECIMAL_CARRY_WINDOW, before_step, carry_window=True
        ) as (image, prefix_reused):
            remaining = steps - DECIMAL_CARRY_WINDOW
            if remaining == DECIMAL_CARRY_WINDOW and image == source:
                yield image, prefix_reused + remaining
                return
            with _frontier(lease, image, remaining, before_step) as (
                target,
                suffix_reused,
            ):
                yield target, prefix_reused + suffix_reused
