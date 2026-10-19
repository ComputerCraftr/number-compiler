"""Radix observers must not reconstruct future prefixes as carry vectors."""

from __future__ import annotations

import sys
from collections.abc import Callable
from inspect import unwrap
from types import FrameType
from typing import Never, cast

import pytest

from number_compiler.projection.lazy_radix import RadixProjection, collatz_radix_digit
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


def _prefix_trace(
    filename: str, prefix: int
) -> Callable[[FrameType, str, object], None]:
    def trace(frame: FrameType, event: str, argument: object) -> None:
        if event != "call":
            return
        caller = frame.f_back
        if caller is None or caller.f_code.co_filename != filename:
            return
        for value in tuple(caller.f_locals.values()):
            if not isinstance(value, (list, tuple)) or len(value) < 32:
                continue
            if all(type(digit) is int and 0 <= digit < 3 for digit in value):
                decoded = sum(digit * 3**index for index, digit in enumerate(value))
                assert decoded != prefix, (
                    "radix carry workspace contains an exact future prefix"
                )
        return

    return trace


@pytest.mark.validation
def test_radix_projection_never_holds_a_whole_endpoint_prefix_buffer() -> None:
    """Trace the public q=64 projection while enforcing the no-prefix invariant."""
    # The requested high ternary digit is one. The old division pipeline held
    # every ternary digit of the 101-bit unrequested prefix immediately before
    # its last input bit, even though it erased final remainders afterward.
    term = PoweredCollatzTerm(3**63, 1)
    prefix = (3**64 + 1) // 2
    assert prefix.bit_length() > 64
    previous = sys.gettrace()
    sys.settrace(
        _prefix_trace(unwrap(collatz_radix_digit).__code__.co_filename, prefix)
    )
    try:
        assert collatz_radix_digit(term, 3, 64) == 1
    finally:
        sys.settrace(previous)


def test_prefix_trace_rejects_the_old_pipeline_before_its_final_input() -> None:
    endpoint = 3**64 + 1

    def source_bit(position: int) -> int:
        return (endpoint >> position) & 1

    def old_pipeline() -> int:
        carries = [0] * 65
        for position in range(endpoint.bit_length() - 1, -1, -1):
            bit = source_bit(position)
            for stage in range(65):
                value = 2 * carries[stage] + bit
                bit, carries[stage] = divmod(value, 3)
        result = carries[-1]
        carries.clear()
        return result

    previous = sys.gettrace()
    sys.settrace(_prefix_trace(old_pipeline.__code__.co_filename, endpoint // 2))
    try:
        with pytest.raises(AssertionError, match="exact future prefix"):
            old_pipeline()
    finally:
        sys.settrace(previous)


@pytest.mark.parametrize("warm", (False, True))
def test_radix_projection_rejects_foreign_source_before_cache_or_exterior(
    warm: bool,
) -> None:
    source = PoweredCollatzTerm(27, 1)
    foreign = PoweredCollatzTerm(31, 1)
    source_width = source.width()
    assert source_width == foreign.width()
    arena = RadixProjection(3, source_width, source.resource_ledger)
    if warm:
        assert arena.digit(source, 1) == 0
    before = source.resource_ledger.snapshot()
    for index in (1, -1, source_width):
        with pytest.raises(ValueError, match="another binary source"):
            arena.digit(foreign, index)
        assert source.resource_ledger.snapshot() == before


def test_radix_entry_rejects_unadmitted_callbacks_and_numeric_aliases_before_width(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class Unadmitted:
        def width(self) -> Never:
            raise AssertionError("unadmitted term callback ran")

    with pytest.raises(TypeError, match="owned powered"):
        collatz_radix_digit(cast("PoweredCollatzTerm", Unadmitted()), 3, 0)
    term = PoweredCollatzTerm(27, 1)
    before = term.resource_ledger.snapshot()

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("invalid radix request reached field width")

    monkeypatch.setattr(PoweredCollatzTerm, "width", forbidden)
    for radix, index in ((True, 0), (3.0, 0), ("3", 0), (3, True), (3, 1.0), (3, "1")):
        with pytest.raises(TypeError, match="exact integers"):
            collatz_radix_digit(term, cast("int", radix), cast("int", index))
    with pytest.raises(IndexError):
        collatz_radix_digit(term, 3, -1)
    assert term.resource_ledger.snapshot() == before


def test_projection_admission_rejects_before_registration_or_source_callbacks() -> None:
    term = PoweredCollatzTerm(27, 1)
    before = term.resource_ledger.snapshot()
    for radix, width in ((3.0, 7), (True, 7), (3, 7.0), (3, True)):
        with pytest.raises(TypeError, match="exact integers"):
            RadixProjection(
                cast("int", radix), cast("int", width), term.resource_ledger
            )
        assert term.resource_ledger.snapshot() == before
    for width in (0, -1):
        with pytest.raises(ValueError, match="positive"):
            RadixProjection(3, width, term.resource_ledger)
        assert term.resource_ledger.snapshot() == before
    projection = RadixProjection(3, term.width(), term.resource_ledger)
    before = term.resource_ledger.snapshot()

    class Unadmitted:
        @property
        def _source_construction(self) -> Never:
            raise AssertionError("unadmitted source callback ran")

    with pytest.raises(TypeError, match="owned powered"):
        projection.digit(cast("PoweredCollatzTerm", Unadmitted()), 0)
    for index in (True, 1.0, "1"):
        with pytest.raises(TypeError, match="exact integer"):
            projection.digit(term, cast("int", index))
        assert term.resource_ledger.snapshot() == before
