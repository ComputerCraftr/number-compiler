"""Independent arithmetic and representation checks for the Collatz lazy path."""

from __future__ import annotations

from collections.abc import Callable
from itertools import product
from typing import cast

import pytest

from devtools.verification.collatz_carry_ranges import CarryRangeTransfer
from devtools.verification.lazy_collatz import (
    CollatzLazyView,
    LazyCollatzApplication,
    Program,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    LoweringCapability,
)
from number_compiler.arithmetic.fields.dyadic_tile import tile_arena_metrics
from number_compiler.projection.microblock_cache import MicroblockCache
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from tests.support.assertions import forbid_explicit_lowering as _forbid


def _microblock_cache(application: LazyCollatzApplication) -> MicroblockCache:
    return MicroblockCache.shared(application.ledger)


def _set_exact_program_width(
    application: LazyCollatzApplication, program_id: int, width: int
) -> None:
    update = cast(
        Callable[[int, int], None],
        object.__getattribute__(application, "_set_exact_program_width"),
    )
    update(program_id, width)


def _bits(value: int) -> tuple[int, ...]:
    return tuple((value >> i) & 1 for i in range(value.bit_length()))


def _physical(value: int, steps: int) -> int:
    for _ in range(steps):
        value = 3 * value + 1 if value & 1 else value // 2
    return value


@pytest.mark.parametrize(
    "seed,steps",
    (
        pytest.param(54, 64, marks=pytest.mark.validation),
        pytest.param(27, 111, marks=pytest.mark.validation),
        (1, 10**9),
        (1, 10**9 + 1),
        (1, 10**9 + 2),
    ),
)
def test_public_collatz_point_and_width_never_lower_an_endpoint(
    monkeypatch: pytest.MonkeyPatch, seed: int, steps: int
) -> None:
    monkeypatch.setattr(LazyCollatzApplication, "materialize_bits", _forbid)
    monkeypatch.setattr(LazyCollatzApplication, "source_span", _forbid)
    expected = (1, 4, 2)[steps % 3] if seed == 1 else _physical(seed, steps)
    term = PoweredCollatzTerm(seed, steps)
    assert term.width() == expected.bit_length()
    assert tuple(term.digit(i) for i in range(term.width())) == _bits(expected)
    with pytest.raises(IndexError):
        term.digit(term.width())


def test_large_valuation_keeps_only_finite_carries_and_symbolic_shifts(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    q = 128
    intermediate = (4**q - 1) // 3
    seed = (2 * intermediate - 1) // 3
    application = LazyCollatzApplication(2, 0, _bits(seed))
    monkeypatch.setattr(LazyCollatzApplication, "materialize_bits", _forbid)
    monkeypatch.setattr(LazyCollatzApplication, "source_span", _forbid)
    before = tile_arena_metrics()["intern_misses"]
    result = application.advance_events(2)
    assert result.valuations == (1, 256)
    assert result.view.width == 1
    assert application.view_point(result.view, 0) == 1
    assert application.maximum_carry <= 2
    assert application.retained_spans() == ()
    assert tile_arena_metrics()["intern_misses"] == before
    assert not hasattr(application, "_physical_advances")
    assert not hasattr(application, "_offset_ports")


def test_collatz_transfer_is_complete_for_all_input_carries() -> None:
    for length in range(1, 6):
        for bits in product((0, 1), repeat=length):
            transfer = CarryRangeTransfer.bit(bits[0])
            for bit in bits[1:]:
                transfer = transfer.compose(CarryRangeTransfer.bit(bit))
            for incoming in range(3):
                carry = incoming
                ones: list[int] = []
                for position, bit in enumerate(bits):
                    value = 3 * bit + carry
                    if value & 1:
                        ones.append(position)
                    carry = value >> 1
                summary = transfer.rows[incoming]
                assert summary.exit_carry == carry
                assert summary.first_one == (ones[0] if ones else None)
                assert summary.last_one == (ones[-1] if ones else None)


def test_collatz_foreign_view_rejected_for_point_summary_and_lowering() -> None:
    left = LazyCollatzApplication(2, 0, _bits(3))
    right = LazyCollatzApplication(2, 0, _bits(7))
    left.range_summary(left.initial)
    with pytest.raises(ValueError):
        left.view_point(right.initial, -1)
    with pytest.raises(ValueError):
        left.range_summary(right.initial)
    with pytest.raises(ValueError):
        left.materialize_bits(right.initial, LoweringCapability(left.token))


def test_far_mul3_microblock_retains_only_bounded_window_blocks() -> None:
    seed = (1 << 4096) | int("10" * 1024, 2) | 1
    application = LazyCollatzApplication(2, 0, _bits(seed))
    expected = 3 * seed + 1
    view = application.append_program(
        application.initial,
        Program("mul3"),
        expected.bit_length(),
    )
    block = 32
    observed = application.program_block(view.program, block)
    assert observed == (expected >> (64 * block)) & ((1 << 64) - 1)
    owned = tuple(
        key
        for key in _microblock_cache(application).audit_snapshot().blocks
        if key.program.owner is application.token and key.kind == "binary"
    )
    assert len(owned) <= 3
    assert {key.block for key in owned} <= {block, block + 1}
    assert application.carry_cell_evaluations == 64
    cache = _microblock_cache(application).audit_snapshot()
    assert len(cache.blocks) <= MicroblockCache.MAX_ENTRIES
    assert cache.payload_bytes <= MicroblockCache.MAX_PAYLOAD_BYTES
    report = collect_ledger_metrics(application.ledger)
    assert report.resource_accounting_mismatch == 0
    assert report.forbidden_future_payloads == 0


def test_program_width_and_view_validation_reject_aliases_before_mutation() -> None:
    application = LazyCollatzApplication(2, 0, _bits(27))
    stale = ActionProgramID(
        application.token,
        "program",
        application.program_count,
    )
    before = application.ledger.snapshot()
    with pytest.raises(ValueError):
        application.known_program_width(stale)
    with pytest.raises(ValueError):
        _set_exact_program_width(application, stale.local_id, 1)
    for width, exact in ((True, True), (5, 1), (0, True)):
        invalid = CollatzLazyView(
            application.initial.source,
            application.initial.program,
            width,
            cast(bool, exact),
        )
        with pytest.raises(ValueError):
            application.range_summary(invalid)
    for coordinate in (True, 1.5):
        with pytest.raises(TypeError):
            application.view_point(application.initial, cast(int, coordinate))
        with pytest.raises(TypeError):
            application.range_evaluator.point(
                application.initial.program,
                cast(int, coordinate),
            )
    for start, length in ((True, 1), (0, 1.5)):
        with pytest.raises(TypeError):
            application.range_evaluator.range_effect(
                application.initial.program,
                start,
                cast(int, length),
            )
    assert application.ledger.snapshot() == before
