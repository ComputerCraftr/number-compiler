"""Adversarial controls for source-bound Antihydra projection occurrences."""

from __future__ import annotations

from collections.abc import Hashable, Sequence
from math import lcm
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageDemand,
    SourceImageID,
    SourceImageProjection,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.sequences.antihydra.blocks import Cylinder
from number_compiler.sequences.antihydra.observers import SpaceTimeProjection
from number_compiler.sequences.antihydra.projection_core import (
    AntihydraFragmentID,
    AntihydraProjectionDriver,
    _AntihydraFragmentAdapter,
)
from number_compiler.sequences.antihydra.projection_fragments import ProjectionFragment
from number_compiler.sequences.antihydra.projection_occurrences import (
    ProjectionBlockImage,
    ProjectionOccurrence,
    ProjectionOccurrenceCursor,
    ProjectionOccurrenceID,
)
from number_compiler.sequences.antihydra.runtime import run
from number_compiler.sequences.antihydra.support import (
    F0,
    STARTUP,
    move,
    section_suffix,
    sweep,
)


def _projection(returns: int = 128) -> SpaceTimeProjection:
    return SpaceTimeProjection(run(returns), 2, 3, -1, 1, 5, 1_000_000)


def _scalar_macro_return(h: int, balance: int) -> tuple[int, int, int, int]:
    """Evaluate one checked section formula without a cylinder roof."""
    half_tail = (h - 4) // 2
    if h & 1:
        ticks = 3 * half_tail * half_tail + 12 * half_tail + 5
        balance -= 1
    else:
        ticks = 2 * balance + 3 * half_tail * half_tail + 12 * half_tail + 11
        balance += 2
    displacement = half_tail + 1
    assert (ticks - displacement) % 2 == 0
    return (
        h + h // 2,
        balance,
        (ticks - displacement) // 2,
        (ticks + displacement) // 2,
    )


def _reference_word(
    sparse: dict[tuple[int, int, int], int],
    word: Sequence[tuple[int, int]],
    head: int,
    time: int,
    *,
    width: int,
    time_width: int,
    sign: int,
    time_sign: int,
    modulus: int,
) -> tuple[int, int]:
    """Accumulate a bounded literal word into canonical twisted phases."""
    for port, supplied_count in word:
        count = 1 if port == F0 else supplied_count
        movement = move(port)
        spatial_period = 1 if movement == 0 else width * (2 if sign == -1 else 1)
        temporal_period = time_width * (2 if time_sign == -1 else 1)
        period = lcm(spatial_period, temporal_period)
        for offset in range(min(count, period)):
            x = head + movement * offset
            t = time + offset
            xturn, xslot = divmod(x, width)
            tturn, tslot = divmod(t, time_width)
            orientation = (-1 if sign == -1 and xturn & 1 else 1) * (
                -1 if time_sign == -1 and tturn & 1 else 1
            )
            key = port, xslot, tslot
            copies = (count - 1 - offset) // period + 1
            sparse[key] = (sparse.get(key, 0) + orientation * copies) % modulus
        if port != F0:
            head += movement * count
            time += count
    return head, time


def _scalar_sparse_projection(
    returns: int,
    *,
    width: int,
    time_width: int,
    sign: int,
    time_sign: int,
    modulus: int,
) -> list[list[int]]:
    """Independent source-8 recurrence plus bounded section-word expansion."""
    sparse: dict[tuple[int, int, int], int] = {}

    def word(value: Sequence[tuple[int, int]], head: int, time: int) -> tuple[int, int]:
        return _reference_word(
            sparse,
            value,
            head,
            time,
            width=width,
            time_width=time_width,
            sign=sign,
            time_sign=time_sign,
            modulus=modulus,
        )

    startup_head, startup_time = word(STARTUP, 0, 0)
    assert (startup_head, startup_time) == (1, 11)
    h, balance, head, time = 8, 0, startup_head, startup_time
    for _ in range(returns):
        # A section is selected from the pre-step arithmetic state.  This is
        # intentionally independent of retained cylinders and fragment images.
        count = (h - 4) // 2 - 1
        for index in range(count):
            word(sweep(index), head - 2 * index, time + 3 * index * index + 9 * index)
        word(
            section_suffix(balance, h - 4),
            head - 2 * count,
            time + 3 * count * count + 9 * count,
        )
        h, balance, left, right = _scalar_macro_return(h, balance)
        head += right - left
        time += left + right
    area = width * time_width
    ports = [[0] * area for _ in range(12)]
    for (port, xslot, tslot), coefficient in sparse.items():
        ports[port][xslot * time_width + tslot] = coefficient
    return ports


@pytest.mark.parametrize("sign,time_sign", ((-1, 1), (1, -1)))
def test_projection_sparse_image_matches_independent_scalar_source8_reference(
    sign: int,
    time_sign: int,
) -> None:
    returns, width, time_width, modulus = 8, 3, 4, 7
    expected = _scalar_sparse_projection(
        returns,
        width=width,
        time_width=time_width,
        sign=sign,
        time_sign=time_sign,
        modulus=modulus,
    )
    observed = SpaceTimeProjection(
        run(returns),
        width,
        time_width,
        sign,
        time_sign,
        modulus,
        1_000_000,
    ).evaluate()
    assert observed["typed_ports"] == expected


def test_projection_adapter_finish_does_not_replay_physical_roofs(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    projection = _projection(64)
    result = projection.result
    driver = AntihydraProjectionDriver(result.ledger)
    result._engine.projection_fragment_driver = driver
    original_finish = _AntihydraFragmentAdapter.finish
    original_apply = Cylinder.apply
    finishing = False
    finishes = 0

    def trace_finish(
        adapter: _AntihydraFragmentAdapter, payload: AntihydraFragmentID
    ) -> ProjectionFragment:
        nonlocal finishes, finishing
        finishes += 1
        finishing = True
        try:
            return original_finish(adapter, payload)
        finally:
            finishing = False

    def reject_finish_replay(
        cylinder: Cylinder, h: int, balance: int
    ) -> tuple[int, int, int, int]:
        if finishing:
            raise AssertionError("projection finish replayed a physical cylinder")
        return original_apply(cylinder, h, balance)

    monkeypatch.setattr(_AntihydraFragmentAdapter, "finish", trace_finish)
    monkeypatch.setattr(Cylinder, "apply", reject_finish_replay)
    projection.evaluate()
    assert finishes == len(result._term.segments)


def test_projection_cursor_chronology_matches_scalar_macro_recurrence() -> None:
    projection = _projection()
    result = projection.result
    cursor = ProjectionOccurrenceCursor(result.ledger)
    h, balance, head, time, completed = 8, 0, 1, 11, 0
    cursor.begin(projection)
    try:
        for segment in result._term.segments:
            occurrence = cursor.next()
            assert type(occurrence) is ProjectionOccurrenceID
            record = cursor.resolve(occurrence)
            assert (
                record.block,
                record.start,
                record.h,
                record.balance,
                record.head,
                record.time,
                record.key,
            ) == (
                segment.cylinder,
                completed,
                h,
                balance,
                head,
                time,
                projection._fragment_key(
                    segment.cylinder,
                    completed,
                    head,
                    time,
                ),
            )
            left = right = 0
            for index in range(segment.cylinder.width):
                assert ((segment.cylinder.parity_word >> index) & 1) == (h & 1)
                h, balance, step_left, step_right = _scalar_macro_return(h, balance)
                left += step_left
                right += step_right
            completed += segment.cylinder.width
            head += right - left
            time += left + right
        assert cursor.next() is None
        cursor.finish()
        assert (completed, h, balance, head, time) == (
            result.returns,
            result.h,
            result.balance,
            result.head,
            result.physical_ticks,
        )
    finally:
        cursor.clear()
    assert cursor.projection is None


def test_projection_cursor_does_not_rescan_all_retained_segments_per_step() -> None:
    projection = _projection(512)
    result = projection.result
    cursor = ProjectionOccurrenceCursor(result.ledger)
    cursor.begin(projection)
    sealed_rows = result.ledger.counters[
        "antihydra_projection_occurrence_segment_seal_rows"
    ]
    assert sealed_rows == len(result._term._segments)
    validations = result.ledger.counters.get("arithmetic_result_validation_blocks", 0)
    try:
        while (occurrence := cursor.next()) is not None:
            cursor.resolve(occurrence)
        # Per-occurrence field seals preserve source authority.  Traversing
        # them must not re-run whole-result validation for every source block.
        assert (
            result.ledger.counters.get("arithmetic_result_validation_blocks", 0)
            == validations
        )
        assert (
            result.ledger.counters["antihydra_projection_occurrence_segment_seal_rows"]
            == sealed_rows
        )
    finally:
        cursor.clear()


def test_projection_cursor_rejects_post_begin_segment_replacement() -> None:
    projection = _projection(128)
    result = projection.result
    cursor = ProjectionOccurrenceCursor(result.ledger)
    cursor.begin(projection)
    segments = result._term._segments
    original = segments[0]
    replacement = type(original)(
        original.start,
        type(original.cylinder)(
            original.cylinder.width,
            original.cylinder.residue,
            original.cylinder.output + (1 << original.cylinder.width),
            original.cylinder.delta,
            original.cylinder.minimum,
            original.cylinder.parity_word,
        ),
    )
    try:
        segments[0] = replacement
        with pytest.raises(
            ValueError, match="retained Antihydra projection support was changed"
        ):
            cursor.next()
    finally:
        segments[0] = original
        cursor.clear()


def test_projection_cursor_finish_rejects_mutated_consumed_segment() -> None:
    projection = _projection(128)
    result = projection.result
    cursor = ProjectionOccurrenceCursor(result.ledger)
    cursor.begin(projection)
    segments = result._term._segments
    original = segments[0]
    try:
        while cursor.next() is not None:
            pass
        object.__setattr__(original.cylinder, "output", original.cylinder.output + 1)
        with pytest.raises(ValueError, match="arithmetic support was changed"):
            cursor.finish()
    finally:
        object.__setattr__(original.cylinder, "output", original.cylinder.output - 1)
        cursor.clear()


def test_projection_cursor_rejects_early_finish_and_stale_handle() -> None:
    projection = _projection()
    cursor = ProjectionOccurrenceCursor(projection.result.ledger)
    cursor.begin(projection)
    try:
        first = cursor.next()
        assert type(first) is ProjectionOccurrenceID
        with pytest.raises(ArithmeticError, match="diverged"):
            cursor.finish()
        second = cursor.next()
        assert type(second) is ProjectionOccurrenceID
        with pytest.raises(ValueError, match="different arena"):
            cursor.resolve(first)
        cursor.resolve(second)
        assert cursor.next() is None
        cursor.finish()
    finally:
        cursor.clear()


def test_projection_cursor_rejects_foreign_occurrence_handle() -> None:
    projection = _projection(64)
    first = ProjectionOccurrenceCursor(projection.result.ledger)
    second = ProjectionOccurrenceCursor(projection.result.ledger)
    first.begin(projection)
    second.begin(projection)
    try:
        first_handle = first.next()
        second_handle = second.next()
        assert type(first_handle) is ProjectionOccurrenceID
        assert type(second_handle) is ProjectionOccurrenceID
        with pytest.raises(ValueError, match="different arena"):
            first.resolve(second_handle)
        with pytest.raises(ValueError, match="different arena"):
            second.resolve(first_handle)
        foreign = ProjectionOccurrenceID(
            ArenaToken("foreign-projection-occurrence"),
            "antihydra-projection-occurrence",
            0,
        )
        with pytest.raises(ValueError, match="different arena"):
            first.resolve(foreign)
    finally:
        first.clear()
        second.clear()


@pytest.mark.parametrize("field", ("h", "balance"))
def test_projection_cursor_rejects_mutated_occurrence_coordinates(field: str) -> None:
    projection = _projection(64)
    cursor = ProjectionOccurrenceCursor(projection.result.ledger)
    cursor.begin(projection)
    try:
        handle = cursor.next()
        assert type(handle) is ProjectionOccurrenceID
        record = cursor.resolve(handle)
        original = getattr(record, field)
        # Preserve the complete cylinder residue in the h case: congruence
        # alone was the old admission gap, so the independent seal must reject.
        increment = (1 << record.block.width) if field == "h" else 1
        object.__setattr__(record, field, original + increment)
        try:
            with pytest.raises(ValueError, match="occurrence was changed"):
                cursor.resolve(handle)
        finally:
            object.__setattr__(record, field, original)
        assert cursor.resolve(handle) is record
    finally:
        cursor.clear()


def test_projection_cursor_rejects_mutated_key_and_block() -> None:
    projection = _projection(64)
    cursor = ProjectionOccurrenceCursor(projection.result.ledger)
    cursor.begin(projection)
    try:
        handle = cursor.next()
        assert type(handle) is ProjectionOccurrenceID
        record = cursor.resolve(handle)
        head_phase = record.key.head_phase
        object.__setattr__(record.key, "head_phase", (head_phase + 1) % 4)
        try:
            with pytest.raises(ValueError, match="occurrence was changed"):
                cursor.resolve(handle)
        finally:
            object.__setattr__(record.key, "head_phase", head_phase)
        assert cursor.resolve(handle) is record

        output = record.block.output
        object.__setattr__(record.block, "output", output + 1)
        try:
            # The realized arithmetic support now rejects the shared cylinder
            # before the cursor reaches its own occurrence seal.
            with pytest.raises(ValueError, match="arithmetic support was changed"):
                cursor.resolve(handle)
        finally:
            object.__setattr__(record.block, "output", output)
        assert cursor.resolve(handle) is record
    finally:
        cursor.clear()


@pytest.mark.parametrize("field", ("output_h", "classes"))
def test_materialized_projection_image_is_source_bound_and_sealed(field: str) -> None:
    projection = _projection(64)
    cursor = ProjectionOccurrenceCursor(projection.result.ledger)
    cursor.begin(projection)
    try:
        handle = cursor.next()
        assert type(handle) is ProjectionOccurrenceID
        assert cursor.resolve(handle).image is None
        record = cursor.materialize_image(handle)
        image = record.image
        assert type(image) is ProjectionBlockImage
        assert (image.output_h, image.output_balance) == record.block.advance(
            record.h, record.balance
        )
        original = getattr(image, field)
        changed = image.output_h + 1 if field == "output_h" else (*image.classes, ())
        object.__setattr__(image, field, changed)
        try:
            with pytest.raises(ValueError, match="occurrence was changed"):
                cursor.resolve(handle)
        finally:
            object.__setattr__(image, field, original)
        assert cursor.resolve(handle) is record
    finally:
        cursor.clear()


def test_projection_image_budget_failure_keeps_unmaterialized_occurrence() -> None:
    projection = _projection(64)
    ledger = projection.result.ledger
    cursor = ProjectionOccurrenceCursor(ledger)
    cursor.begin(projection)
    original_limit = ledger.max_nodes
    try:
        handle = cursor.next()
        assert type(handle) is ProjectionOccurrenceID
        before_nodes = ledger.nodes
        ledger.max_nodes = before_nodes
        with pytest.raises(BlockContextBudgetExceeded, match="budget exceeded"):
            cursor.materialize_image(handle)
        assert ledger.nodes == before_nodes
        assert cursor.resolve(handle).image is None
        assert ledger.counters["antihydra_projection_block_image_discovery_steps"] == 64
    finally:
        ledger.max_nodes = original_limit
        cursor.clear()


@pytest.mark.parametrize(
    "field,value",
    (
        ("width", 3),
        ("time_width", 4),
        ("sign", 1),
        ("time_sign", -1),
        ("modulus", 7),
    ),
)
def test_projection_cursor_seals_projection_parameters(field: str, value: int) -> None:
    projection = _projection(64)
    cursor = ProjectionOccurrenceCursor(projection.result.ledger)
    cursor.begin(projection)
    try:
        handle = cursor.next()
        assert type(handle) is ProjectionOccurrenceID
        original = getattr(projection, field)
        object.__setattr__(projection, field, value)
        try:
            with pytest.raises(ValueError, match="cursor state was changed"):
                cursor.resolve(handle)
        finally:
            object.__setattr__(projection, field, original)
        cursor.resolve(handle)
    finally:
        cursor.clear()


def test_projection_cursor_budget_failure_releases_transient_authority() -> None:
    projection = _projection(64)
    ledger = projection.result.ledger
    cursor = ProjectionOccurrenceCursor(ledger)
    baseline = ledger.entries, ledger.nodes
    before_validation = ledger.counters.get(
        "antihydra_projection_occurrence_validation_steps", 0
    )
    before_roof = ledger.counters.get("antihydra_projection_occurrence_roof_steps", 0)
    before_operand_bits = ledger.counters.get(
        "antihydra_projection_occurrence_operand_bits", 0
    )
    before_publications = ledger.counters.get(
        "antihydra_projection_occurrence_steps", 0
    )
    cursor.begin(projection)
    original_limit = ledger.max_nodes
    try:
        ledger.max_nodes = ledger.nodes
        with pytest.raises(BlockContextBudgetExceeded, match="budget exceeded"):
            cursor.next()
        assert not cursor._occurrences
        assert not cursor._occurrence_seals
    finally:
        ledger.max_nodes = original_limit
        cursor.clear()
    assert (ledger.entries, ledger.nodes) == baseline
    assert (
        ledger.counters["antihydra_projection_occurrence_validation_steps"]
        - before_validation
        == 64
    )
    assert (
        ledger.counters["antihydra_projection_occurrence_roof_steps"] - before_roof
        == 64
    )
    assert (
        ledger.counters["antihydra_projection_occurrence_operand_bits"]
        > before_operand_bits
    )
    assert (
        ledger.counters.get("antihydra_projection_occurrence_steps", 0)
        == before_publications
    )
    assert cursor.projection is None
    for row in ledger.inventory():
        if row.name.startswith("antihydra.projection-occurrence"):
            assert row.entries == row.nodes == 0


def test_projection_cursor_admits_segment_snapshot_before_allocating_it(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    projection = _projection(128)
    result = projection.result
    result._term._materialize_segments(result)
    cursor = ProjectionOccurrenceCursor(result.ledger)
    original_limit = result.ledger.max_nodes
    result.ledger.max_nodes = result.ledger.nodes

    def forbidden(_segment: object) -> tuple[int, int, int, int, int, int, int]:
        raise AssertionError("segment snapshot allocated before resource admission")

    monkeypatch.setattr(
        ProjectionOccurrenceCursor, "_segment_seal", staticmethod(forbidden)
    )
    try:
        with pytest.raises(BlockContextBudgetExceeded, match="budget exceeded"):
            cursor.begin(projection)
    finally:
        result.ledger.max_nodes = original_limit
        cursor.clear()
    assert (
        result.ledger.counters.get(
            "antihydra_projection_occurrence_segment_seal_rows", 0
        )
        == 0
    )


def test_fragment_adapter_rejects_unissued_raw_occurrence_records() -> None:
    projection = _projection(64)
    result = projection.result
    driver = AntihydraProjectionDriver(result.ledger)
    result._engine.projection_fragment_driver = driver
    driver.cursor.begin(projection)
    try:
        handle = driver.cursor.next()
        assert type(handle) is ProjectionOccurrenceID
        issued = driver.cursor.resolve(handle)
        raw = ProjectionOccurrence(
            issued.block,
            issued.start,
            issued.h,
            issued.balance,
            issued.head,
            issued.time,
            issued.key,
        )
        unissued = cast(ProjectionOccurrenceID, raw)
        with pytest.raises(TypeError, match="occurrence ID"):
            driver.adapter.configure(driver.cursor, unissued, 8)
        with pytest.raises(TypeError, match="occurrence ID"):
            driver.build(unissued, 8, 0)

        forged = ProjectionOccurrenceID(
            ArenaToken("forged-projection-occurrence"),
            "antihydra-projection-occurrence",
            0,
        )
        with pytest.raises(ValueError, match="different arena"):
            driver.adapter.configure(driver.cursor, forged, 8)
        with pytest.raises(ValueError, match="different arena"):
            driver.build(forged, 8, 0)
    finally:
        driver.cursor.clear()


def test_spacetime_fragments_use_tile_scheduler_and_transport_cached_segments(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    image_calls = 0
    projection_calls = 0
    occurrence_calls = 0
    source_image = TileScheduler.source_image
    source_image_demanded = TileScheduler.source_image_demanded
    source_projection = TileScheduler.source_projection
    next_occurrence = ProjectionOccurrenceCursor.next

    def trace_image(
        scheduler: TileScheduler,
        adapter: SourceBoundImageAdapter,
        source: Hashable,
        action: Hashable,
    ) -> SourceImageID:
        nonlocal image_calls
        image_calls += 1
        return source_image(scheduler, adapter, source, action)

    def trace_demanded_image(
        scheduler: TileScheduler,
        adapter: SourceBoundImageAdapter,
        source: Hashable,
        action: Hashable,
        demand: SourceImageDemand,
    ) -> SourceImageID:
        nonlocal image_calls
        image_calls += 1
        return source_image_demanded(scheduler, adapter, source, action, demand)

    def trace_projection(
        scheduler: TileScheduler,
        adapter: SourceBoundImageAdapter,
        image: SourceImageID,
        demand: SourceImageDemand,
    ) -> SourceImageProjection:
        nonlocal projection_calls
        projection_calls += 1
        return source_projection(scheduler, adapter, image, demand)

    def trace_occurrence(
        cursor: ProjectionOccurrenceCursor,
    ) -> ProjectionOccurrenceID | None:
        nonlocal occurrence_calls
        occurrence_calls += 1
        return next_occurrence(cursor)

    monkeypatch.setattr(TileScheduler, "source_image", trace_image)
    monkeypatch.setattr(TileScheduler, "source_image_demanded", trace_demanded_image)
    monkeypatch.setattr(TileScheduler, "source_projection", trace_projection)
    monkeypatch.setattr(ProjectionOccurrenceCursor, "next", trace_occurrence)
    projection = _projection()
    result = projection.result
    segments = len(result._term.segments)
    # Arithmetic construction is now an actual shared-scheduler consumer.
    # Measure observer calls separately so its exact reuse contract stays fixed.
    assert (image_calls, projection_calls, occurrence_calls) == (1, 1, 0)
    image_calls = projection_calls = 0
    first = projection.evaluate()
    assert (image_calls, projection_calls, occurrence_calls) == (
        segments,
        segments,
        segments + 1,
    )
    before_steps = result.ledger.counters["antihydra_projection_occurrence_steps"]

    repeated = SpaceTimeProjection(
        result,
        projection.width,
        projection.time_width,
        projection.sign,
        projection.time_sign,
        projection.modulus,
        projection.max_terms,
    ).evaluate()
    assert repeated == first
    assert (image_calls, projection_calls) == (segments, segments)
    assert occurrence_calls == 2 * (segments + 1)
    assert (
        result.ledger.counters["antihydra_projection_occurrence_steps"] - before_steps
        == segments
    )
    driver = result._engine.projection_fragment_driver
    assert type(driver) is AntihydraProjectionDriver
    assert type(driver.scheduler) is TileScheduler
    assert driver.cursor.projection is None
    assert driver.adapter.projection is None
