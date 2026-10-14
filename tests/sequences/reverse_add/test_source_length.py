"""Independent width checks for source-derived reverse/add cylinders."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.hashlife.execution.source_bound_images import SourceImageDemand
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.source_images import (
    ReverseSourceImageWorkspace,
    _ReverseSourceImageAdapter,
)
from number_compiler.sequences.reverse_add.source_workspace import (
    ReverseSourceImageWorkspace as DirectReverseSourceImageWorkspace,
)
from tests.support.reverse_source_length import (
    fused_two_step_width,
    iter_second_pairs,
    one_step_width,
    source_growth,
    source_width,
)


def _digits(value: int, base: int) -> tuple[int, ...]:
    result: list[int] = []
    while True:
        result.append(value % base)
        value //= base
        if not value:
            return tuple(result)


def _source(value: int, base: int) -> ExactSource:
    return ExactSource(_digits(value, base), base, orbit="reverse-add")


def _step(value: int, base: int) -> int:
    reflected = 0
    for digit in _digits(value, base):
        reflected = reflected * base + digit
    return value + reflected


def test_workspace_direct_import_matches_the_legacy_module_export() -> None:
    assert ReverseSourceImageWorkspace is DirectReverseSourceImageWorkspace


@pytest.mark.parametrize(
    ("value", "base"),
    (
        (0, 2),
        (1, 2),
        (11, 2),
        (5, 3),
        (41, 3),
        (1, 10),
        (45, 10),
        (99, 10),
        (196, 10),
        (1001, 10),
    ),
)
def test_source_and_fused_widths_match_literal_arithmetic(
    value: int, base: int
) -> None:
    source = _source(value, base)
    ledger = ResourceLedger()
    first = _step(value, base)
    second = _step(first, base)
    assert source_width(source) == len(_digits(value, base))
    assert one_step_width(source, ledger) == len(_digits(first, base))
    assert fused_two_step_width(source, ledger) == len(_digits(second, base))


@pytest.mark.parametrize(("value", "expected"), ((45, 0), (196, 0), (19, 1), (99, 1)))
def test_palindromic_source_growth_uses_first_decisive_pair(
    value: int, expected: int
) -> None:
    ledger = ResourceLedger()
    assert source_growth(_source(value, 10), ledger) == expected
    assert ledger.counters["reverse_source_length_growth_queries"] == 1


@pytest.mark.parametrize(("value", "base"), ((99, 10), (196, 10), (41, 3)))
def test_second_pair_pullback_matches_literal_first_output(
    value: int, base: int
) -> None:
    source = _source(value, base)
    first_digits = _digits(_step(value, base), base)
    expected = tuple(
        first_digits[i] + first_digits[-1 - i] for i in range(len(first_digits))
    )
    assert tuple(iter_second_pairs(source, ResourceLedger())) == expected


def test_length_queries_never_normalize_or_emit_digits(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.formula.skew_residue_laws as skew
    import number_compiler.sequences.reverse_add.source_images as images

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("length query entered digit normalization")

    monkeypatch.setattr(skew, "skew_normalized_digit", forbidden)
    monkeypatch.setattr(images._ReverseSourceImageAdapter, "_normalized", forbidden)
    monkeypatch.setattr(
        images._ReverseSourceImageAdapter, "iter_primitive_digits", forbidden
    )
    source = _source(196, 10)
    ledger = ResourceLedger()
    assert one_step_width(source, ledger) == 3
    assert fused_two_step_width(source, ledger) == 4


def test_length_queries_retain_no_pairs_or_carries() -> None:
    source = _source(int("4" * 256 + "5" * 256), 10)
    ledger = ResourceLedger()
    retained = ledger.entries, ledger.nodes
    assert one_step_width(source, ledger) == 512
    assert fused_two_step_width(source, ledger) == 513
    assert (ledger.entries, ledger.nodes) == retained
    assert ledger.counters["reverse_source_length_pair_reads"] <= 514


def test_maximum_width_tightens_only_after_the_completed_width_projection() -> None:
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    term = ReverseAddPoweredTerm(196, 3)
    conservative = len(_digits(196, 10)) + 3
    assert term.maximum_width == conservative == 6
    assert term._workspace is None

    assert term.width() == 4
    workspace = term._workspace
    assert workspace is not None
    image = workspace._image
    assert image is not None
    assert workspace.adapter._q19_owner is not None
    assert term._ledger.counters.get("recursive_output_stream_emitted_digits", 0) == 0
    misses = term._ledger.counters.get("source_image_projection_misses", 0)
    assert term.maximum_width == 4
    assert term.maximum_width == 4
    assert term._ledger.counters.get("source_image_projection_misses", 0) == misses
    assert term.digits() == (6, 3, 4, 7)
    assert workspace._image is not None
    assert workspace.adapter._q19_owner is not None
    assert (
        term._ledger.counters.get("reverse_successor_tape_width_compilations", 0) == 0
    )


def test_maximum_width_drops_to_conservative_after_its_image_owner_is_cleared() -> None:
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    term = ReverseAddPoweredTerm(196, 3)
    assert term.width() == 4
    workspace = term._workspace
    assert workspace is not None
    owner = workspace.adapter._q19_owner
    assert owner is not None
    workspace.scheduler.clear_source_images()

    assert term.maximum_width == 6
    assert workspace.adapter._q19_owner is None
    assert owner._disposed


def test_maximum_width_rejects_a_mutated_source_action_binding() -> None:
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    term = ReverseAddPoweredTerm(196, 3)
    assert term.width() == 4
    term.generation = 4

    with pytest.raises(ValueError, match="source/action binding changed"):
        _ = term.maximum_width


def test_maximum_width_does_not_trust_a_replaced_cached_projection() -> None:
    from number_compiler.hashlife.execution.source_bound_images import (
        SourceImageProjection,
    )
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    term = ReverseAddPoweredTerm(196, 3)
    assert term.width() == 4
    workspace = term._workspace
    assert workspace is not None
    from dataclasses import replace

    core = workspace.scheduler._source_image_core()
    image = workspace._image
    assert image is not None
    key = image, SourceImageDemand("width")
    assert key in core._projections
    core._projections[key] = replace(
        core._projections[key], projection=SourceImageProjection(99)
    )

    with pytest.raises(ValueError, match="projection record was altered"):
        _ = term.maximum_width


def test_maximum_width_falls_back_when_the_retained_projection_is_missing() -> None:
    from number_compiler.hashlife.execution.source_bound_images import (
        SourceImageDemand,
    )
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    term = ReverseAddPoweredTerm(196, 3)
    assert term.width() == 4
    workspace = term._workspace
    assert workspace is not None
    image = workspace._image
    assert image is not None
    core = workspace.scheduler._source_image_core()
    demand = SourceImageDemand("width")
    key = image, demand
    record = core._projections.pop(key)
    assert record.projection.value == 4
    core._publication_seals.drop_projection(key)
    core.ledger.release(core._projection_owner, entries=1, nodes=1)
    misses = term._ledger.counters.get("source_image_projection_misses", 0)

    # Neither a direct cache lookup nor maximum_width may rebuild this result.
    assert core.cached_projection(workspace.adapter, image, demand) is None
    assert term._ledger.counters.get("source_image_projection_misses", 0) == misses

    assert term.maximum_width == 6
    assert term._ledger.counters.get("source_image_projection_misses", 0) == misses


@pytest.mark.parametrize("base", [2, 3, 10, 16])
def test_all_small_sources_match_two_literal_lengths(base: int) -> None:
    for seed in range(1024):
        source = _source(seed, base)
        first = _step(seed, base)
        second = _step(first, base)
        ledger = ResourceLedger()
        assert one_step_width(source, ledger) == len(_digits(first, base))
        assert fused_two_step_width(source, ledger) == len(_digits(second, base))
        assert ledger.counters["reverse_source_validation_coordinates"] == (
            4 * len(source.digits)
        )


@pytest.mark.parametrize(
    "seed,steps,width", [(196, 1, 3), (196, 2, 4), (99, 2, 4), (1, 3, 1)]
)
def test_scheduler_width_demand_never_calls_digit_consumers(
    seed: int, steps: int, width: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("scheduler length demand called a digit consumer")

    for method in (
        "_carry_and_digit",
        "_normalized",
        "iter_primitive_digits",
        "iter_second_digits",
        "iter_same_carry_digits",
    ):
        monkeypatch.setattr(
            _ReverseSourceImageAdapter, method, forbidden, raising=False
        )
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, steps)
    assert workspace.width() == width
    before = dict(workspace.ledger.counters)
    assert workspace.width() == width
    for counter in (
        "reverse_source_validation_coordinates",
        "reverse_source_pullback_pair_reads",
        "reverse_source_length_pair_reads",
    ):
        assert workspace.ledger.counters.get(counter, 0) == before.get(counter, 0)
    workspace.dispose()
    assert workspace.ledger.nodes == workspace.ledger.entries == 0


@pytest.mark.parametrize("width", [16, 64, 256, 1024])
def test_decisive_outer_pair_does_not_scan_pair_interior(width: int) -> None:
    source = ExactSource((1,) * width, 10, orbit="reverse-add")
    ledger = ResourceLedger()
    assert fused_two_step_width(source, ledger) == width
    # Initial radix validation remains linear and is explicitly charged.
    assert ledger.counters["reverse_source_validation_coordinates"] == 2 * width
    assert ledger.counters["reverse_source_pullback_pair_reads"] <= 5
    assert ledger.counters["reverse_source_length_pair_reads"] == 0
    assert ledger.counters["reverse_source_ports_crt_threshold_queries"] == 1


@pytest.mark.parametrize("width", [16, 64, 256, 1024])
def test_long_neutral_gap_is_not_researched_at_every_boundary(width: int) -> None:
    half = (width - 2) // 2
    digits = (4,) + (4,) * half + (5,) * half + (4,)
    source = ExactSource(digits, 10, orbit="reverse-add")
    # Pair field is [8, 9, ..., 9, 8]. The descending cursor searches
    # across the gap once and reuses its carry through the neutral cells.
    seed = 0
    for digit in reversed(digits):
        seed = 10 * seed + digit
    first_digits = _digits(_step(seed, 10), 10)
    expected = tuple(a + b for a, b in zip(first_digits, reversed(first_digits)))
    ledger = ResourceLedger()
    assert tuple(iter_second_pairs(source, ledger)) == expected
    assert ledger.counters["reverse_source_pullback_predecessor_search"] <= width
    assert ledger.counters["reverse_source_pullback_pair_reads"] <= 5 * width


def test_zero_point_demand_checks_workspace_authority() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 0, 20)
    workspace.steps = 21
    with pytest.raises(ValueError, match="binding was altered"):
        workspace.digit(0)
    workspace.steps = 20
    assert workspace.digit(0) == 0
    assert workspace._image is None
    workspace.dispose()
    with pytest.raises(ValueError, match="disposed"):
        workspace.digit(0)


def test_decimal_rejects_unused_recursive_authority_before_allocation() -> None:
    from number_compiler.arithmetic.contracts.exact_tree_context import (
        OriginalSourceConstruction,
    )

    ledger = ResourceLedger()
    construction = OriginalSourceConstruction(ExactSource((7, 8, 7), 10))
    with pytest.raises(ValueError, match="do not consume recursive source authority"):
        ReverseSourceImageWorkspace(ledger, 196, 20, source_construction=construction)
    assert ledger.nodes == ledger.entries == ledger.owner_count == 0
