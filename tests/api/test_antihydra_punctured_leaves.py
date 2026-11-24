"""Closed events remain bounded consumers of the shared source scheduler."""

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.execution.dyadic_return_actions import append_source
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnSourceRecord,
    DyadicReturnSupportRecord,
)
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.dyadic_return_payload_audit import (
    audit_dyadic_return_payloads,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra import mahler_cache
from number_compiler.sequences.antihydra.mahler_action import associated_action
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm
from tests.support.mahler_harmonic_reference import literal_antihydra_summary
from tests.support.source_image_assertions import dyadic_image_summary


def _cyclic_source(width: int) -> int:
    motif = (1, 0, 1, 0, 1, 0, 0, 1)
    correction = 0
    for position, parity in enumerate(motif):
        correction = 3 * correction + (parity << position)
    factor: int = 3 ** len(motif) - (1 << len(motif))
    return correction * pow(factor, -1, 1 << width) % (1 << width)


def _assert_cyclic_summary(
    result: DyadicReturnSupportRecord,
    source: int,
    expected: tuple[int, int, int, int, int | None],
) -> None:
    transfer = result.transfer
    assert (transfer.upper * source + transfer.offset) // transfer.lower == expected[0]
    assert (result.delta, result.minimum, result.odd_steps) == expected[1:4]


def test_pointed_carry_response_matches_complete_alphabet() -> None:
    from number_compiler.sequences.antihydra.mahler_transient_carry_sheet import (
        physical_carry_at,
        physical_carry_sheet,
    )

    for steps in range(1, 9):
        assert tuple(physical_carry_at(steps, r) for r in range(1 << steps)) == (
            physical_carry_sheet(steps)
        )


def test_power_probe_selects_one_response_without_allocating_carry_alphabet(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.antihydra import mahler_transient_carry_sheet

    def forbidden(_steps: int) -> None:
        pytest.fail("powered probe allocated the complete carry alphabet")

    select_response = mahler_transient_carry_sheet.select_repeat_response
    requests = 0

    def select_once(h: int, width: int) -> tuple[int, int, int, int, int] | None:
        nonlocal requests
        requests += 1
        assert requests == 1
        return select_response(h, width)

    monkeypatch.setattr(mahler_transient_carry_sheet, "physical_carry_sheet", forbidden)
    monkeypatch.setattr(
        mahler_transient_carry_sheet, "select_repeat_response", select_once
    )
    workspace = AntihydraArithmeticTerm(0).arithmetic_image()
    source = _cyclic_source(128)
    try:
        assert workspace.transient_powered_effect(128, source) is not None
        assert requests == 1
    finally:
        workspace.dispose()


@pytest.mark.parametrize("q", (2, 3, 6, 32, 64))
@pytest.mark.parametrize("tail", (-1, 0, 1))
def test_punctured_leaf_and_partial_zero_prefix_match_literal(
    q: int,
    tail: int,
) -> None:
    width = q + tail
    h = (5 << (q - 1)) + 1
    term = AntihydraArithmeticTerm(0)
    workspace = term.arithmetic_image()
    source = append_source(
        workspace,
        DyadicReturnSourceRecord(
            h % (1 << width), width, h >> width, None, None, None, 0, True
        ),
    )
    image = workspace.scheduler.source_image(
        workspace, source, workspace.action_for_extent(width)
    )
    view = workspace.scheduler.source_image_core().view(image)
    summary = dyadic_image_summary(workspace, view)
    expected_h, delta, minimum, _odd_steps, failure = literal_antihydra_summary(
        h, width
    )
    transfer = summary.transfer
    assert (transfer.upper * h + transfer.offset) // transfer.lower == expected_h
    assert (summary.delta, summary.minimum) == (delta, minimum)
    assert workspace.first_failure(view) == failure
    assert summary.support is not None
    support = workspace.support_node(summary.support)
    assert (
        support.saturated and support.branch_word is None and support.children is None
    )
    if tail == -1:
        assert (
            term.ledger.counters.get(
                "antihydra_arithmetic_temporal_punctured_event_actions", 0
            )
            == 0
        )
    elif width <= workspace.MAX_LEAF_STEPS:
        assert (
            term.ledger.counters[
                "antihydra_arithmetic_temporal_punctured_event_actions"
            ]
            >= 1
        )


def test_public_source_and_lazy_mahler_share_closed_leaf_publication(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = AntihydraArithmeticTerm(64)
    workspace = term.arithmetic_image()
    event_actions = term.ledger.counters[
        "antihydra_arithmetic_temporal_punctured_event_actions"
    ]

    def forbidden_event_replay(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("published source image replayed punctured events")

    # The scheduler has already published the complete source image. Results
    # and the later Mahler projection must consume that publication instead of
    # reopening the arithmetic event constructor.
    monkeypatch.setattr(workspace, "punctured_steps", forbidden_event_replay)
    assert event_actions > 0
    with monkeypatch.context() as optional:
        optional.setattr(mahler_cache, "ExactRational", forbidden_event_replay)
        optional.setattr(mahler_cache, "SaturatingAffineAction", forbidden_event_replay)
        result = term.result()
    expected = literal_antihydra_summary(8, 64)
    assert (result.h, result.balance, result.minimum, result.first_failure_index) == (
        expected[0],
        expected[1],
        expected[2],
        expected[4],
    )
    assert not term.mahler_workspace and not term.audit_snapshot().segments_ready
    assert (
        term.ledger.counters["antihydra_arithmetic_temporal_punctured_event_actions"]
        == event_actions
    )
    assert associated_action(result)["first_failure"] == 2
    assert (
        term.ledger.counters["antihydra_arithmetic_temporal_punctured_event_actions"]
        == event_actions
    )
    assert term.mahler_workspace is not None
    assert term.mahler_workspace.source_workspace is workspace
    assert term.ledger.counters["mahler_source_composed_image_reads"] == 1
    assert not audit_dyadic_return_payloads(term.ledger).invalid


@pytest.mark.parametrize("h", (6, 10, 14, 16))
def test_punctured_leaf_preserves_late_first_failure_without_event_replay(
    h: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    width = 64
    workspace = AntihydraArithmeticTerm(0).arithmetic_image()
    source = append_source(
        workspace, DyadicReturnSourceRecord(h, width, 0, None, None, None, 0, True)
    )
    image = workspace.scheduler.source_image(
        workspace, source, workspace.action_for_extent(width)
    )
    view = workspace.scheduler.source_image_core().view(image)
    expected = literal_antihydra_summary(h, width)[4]
    assert expected is not None and expected > 0

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("first-failure consumer replayed punctured events")

    monkeypatch.setattr(workspace, "punctured_steps", forbidden)
    monkeypatch.setattr(workspace, "source_value", forbidden)
    assert workspace.first_failure(view) == expected
    assert not workspace.demanded_support


def test_punctured_power_budget_releases_transient_workspace() -> None:
    term = AntihydraArithmeticTerm(0)
    workspace = term.arithmetic_image()
    ledger = term.ledger
    scratch = RunArithmeticWorkspace.for_ledger(ledger, workspace.counter_prefix)
    before = ledger.entries, ledger.nodes
    ledger.max_nodes = ledger.nodes + 23
    with pytest.raises(BlockContextBudgetExceeded), scratch.scope():
        tuple(workspace.punctured_steps((5 << 31) + 1, 32, scratch))
    assert (ledger.entries, ledger.nodes) == before
    assert scratch.nodes == 0 and not scratch.active


def test_homogeneous_puncture_precedes_mixed_repeat_sheet(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.antihydra import mahler_transient_carry_sheet

    def forbidden(_steps: int) -> None:
        pytest.fail("homogeneous source opened a mixed-row carry sheet")

    monkeypatch.setattr(mahler_transient_carry_sheet, "physical_carry_sheet", forbidden)
    workspace = AntihydraArithmeticTerm(0).arithmetic_image()
    h = (5 << 31) + 1
    scratch = RunArithmeticWorkspace.for_ledger(
        workspace.ledger, workspace.counter_prefix
    )
    with scratch.scope():
        actions = tuple(workspace.punctured_steps(h, 32, scratch, repeat_only=True))
    expected, delta, minimum, odd, _failure = literal_antihydra_summary(h, 32)
    assert actions == ((32, delta, minimum, odd, expected - 1),)


@pytest.mark.parametrize("length", (127, 128))
def test_admitted_cyclic_root_precedes_subtree_opening(
    length: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.hashlife.execution.dyadic_return_transport import (
        balanced_residue_effect,
    )
    from number_compiler.sequences.antihydra.arithmetic_images import (
        AntihydraArithmeticImageWorkspace,
    )

    source = _cyclic_source(length)
    expected = literal_antihydra_summary(source, length)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("the admitted root opened a transient child")

    monkeypatch.setattr(
        AntihydraArithmeticImageWorkspace, "transient_leaf_effect", forbidden
    )
    ledger = ResourceLedger()
    workspace = AntihydraArithmeticImageWorkspace(ledger, 0, shared_cache=False)
    try:
        result = balanced_residue_effect(workspace, length, source)
        _assert_cyclic_summary(result, source, expected)
        transfer = result.transfer
        lifted = source + (3 << length)
        lifted_expected = literal_antihydra_summary(lifted, length)
        assert (
            transfer.upper * lifted + transfer.offset
        ) // transfer.lower == lifted_expected[0]
        assert (result.delta, result.minimum, result.odd_steps) == lifted_expected[1:4]
        assert (
            ledger.counters.get("antihydra_arithmetic_balanced_effect_compositions", 0)
            == 0
        )
    finally:
        workspace.dispose()
    assert ledger.nodes == ledger.entries == 0


def test_partial_cyclic_action_transports_actual_source_lift() -> None:
    from number_compiler.hashlife.execution.dyadic_return_transport import (
        balanced_residue_effect,
    )
    from number_compiler.sequences.antihydra.arithmetic_images import (
        AntihydraArithmeticImageWorkspace,
    )

    width = 128
    source = _cyclic_source(width)
    source ^= 1 << 90
    expected = literal_antihydra_summary(source, width)
    ledger = ResourceLedger()
    workspace = AntihydraArithmeticImageWorkspace(ledger, 0, shared_cache=False)
    try:
        result = balanced_residue_effect(workspace, width, source)
        _assert_cyclic_summary(result, source, expected)
    finally:
        workspace.dispose()
    assert ledger.nodes == ledger.entries == 0


def test_cyclic_root_interruption_releases_scratch_and_stack(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.execution.dyadic_return_transport import (
        balanced_residue_effect,
    )
    from number_compiler.sequences.antihydra.arithmetic_images import (
        AntihydraArithmeticImageWorkspace,
    )

    width = 128
    source = _cyclic_source(width)

    def interrupted(
        _workspace: AntihydraArithmeticImageWorkspace,
        _source: int,
        _width: int,
        _selected: tuple[int, int, int, int, int],
        _scratch: RunArithmeticWorkspace,
    ) -> tuple[int, int, int, int, int]:
        raise KeyboardInterrupt("injected before publication")

    monkeypatch.setattr(
        AntihydraArithmeticImageWorkspace, "_evaluate_repeat", interrupted
    )
    ledger = ResourceLedger()
    workspace = AntihydraArithmeticImageWorkspace(ledger, 0, shared_cache=False)
    try:
        before = (ledger.nodes, ledger.entries)
        with pytest.raises(KeyboardInterrupt, match="injected before publication"):
            balanced_residue_effect(workspace, width, source)
        assert (ledger.nodes, ledger.entries) == before
    finally:
        workspace.dispose()
    assert ledger.nodes == ledger.entries == 0
