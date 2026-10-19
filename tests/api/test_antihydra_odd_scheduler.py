"""Production TileScheduler refinement for guarded odd-to-odd actions."""

from __future__ import annotations

import pytest

from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
    DyadicReturnLaw,
)
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicImageSummary,
    DyadicReturnImageID,
    DyadicReturnSourceID,
)
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageDemand,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra import arithmetic_images
from number_compiler.sequences.antihydra.arithmetic_images import (
    AntihydraArithmeticImageWorkspace,
)
from number_compiler.sequences.antihydra.mahler_mixed_harmonic_ring import (
    MahlerMixedOddHarmonicRing,
)
from number_compiler.sequences.antihydra.mahler_source_actions import (
    MahlerOccurrenceConsumer,
)
from tests.support.mahler_harmonic_reference import (
    literal_antihydra_summary,
    source_for_motif,
)


def _requested_summary(
    workspace: AntihydraArithmeticImageWorkspace, source: DyadicReturnSourceID
) -> DyadicImageSummary:
    demand = SourceImageDemand("physical-summary")
    image = workspace.scheduler.source_image_demanded(
        workspace, source, workspace.root_action, demand
    )
    payload = workspace.scheduler.source_projection(workspace, image, demand).value
    assert type(payload) is DyadicReturnImageID
    return workspace.image_node(payload).summary


def test_scheduler_applies_mixed_odd_macro_with_bounded_partial_suffix(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source_h = source_for_motif((1, 2), 128) + 1
    width = 394
    ledger = ResourceLedger()
    workspace = AntihydraArithmeticImageWorkspace(ledger, width, shared_cache=False)
    try:
        source = workspace.admitted_source(source_h, width)

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("powered admitted macro fell back to child discovery")

        monkeypatch.setattr(workspace, "complete_composite_candidate", forbidden)
        monkeypatch.setattr(workspace, "_source_value", forbidden)
        before = dict(ledger.counters)
        summary = _requested_summary(workspace, source)
        transfer = summary.transfer
        endpoint, remainder = divmod(
            transfer.upper * source_h + transfer.offset, transfer.lower
        )
        expected = literal_antihydra_summary(source_h, width)[:4]
        assert remainder == 0
        assert (endpoint, summary.delta, summary.minimum, summary.odd_steps) == expected
        assert summary.width == width
        assert (
            ledger.counters["antihydra_arithmetic_temporal_odd_macro_evaluations"]
            - before.get("antihydra_arithmetic_temporal_odd_macro_evaluations", 0)
            == 1
        )
        assert (
            ledger.counters["antihydra_arithmetic_temporal_odd_macro_return_steps"]
            - before.get("antihydra_arithmetic_temporal_odd_macro_return_steps", 0)
            == 393
        )
        assert (
            ledger.counters["antihydra_arithmetic_temporal_odd_macro_residual_steps"]
            - before.get("antihydra_arithmetic_temporal_odd_macro_residual_steps", 0)
            == 1
        )
        assert (
            ledger.counters["antihydra_arithmetic_temporal_odd_macro_selector_events"]
            - before.get("antihydra_arithmetic_temporal_odd_macro_selector_events", 0)
            >= 2
        )
        assert (
            ledger.counters[
                "antihydra_arithmetic_temporal_odd_macro_selector_operand_bits"
            ]
            - before.get(
                "antihydra_arithmetic_temporal_odd_macro_selector_operand_bits", 0
            )
            > 0
        )
        assert (
            ledger.counters.get("antihydra_arithmetic_temporal_balanced_routes", 0)
            - before.get("antihydra_arithmetic_temporal_balanced_routes", 0)
            == 0
        )
    finally:
        workspace.dispose()


def test_scheduler_keeps_total_arithmetic_after_ledger_failure() -> None:
    ledger = ResourceLedger()
    workspace = AntihydraArithmeticImageWorkspace(ledger, 4, shared_cache=False)
    try:
        # h=6 has centered D=5 and a=4. The first odd macro's ledger change is
        # -1, but arithmetic remains total and publishes the exact endpoint.
        source = workspace.admitted_source(6, 4)
        summary = _requested_summary(workspace, source)
        expected = literal_antihydra_summary(6, 4)[:4]
        assert (summary.width, summary.delta, summary.minimum, summary.odd_steps) == (
            4,
            expected[1],
            expected[2],
            expected[3],
        )
        assert summary.minimum < 0
    finally:
        workspace.dispose()


def test_warm_parent_hit_bypasses_odd_macro_reconstruction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source_h = source_for_motif((1, 2), 128) + 1
    width = 394
    workspace = AntihydraArithmeticImageWorkspace(
        ResourceLedger(), width, shared_cache=False
    )
    try:
        source = workspace.admitted_source(source_h, width)
        demand = SourceImageDemand("physical-summary")
        first = workspace.scheduler.source_image_demanded(
            workspace, source, workspace.root_action, demand
        )

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("warm parent hit reconstructed its odd macro")

        monkeypatch.setattr(
            arithmetic_images,
            "select_source_certified_odd_macro",
            forbidden,
        )
        monkeypatch.setattr(MahlerMixedOddHarmonicRing, "power", forbidden)
        monkeypatch.setattr(type(workspace), "_punctured_steps", forbidden)
        second = workspace.scheduler.source_image_demanded(
            workspace, source, workspace.root_action, demand
        )
        assert second == first
    finally:
        workspace.dispose()


def test_powered_odd_macro_preserves_negative_ledger_minimum() -> None:
    source_h = source_for_motif((4,), 128) + 1
    width = 520
    ledger = ResourceLedger()
    workspace = AntihydraArithmeticImageWorkspace(ledger, width, shared_cache=False)
    try:
        source = workspace.admitted_source(source_h, width)
        summary = _requested_summary(workspace, source)
        expected = literal_antihydra_summary(source_h, width)[:4]
        transfer = summary.transfer
        endpoint, remainder = divmod(
            transfer.upper * source_h + transfer.offset, transfer.lower
        )
        assert remainder == 0
        assert (
            summary.width,
            endpoint,
            summary.delta,
            summary.minimum,
            summary.odd_steps,
        ) == (
            width,
            expected[0],
            expected[1],
            expected[2],
            expected[3],
        )
        assert summary.minimum < 0
        assert (
            ledger.counters["antihydra_arithmetic_temporal_odd_macro_evaluations"] == 1
        )
    finally:
        workspace.dispose()


def test_failed_odd_macro_publication_releases_scratch_and_rolls_back(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source_h = source_for_motif((1, 2), 128) + 1
    width = 394
    ledger = ResourceLedger()
    workspace = AntihydraArithmeticImageWorkspace(ledger, width, shared_cache=False)
    try:
        source = workspace.admitted_source(source_h, width)
        workspace.scheduler.source_image_origin(workspace, source)
        support_count, image_count = len(workspace.support), len(workspace.images)
        compositions_before = ledger.counters.get(
            "antihydra_arithmetic_temporal_odd_macro_evaluations", 0
        )

        def fail_target_image(_node: object) -> None:
            raise RuntimeError("injected odd macro publication failure")

        monkeypatch.setattr(workspace, "_append_image", fail_target_image)
        demand = SourceImageDemand("physical-summary")
        with pytest.raises(RuntimeError, match="injected odd macro publication"):
            workspace.scheduler.source_image_demanded(
                workspace, source, workspace.root_action, demand
            )
        assert len(workspace.support) == support_count
        assert len(workspace.images) == image_count
        assert (
            ledger.counters["antihydra_arithmetic_temporal_odd_macro_evaluations"]
            - compositions_before
            == 1
        )
        scratch = RunArithmeticWorkspace.for_ledger(ledger, workspace.counter_prefix)
        assert scratch.nodes == 0 and not scratch.active
    finally:
        workspace.dispose()


def test_dispose_cleans_base_workspace_and_preserves_primary_release_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    workspace = AntihydraArithmeticImageWorkspace(
        ledger, 8, shared_cache=False, prepare_mahler=True
    )
    owner = workspace.mahler_binding_owner
    bindings = workspace.mahler_bindings
    assert owner is not None and bindings is not None and len(bindings) == 1

    release = ledger.release
    failed = False

    def fail_binding_release(owner_id: int, entries: int = 0, nodes: int = 0) -> None:
        nonlocal failed
        if owner_id == owner and not failed:
            failed = True
            raise RuntimeError("injected Mahler release failure")
        release(owner_id, entries=entries, nodes=nodes)

    base_dispose = DyadicReturnImageWorkspace.dispose

    def fail_after_base_cleanup(
        base_workspace: DyadicReturnImageWorkspace,
    ) -> None:
        base_dispose(base_workspace)
        raise RuntimeError("injected base cleanup failure")

    monkeypatch.setattr(ledger, "release", fail_binding_release)
    monkeypatch.setattr(DyadicReturnImageWorkspace, "dispose", fail_after_base_cleanup)
    with pytest.raises(RuntimeError) as raised:
        workspace.dispose()

    assert workspace.finite_cache_audit_snapshot().closed
    assert workspace.mahler_bindings is bindings
    assert len(workspace.actions) == 0
    chain = (raised.value, raised.value.__cause__, raised.value.__context__)
    assert any(
        isinstance(error, RuntimeError)
        and "injected Mahler release failure" in str(error)
        for error in chain
    )
    assert any(
        isinstance(error, RuntimeError)
        and "injected base cleanup failure" in str(error)
        for error in chain
    )

    monkeypatch.setattr(DyadicReturnImageWorkspace, "dispose", base_dispose)
    workspace.dispose()
    assert workspace.mahler_bindings is None
    assert workspace.mahler_binding_owner is None
    inventory = ledger.inventory_owner(owner)
    assert inventory.entries == inventory.nodes == 0


def test_constructor_preserves_primary_error_when_consumer_close_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    base_init = DyadicReturnImageWorkspace.__init__

    def fail_after_base_init(
        workspace: DyadicReturnImageWorkspace,
        base_ledger: ResourceLedger,
        seed: int,
        steps: int,
        law: DyadicReturnLaw,
    ) -> None:
        base_init(workspace, base_ledger, seed, steps, law)
        raise RuntimeError("injected primary constructor failure")

    consumer_close = MahlerOccurrenceConsumer.close

    def close_then_fail(consumer: MahlerOccurrenceConsumer) -> None:
        consumer_close(consumer)
        raise RuntimeError("injected consumer close failure")

    monkeypatch.setattr(DyadicReturnImageWorkspace, "__init__", fail_after_base_init)
    monkeypatch.setattr(MahlerOccurrenceConsumer, "close", close_then_fail)
    workspace = AntihydraArithmeticImageWorkspace.__new__(
        AntihydraArithmeticImageWorkspace
    )
    with pytest.raises(RuntimeError, match="injected consumer close failure") as raised:
        AntihydraArithmeticImageWorkspace.__init__(
            workspace, ledger, 8, shared_cache=False, prepare_mahler=True
        )

    assert workspace.finite_cache_audit_snapshot().closed
    assert (
        raised.value.__cause__ is not None
        and "injected primary constructor failure" in str(raised.value.__cause__)
    )
