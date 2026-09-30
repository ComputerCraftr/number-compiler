"""The public tile authority owns scoped reverse source-sector bounds."""

from tests.support.assertions import assert_rejected_atomically


from collections.abc import MutableMapping
from dataclasses import replace
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockEffect, _effect_key
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.polynomials.frobenius_sector import (
    DECIMAL_REVERSE_GROWTH_CERTIFICATE,
    ReverseFrobeniusPlan,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution import tile_kernel_validation
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_tasks import CausalFrame
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.observation.tile_projection import build_tile_projection
from number_compiler.resources.causal_workspace import _ACTION_ADMISSION_NODES
from number_compiler.resources.field_image_payload_audit import (
    audit_field_image_payloads,
)
from number_compiler.resources.ledger import ResourceLedger


def test_public_reverse_action_composes_sector_bounds_before_source_descent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=4, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as p:
        application = p._application
        adapter = p.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("temporal sector composition visited source digits")

        monkeypatch.setattr(p.scheduler.tiles, "point", forbidden)
        primitive = application.action
        f16, f4 = adapter.power(primitive, 16), adapter.power(primitive, 4)
        f20 = adapter.compose(f16, f4)
        plan = adapter._action(f20).reverse_frobenius
        assert type(plan) is ReverseFrobeniusPlan
        assert plan.steps == 20
        assert tuple(sector.classes for sector in plan.sectors) == (1, 2, 4, 8)
        # This is the conditional symmetric-field certificate. Application
        # observation must establish its hypotheses before dropping the source.
        assert plan.growth_certificate is DECIMAL_REVERSE_GROWTH_CERTIFICATE
        assert plan.annihilated_sectors == (True, True, True, True)
        assert adapter.compose(f4, f16) == f20
        assert adapter.power(primitive, 1024) == adapter.power(primitive, 1024)
        assert ledger.counters["reverse_frobenius_plan_compositions"] > 0
        assert ledger.counters.get("source_annihilations", 0) == 0
        assert application._root is None


def test_warm_action_rejects_a_frobenius_plan_for_another_depth() -> None:
    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=4, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as p:
        adapter = p.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        primitive = p._application.action
        powered = adapter.power(primitive, 8)
        record = adapter._action(powered)
        adapter._actions[powered.local_id] = replace(
            record, reverse_frobenius=adapter._action(primitive).reverse_frobenius
        )
        assert_rejected_atomically(
            ledger,
            lambda: adapter.power(powered, 1),
            ValueError,
            match="differs from its temporal action",
        )
        adapter._actions[powered.local_id] = record


def test_warm_action_rejects_mutated_frobenius_sector_without_a_validation_cache() -> (
    None
):
    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=4, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as projection:
        adapter = projection.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        powered = adapter.power(projection._application.action, 8)
        plan = adapter._action(powered).reverse_frobenius
        assert type(plan) is ReverseFrobeniusPlan
        sector = plan.sectors[0]
        original = sector.valuation_lower_bound
        object.__setattr__(sector, "valuation_lower_bound", original + 1)
        before = ledger.snapshot()
        try:
            with pytest.raises(ValueError, match="differs from its temporal action"):
                adapter.validate_action(powered)
            assert ledger.snapshot() == before
        finally:
            object.__setattr__(sector, "valuation_lower_bound", original)


def test_internal_action_reads_skip_deep_semantic_and_sector_revalidation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=4, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as projection:
        adapter = projection.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        powered = adapter.power(projection._application.action, 8)
        deep_reconstructions = 0

        def counted_effect_key(effect: BlockEffect) -> object:
            nonlocal deep_reconstructions
            deep_reconstructions += 1
            return _effect_key(effect)

        monkeypatch.setattr(tile_kernel_validation, "_effect_key", counted_effect_key)
        before = ledger.snapshot()
        for _ in range(64):
            assert adapter._action_record(powered).repetitions == 8
        assert deep_reconstructions == 0
        adapter.validate_action(powered)
        assert deep_reconstructions == 1
        assert ledger.snapshot() == before


@pytest.mark.parametrize("warm", (False, True), ids=("cold", "warm"))
@pytest.mark.parametrize("poison", ("sector", "effect"))
def test_post_admission_action_poison_rejects_before_source_demand(
    poison: str,
    warm: bool,
) -> None:
    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=4, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as projection:
        application = projection._application
        adapter = application.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        if warm:
            application.point(0)
        record = adapter._actions[application.action.local_id]
        kernel = adapter.kernels.kernel(record.kernel)
        plan = record.reverse_frobenius
        assert type(plan) is ReverseFrobeniusPlan
        target = plan.sectors[0] if poison == "sector" else kernel.effect
        attribute = "valuation_lower_bound" if poison == "sector" else "base"
        original = getattr(target, attribute)
        assert type(original) is int
        before = ledger.snapshot()
        object.__setattr__(target, attribute, original + 1)
        try:
            with pytest.raises(ValueError):
                application.point(0)
            assert ledger.snapshot() == before
        finally:
            object.__setattr__(target, attribute, original)


@pytest.mark.parametrize(
    "operation",
    (
        "children",
        "cocycle",
        "wiring",
        "ports",
        "law",
        "symmetry",
        "fused-action",
        "fused-wiring",
    ),
)
def test_direct_adapter_methods_keep_deep_action_admission(operation: str) -> None:
    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=4, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as projection:
        adapter = projection.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        primitive = projection._application.action
        composite = adapter.power(primitive, 2)
        selected = composite if operation.startswith("fused-") else primitive
        wiring = adapter.wiring(primitive)
        plan = adapter._actions[selected.local_id].reverse_frobenius
        assert type(plan) is ReverseFrobeniusPlan
        sector = plan.sectors[0]
        original = sector.valuation_lower_bound
        object.__setattr__(sector, "valuation_lower_bound", original + 1)
        before = ledger.snapshot()
        try:
            with pytest.raises(ValueError, match="reverse Frobenius plan differs"):
                if operation == "children":
                    adapter.action_children(selected)
                elif operation == "cocycle":
                    adapter.action_cocycle(selected)
                elif operation == "wiring":
                    adapter.validate_wiring(selected, wiring)
                elif operation == "ports":
                    adapter.initial_ports(selected)
                elif operation == "law":
                    adapter.primitive_law(selected)
                elif operation == "symmetry":
                    adapter.local_symmetry(selected)
                elif operation == "fused-action":
                    adapter.validate_fused_action(selected)
                else:
                    adapter.validate_fused_wiring(selected, wiring, wiring)
            assert ledger.snapshot() == before
        finally:
            object.__setattr__(sector, "valuation_lower_bound", original)


def test_causal_setup_failure_cannot_leave_structural_action_access_enabled(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=4, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as projection:
        application = projection._application
        adapter = application.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        engine = CausalTileEngine(application.scheduler)
        frames = application.scheduler._causal_tasks.frames

        def fail_before_loop(*_args: object) -> None:
            raise RuntimeError("injected frame setup failure")

        monkeypatch.setattr(type(frames), "append", fail_before_loop)
        before = ledger.snapshot()
        visits_before = ledger.counters.get("tile_causal_action_admission_visits", 0)
        with pytest.raises(RuntimeError, match="injected frame setup failure"):
            engine.output(application.action, application.source)
        assert engine._action_admission_token is None
        after = ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
        assert ledger.counters["tile_causal_action_admission_visits"] > visits_before
        plan = adapter._actions[application.action.local_id].reverse_frobenius
        assert type(plan) is ReverseFrobeniusPlan
        sector = plan.sectors[0]
        original = sector.valuation_lower_bound
        object.__setattr__(sector, "valuation_lower_bound", original + 1)
        try:
            with pytest.raises(ValueError, match="reverse Frobenius plan differs"):
                adapter.action_cocycle(application.action)
        finally:
            object.__setattr__(sector, "valuation_lower_bound", original)


def test_causal_action_admission_failure_releases_application_and_workspace(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=4, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as projection:
        application = projection._application
        adapter = application.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        engine = CausalTileEngine(application.scheduler)
        engine._application = application.identity

        def fail_admission(_action: object) -> None:
            raise ValueError("injected action admission failure")

        monkeypatch.setattr(adapter, "validate_action", fail_admission)
        before = ledger.snapshot()
        visits_before = ledger.counters.get("tile_causal_action_admission_visits", 0)
        frame = CausalFrame("point", (application.action, application.source, 0, 0, 0))
        with pytest.raises(ValueError, match="injected action admission failure"):
            engine._run(frame, tile_result=False)
        after = ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
        assert engine._application is None
        assert engine._action_admission_token is None
        assert ledger.counters["tile_causal_action_admission_visits"] == (
            visits_before + 1
        )


def test_causal_structural_access_is_limited_to_the_reachable_run_dag(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=4, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as projection:
        application = projection._application
        adapter = application.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        unrelated = adapter.admit(BaseBlockEffect(3))
        engine = CausalTileEngine(application.scheduler)
        other_engine = CausalTileEngine(application.scheduler)
        frames = application.scheduler._causal_tasks.frames
        before = ledger.snapshot()
        observed: list[tuple[int, int]] = []

        def inspect_admission(*_args: object) -> None:
            admitted = application.scheduler._causal_tasks.action_admitted
            observed.append((len(admitted), ledger.entries - before.entries))
            assert ledger.nodes - before.nodes == _ACTION_ADMISSION_NODES * len(
                admitted
            )
            assert not audit_field_image_payloads(ledger).invalid
            assert all(row.accounting_delta == 0 for row in ledger.inventory())
            admitted_action = next(iter(admitted))
            marker = admitted[admitted_action]
            raw_admitted = cast(
                "MutableMapping[object, object]",
                admitted,
            )
            raw_admitted[admitted_action] = False
            assert (
                application.scheduler._causal_tasks.action_admitted_owner,
                id(False),
            ) in audit_field_image_payloads(ledger).invalid
            raw_admitted[admitted_action] = marker
            with pytest.raises(ValueError, match="outside this run's admitted DAG"):
                engine._cocycle(unrelated)
            for invalid in (True, 0.0):
                with pytest.raises(TypeError, match="field action ID"):
                    engine._cocycle(cast("FieldCellActionID", invalid))
            with pytest.raises(RuntimeError, match="cannot reenter"):
                engine._run(
                    CausalFrame(
                        "point",
                        (application.action, application.source, 0, 0, 0),
                    ),
                    tile_result=False,
                )
            with pytest.raises(RuntimeError, match="already has an active run"):
                other_engine._run(
                    CausalFrame(
                        "point",
                        (application.action, application.source, 0, 0, 0),
                    ),
                    tile_result=False,
                )
            assert len(admitted) == observed[0][0]
            assert not audit_field_image_payloads(ledger).invalid
            raise RuntimeError("stop after inspecting run admission")

        monkeypatch.setattr(type(frames), "append", inspect_admission)
        with pytest.raises(RuntimeError, match="stop after inspecting run admission"):
            engine.output(application.action, application.source)
        assert observed and observed[0][0] == observed[0][1]
        assert engine._action_admission_token is None
        assert not engine._running
        after = ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)


@pytest.mark.parametrize("base", (2, 3, 5))
def test_other_radices_do_not_receive_a_decimal_sector_certificate(base: int) -> None:
    ledger = ResourceLedger()
    blank = 2 * base - 1
    source = ExactSource((1, 1), base, blank=blank, extent=4, alphabet_size=blank)
    with build_tile_projection(
        BaseBlockEffect(base), SourceGeometry(ledger, source)
    ) as p:
        adapter = p.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        assert (
            adapter._action(adapter.power(p._application.action, 20)).reverse_frobenius
            is None
        )
