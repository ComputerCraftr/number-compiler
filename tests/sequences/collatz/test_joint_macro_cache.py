"""Source authority and bounded reuse for the normalized joint macro cache."""

from dataclasses import replace
from typing import cast

import pytest

from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.process_cache import ProcessCache, clear_process_cache
from number_compiler.sequences.collatz import joint_cylinder_cache
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.joint_cylinder_cache import (
    JointCertifiedMacroCache,
)
from number_compiler.sequences.collatz.joint_temporal_action import (
    CollatzJointTemporalBuilder,
    JointTemporalSpine,
)
from number_compiler.sequences.collatz.source_cylinder_cache import (
    CollatzDyadicMacros,
)
from number_compiler.sequences.collatz.temporal_dyadic import (
    D8CylinderFrame,
    D8TemporalTable,
)
from tests.support.collatz_affine_fixtures import alternating_collatz_source_action


def test_joint_macro_cache_reuses_only_issued_complete_actions() -> None:
    source = (1 << 16) - 1
    action = DyadicTerminalFieldAction.one_run(16)
    with JointCertifiedMacroCache(ResourceLedger(), shared_cache=False) as cache:
        assert cache.remember(source, action, 16)
        assert cache.lookup(source, 16) == (action, 16)
        assert cache.ledger.counters["collatz_hashlife_joint_applied_hits"] == 0
        cache.applied()
        assert cache.ledger.counters["collatz_hashlife_joint_applied_hits"] == 1


@pytest.mark.parametrize(
    ("shared_cache", "process_enabled", "reason"),
    ((False, True, "policy"), (True, False, "disabled")),
)
def test_joint_cache_classifies_non_capacity_bypasses(
    monkeypatch: pytest.MonkeyPatch,
    shared_cache: bool,
    process_enabled: bool,
    reason: str,
) -> None:
    process_cache = ProcessCache(enabled=process_enabled)
    monkeypatch.setattr(
        joint_cylinder_cache, "get_process_cache", lambda: process_cache
    )
    source = (1 << 16) - 1
    action = DyadicTerminalFieldAction.one_run(16)
    with JointCertifiedMacroCache(ResourceLedger(), shared_cache=shared_cache) as cache:
        assert cache.lookup(source, 16) is None
        assert cache.remember(source, action, 16)
        counters = cache.ledger.counters
        assert counters[f"collatz_hashlife_joint_{reason}_bypasses"] == 2
        assert counters["collatz_hashlife_joint_bypasses"] == 0


def test_joint_cache_keeps_capacity_bypasses_in_legacy_lane(
    monkeypatch: pytest.MonkeyPatch,
    publication_blocked_cache: ProcessCache,
) -> None:
    monkeypatch.setattr(
        joint_cylinder_cache,
        "get_process_cache",
        lambda: publication_blocked_cache,
    )
    source = (1 << 16) - 1
    action = DyadicTerminalFieldAction.one_run(16)
    with JointCertifiedMacroCache(ResourceLedger(), shared_cache=True) as cache:
        assert cache.remember(source, action, 16)
        counters = cache.ledger.counters
        assert counters["collatz_hashlife_joint_bypasses"] == 1
        assert counters["collatz_hashlife_joint_disabled_bypasses"] == 0
        assert counters["collatz_hashlife_joint_policy_bypasses"] == 0


def test_joint_cache_miss_does_not_construct_occurrence_high_fiber(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cache = JointCertifiedMacroCache(ResourceLedger(), shared_cache=False)

    def reject_fiber(_source: int, _width: int) -> int:
        raise AssertionError("a miss constructed occurrence high-fiber data")

    monkeypatch.setattr(cache, "_fiber", reject_fiber)
    with cache:
        assert cache.lookup((1 << 131_072) + 27, 16) is None


def test_joint_macro_identity_ignores_publisher_high_fiber() -> None:
    source = (1 << 16) - 1
    transported_source = source + (1 << 16)
    action = DyadicTerminalFieldAction.one_run(16)
    with JointCertifiedMacroCache(ResourceLedger(), shared_cache=False) as cache:
        assert cache.remember(source, action, 16)
        assert not cache.remember(transported_source, action, 16)
        assert cache.lookup(transported_source, 16) == (action, 16)
        assert cache.ledger.counters["collatz_hashlife_joint_transported_hits"] == 1


def test_joint_builder_disposes_batch_owner_if_spine_construction_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")

    def fail_init(*_args: object, **_kwargs: object) -> None:
        raise RuntimeError("injected spine initialization failure")

    monkeypatch.setattr(JointTemporalSpine, "__init__", fail_init)
    with scratch.scope(), pytest.raises(RuntimeError, match="injected spine"):
        CollatzJointTemporalBuilder(
            ledger, scratch, 27, requested=True, shared_cache=False
        )
    assert ledger.entries == 0
    assert ledger.nodes == 0


def test_joint_cache_close_retries_failed_store_after_closing_its_peer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    cache = JointCertifiedMacroCache(ledger, shared_cache=False)
    original = cache.actions.dispose
    calls = 0

    def fail_once() -> None:
        nonlocal calls
        calls += 1
        if calls == 1:
            raise RuntimeError("injected action disposal failure")
        original()

    monkeypatch.setattr(cache.actions, "dispose", fail_once)
    with pytest.raises(RuntimeError, match="action disposal failure"):
        cache.close()
    assert cache._closed
    assert not cache.actions._disposed
    assert cache.frontier._disposed

    cache.close()
    assert cache.actions._disposed
    assert ledger.entries == ledger.nodes == 0


def test_joint_builder_rejects_reentry_and_reuse_after_exit() -> None:
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    builder = CollatzJointTemporalBuilder(
        ledger, scratch, 27, requested=False, shared_cache=False
    )
    with scratch.scope(), builder, pytest.raises(RuntimeError, match="entered twice"):
        builder.__enter__()
    with pytest.raises(RuntimeError, match="closed"):
        builder.__enter__()
    assert ledger.entries == ledger.nodes == 0


def test_parity_builder_failure_unwinds_previously_opened_query_owners(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz.innovation_input_tape import (
        ParityProgramBuilder,
    )
    from number_compiler.sequences.collatz.temporal_run_quotient import (
        compile_collatz_temporal_run_quotient,
    )

    ledger = ResourceLedger()

    def fail_init(*_args: object, **_kwargs: object) -> None:
        raise RuntimeError("injected parity allocation failure")

    monkeypatch.setattr(ParityProgramBuilder, "__init__", fail_init)
    with pytest.raises(RuntimeError, match="injected parity allocation failure"):
        compile_collatz_temporal_run_quotient(
            (1 << 128) + 27,
            256,
            ledger=ledger,
            shared_cache=True,
            include_joint_cocycle=True,
            include_innovation_tape=True,
            innovation_modulus=49,
        )
    assert ledger.entries == ledger.nodes == 0


def test_joint_builder_cleans_up_when_context_entry_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    builder = CollatzJointTemporalBuilder(
        ledger, scratch, 27, requested=True, shared_cache=False
    )
    assert builder.cache is not None

    def fail_entry() -> object:
        raise RuntimeError("injected cache entry failure")

    monkeypatch.setattr(builder.cache, "__enter__", fail_entry)
    with scratch.scope(), pytest.raises(RuntimeError, match="injected cache entry"):
        builder.__enter__()
    assert ledger.entries == ledger.nodes == 0
    with pytest.raises(RuntimeError, match="closed"):
        builder.__enter__()


def test_failed_batch_publication_clears_the_completed_frontier(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    source = (1 << 128) + 255
    builder = CollatzJointTemporalBuilder(
        ledger, scratch, source, requested=True, shared_cache=False
    )
    table = D8TemporalTable.for_ledger(ledger)
    with scratch.scope(), builder:
        frame = D8CylinderFrame(source)
        builder.begin_d8_batch(source)
        last_transition: tuple[DyadicTerminalFieldAction, int, int] | None = None
        for _ in range(2):
            frame, ones, residue, _origin, _width, action = (
                table.transition_with_joint_action(frame)
            )
            builder.append_d8_transition(action, ones, residue)
            last_transition = action, ones, residue
        assert last_transition is not None
        action, ones, residue = last_transition

        def fail_publication(*_args: object, **_kwargs: object) -> bool:
            raise RuntimeError("injected joint cache publication failure")

        assert builder.cache is not None
        monkeypatch.setattr(builder.cache, "remember", fail_publication)
        with pytest.raises(RuntimeError, match="injected joint cache publication"):
            builder.finish_d8_batch(None, frame)
        assert builder._d8_batch_source is None
        with pytest.raises(ValueError, match="no active frame batch"):
            builder.append_d8_transition(action, ones, residue)


def test_joint_cache_rejects_forged_sum_with_same_endpoint() -> None:
    source = (1 << 16) - 1
    action = DyadicTerminalFieldAction.one_run(16)
    endpoint = action.endpoint(source)
    original_sum = action.sum_offset
    object.__setattr__(action, "sum_offset", original_sum + 1)
    assert action.endpoint(source) == endpoint
    assert not action.producer_issued
    with JointCertifiedMacroCache(ResourceLedger(), shared_cache=False) as cache:
        with pytest.raises(ValueError, match="producer action"):
            cache.remember(source, action, 16)
        assert len(cache.actions) == 0


def test_joint_run_rejects_even_normalized_endpoint_with_pending_half_step() -> None:
    from number_compiler.sequences.collatz.joint_temporal_action import (
        CollatzJointRunAction,
    )

    fields = DyadicTerminalFieldAction.zero_run(1)
    with pytest.raises(ValueError, match="requires an odd normalized endpoint"):
        CollatzJointRunAction(
            source=12,
            endpoint=19,
            normalized_endpoint=6,
            physical_ticks=2,
            normalized_steps=1,
            odd_symbols=0,
            phase=1,
            fields=fields,
        )


def test_accumulator_requires_prepared_source_image_and_matches_literal_run() -> None:
    seed, ticks, modulus = 27, 17, 257
    term = PoweredCollatzTerm(seed, ticks, shared_cache=False)
    with pytest.raises(ValueError, match="prepare the joint cocycle"):
        term.accumulator(modulus)
    term.prepare_joint_cocycle()
    current, elapsed, expected = seed, 0, seed
    while elapsed < ticks:
        if current & 1:
            current = 3 * current + 1
            elapsed += 1
            if elapsed == ticks:
                break
        current //= 2
        elapsed += 1
        expected += current
    observation = term.accumulator(modulus)
    assert observation.normalized_accumulator_residue == expected % modulus
    assert observation.source_included
    assert observation.physical_ticks == ticks
    root = term._source_image()
    view = root.scheduler._source_image_core().view(root.root_image)
    joint_ports = tuple(
        cast(tuple[object, ...], port)
        for port in view.binding.boundary_ports
        if isinstance(port, tuple)
        and len(port) > 0
        and port[0] == "collatz-joint-temporal-action-v1"
    )
    assert len(joint_ports) == 1
    joint_port = joint_ports[0]
    assert len(joint_port) > 1
    wire_payload = joint_port[1]
    assert type(wire_payload) is tuple
    typed_payload = cast(tuple[int, ...], wire_payload)
    assert all(type(value) is int for value in typed_payload)
    forged_payload = (
        *typed_payload[:10],
        typed_payload[10] + 1,
        *typed_payload[11:],
    )
    forged_port = (joint_ports[0][0], forged_payload)
    forged_ports = tuple(
        forged_port if port is joint_ports[0] else port
        for port in view.binding.boundary_ports
    )
    with pytest.raises(ValueError, match="producer-issued by this root"):
        root.audit_image_binding(
            replace(view.binding, boundary_ports=forged_ports), view.payload, None
        )
    assert collect_ledger_metrics(term._ledger).resource_audit_complete == 1


def test_joint_lookup_descends_when_only_smaller_paired_macro_is_cached() -> None:
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    source = (1 << 128) + (1 << 64) - 1
    small_action = DyadicTerminalFieldAction.one_run(32)
    large_action = DyadicTerminalFieldAction.one_run(64)
    small_endpoint = small_action.endpoint(source)
    large_endpoint = large_action.endpoint(source)
    builder = CollatzJointTemporalBuilder(
        ledger, scratch, source, requested=True, shared_cache=False
    )
    with (
        scratch.scope(),
        CollatzDyadicMacros(ledger, shared_cache=False) as macros,
        builder,
    ):
        assert macros.remember(source, 32, 32, small_endpoint)
        assert macros.remember(source, 64, 64, large_endpoint)
        assert builder.cache is not None
        assert builder.cache.remember(source, small_action, 32)
        paired = builder.lookup_largest_macro(
            macros, source, 64, 128, include_width=False
        )
        assert paired is not None
        assert paired[0].width == 32
        assert paired[1] == (small_action, 32)


@pytest.mark.usefixtures("isolated_process_cache")
def test_warm_joint_macro_is_consumed_without_reopening_d8(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    clear_process_cache()
    _, first_source = alternating_collatz_source_action(32, 128)
    receiving_source = first_source + (1 << 128)
    first = PoweredCollatzTerm(first_source, 48, shared_cache=True)
    first.prepare_joint_cocycle()
    first.accumulator(257)
    cold = PoweredCollatzTerm(receiving_source, 48, shared_cache=False)
    cold.prepare_joint_cocycle()
    cold.accumulator(257)
    assert (
        cold._ledger.counters.get("collatz_physical_unified_skew_applied_actions", 0)
        >= 1
    )

    def reject_d8_reconstruction(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("warm paired macro reopened D8 construction")

    monkeypatch.setattr(
        D8TemporalTable, "_joint_action_for_row", reject_d8_reconstruction
    )
    monkeypatch.setattr(
        D8TemporalTable, "_action_from_width_row", reject_d8_reconstruction
    )

    def reject_skew_reconstruction(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("warm paired macro fell through to skew selection")

    monkeypatch.setattr(
        "number_compiler.sequences.collatz.temporal_unified_skew_execution.consume_unified_skew_chain",
        reject_skew_reconstruction,
    )
    receiving = PoweredCollatzTerm(receiving_source, 48, shared_cache=True)
    receiving.prepare_joint_cocycle()
    observation = receiving.accumulator(257)
    assert observation.physical_ticks == 48
    assert (
        receiving._ledger.counters.get(
            "collatz_physical_temporal_d8_joint_action_builds", 0
        )
        == 0
    )
    assert (
        receiving._ledger.counters.get("collatz_hashlife_occurrence_process_hits", 0)
        >= 1
    )
    assert (
        receiving._ledger.counters.get("collatz_hashlife_occurrence_applied_hits", 0)
        >= 1
    )
    assert receiving._ledger.counters["collatz_hashlife_joint_process_hits"] >= 1
    assert receiving._ledger.counters["collatz_hashlife_joint_applied_hits"] >= 1


def test_joint_cocycle_cannot_be_retrofitted_after_image_creation() -> None:
    term = PoweredCollatzTerm(27, 4, shared_cache=False)
    term.width()
    with pytest.raises(ValueError, match="must precede"):
        term.prepare_joint_cocycle()
