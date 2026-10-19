"""Production handoff, refusal and output equivalence for conditional Moore powers."""

from dataclasses import replace
from typing import TypedDict
from unittest.mock import patch

import pytest

import number_compiler.sequences.collatz.conditional_border_moore as conditional_graph
import number_compiler.sequences.collatz.conditional_scheduler_adapter as scheduler_adapter
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.border_harmonic_ring import (
    ConstantTail6305Ring,
    PeriodicTail6305Ring,
)
from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.conditional_scheduler_adapter import (
    CertifiedSchedulerCandidate,
    issue_conditional_scheduler_candidate,
)
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)


class _ProjectionOptions(TypedDict, total=False):
    include_f5: bool
    include_joint_cocycle: bool


class _DemandOptions(TypedDict, total=False):
    include_width_spine: bool
    include_innovation_tape: bool
    innovation_modulus: int


def sample(motif: tuple[int, ...], count: int = 64) -> tuple[int, int]:
    residue, modulus = PeriodicTail6305Ring.guard_residue(motif, count)
    residue += ((3 - residue) * pow(modulus, -1, 5) % 5) * modulus
    return residue + 5 * modulus * (1 << 48), count * sum(j + 4 for j in motif)


def scalar_physical(x: int, ticks: int) -> int:
    for _ in range(ticks):
        x = 3 * x + 1 if x & 1 else x >> 1
    return x


def issue_candidate(
    source: int, ticks: int, *, max_coefficient_bits: int = 8192
) -> CertifiedSchedulerCandidate | None:
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "conditional-test")
    with scratch.scope():
        return issue_conditional_scheduler_candidate(
            source,
            ticks,
            scratch=scratch,
            ledger=ledger,
            max_coefficient_bits=max_coefficient_bits,
        )


@pytest.mark.parametrize("motif", ((0, 1), (1, 2)))
@pytest.mark.parametrize(
    "flags",
    (
        {},
        {"include_f5": True},
        {"include_joint_cocycle": True},
        {"include_f5": True, "include_joint_cocycle": True},
    ),
)
def test_certified_mixed_tail_adapter_matches_scalar_and_legacy(
    motif: tuple[int, ...], flags: _ProjectionOptions
) -> None:
    source, ticks = sample(motif)
    candidate = issue_candidate(source, ticks)
    assert candidate is not None
    candidate.verify()
    assert candidate.return_count == 64 * len(motif)
    assert candidate.physical_ticks == ticks
    assert candidate.endpoint == scalar_physical(source, ticks)
    ledger = ResourceLedger()
    new = compile_collatz_temporal_run_quotient(
        source,
        ticks,
        ledger=ledger,
        require_mixed_prefix=True,
        **flags,
    )
    assert ledger.counters.get("collatz_conditional_scheduler_certified_actions") == 1
    with patch.object(
        scheduler_adapter, "issue_conditional_scheduler_candidate", return_value=None
    ):
        original = compile_collatz_temporal_run_quotient(
            source,
            ticks,
            ledger=ResourceLedger(),
            require_mixed_prefix=True,
            **flags,
        )
    assert new.semantic_key == original.semantic_key
    assert new.run_actions == 1
    if flags.get("include_joint_cocycle"):
        assert new.joint_action is not None
        assert new.joint_action.endpoint == candidate.endpoint
    if flags.get("include_f5"):
        assert new.physical_f5 is not None
        assert new.physical_f5.apply(source) == candidate.endpoint % 5


@pytest.mark.parametrize("motif", ((0, 1), (1, 2)))
def test_partial_horizon_is_never_overrun(motif: tuple[int, ...]) -> None:
    source, ticks = sample(motif)
    partial = ticks - 1
    # A full 128-return action would overrun, but a certified smaller
    # 64-return block is a valid prefix; no half-step may be fabricated.
    prefix = issue_candidate(source, partial)
    assert prefix is not None
    assert 0 < prefix.physical_ticks <= partial
    assert prefix.endpoint == scalar_physical(source, prefix.physical_ticks)
    result = compile_collatz_temporal_run_quotient(
        source,
        partial,
        ledger=ResourceLedger(),
        include_f5=True,
    )
    assert result.endpoint == scalar_physical(source, partial)
    assert result.physical_ticks == partial


def test_forced_source_guard_and_immutability_are_checked() -> None:
    source, ticks = sample((0, 1))
    candidate = issue_candidate(source, ticks)
    assert candidate is not None
    with pytest.raises(ValueError, match="clocks/guards"):
        replace(candidate, endpoint=candidate.endpoint + 1).verify()
    with pytest.raises(ValueError, match="clocks/guards"):
        replace(candidate, odd_ticks=candidate.odd_ticks - 1).verify()
    with pytest.raises(ValueError):
        issue_candidate(source, -1)
    with pytest.raises(ValueError):
        issue_candidate(0, ticks)
    with pytest.raises(ValueError):
        issue_candidate(source, ticks, max_coefficient_bits=1)


def test_discovery_budget_is_reserved_before_cylinder_construction() -> None:
    source, ticks = sample((0, 1))
    ledger = ResourceLedger(max_nodes=1)
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "conditional-budget-test")
    with (
        scratch.scope(),
        patch.object(
            CollatzTwoSidedCylinder,
            "from_pointed_source",
            side_effect=AssertionError("discovery ran before its budget preflight"),
        ),
    ):
        candidate = issue_conditional_scheduler_candidate(
            source, ticks, scratch=scratch, ledger=ledger
        )
    assert candidate is None
    assert (
        ledger.counters[_collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_DISCOVERY_ATTEMPTS]
        == 1
    )
    assert (
        ledger.counters[
            _collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_DISCOVERY_BUDGET_REFUSALS
        ]
        == 1
    )
    assert ledger.nodes == 0


def test_successful_discovery_keeps_arithmetic_charged_until_scope_exit() -> None:
    source, ticks = sample((0, 1))
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "conditional-live-test")
    with scratch.scope():
        candidate = issue_conditional_scheduler_candidate(
            source, ticks, scratch=scratch, ledger=ledger
        )
        assert candidate is not None
        assert scratch.nodes > 0
        assert ledger.nodes >= scratch.nodes
        candidate.verify()
    assert scratch.nodes == 0
    assert ledger.nodes == 0


@pytest.mark.parametrize(
    "flags",
    (
        {"include_width_spine": True},
        {"include_innovation_tape": True, "innovation_modulus": 97},
    ),
)
def test_unsupported_publisher_modes_preserve_old_scheduler(
    flags: _DemandOptions,
) -> None:
    source, ticks = sample((1, 2))
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        source, ticks, ledger=ledger, **flags
    )
    assert (
        ledger.counters.get("collatz_conditional_scheduler_certified_actions", 0) == 0
    )
    assert result.endpoint == scalar_physical(source, ticks)
    if flags.get("include_width_spine"):
        assert result.tape_width_summary is not None
    if flags.get("include_innovation_tape"):
        assert result.innovation_observation is not None


def test_completed_mixed_prefix_uses_certified_parent_in_scheduler() -> None:
    source, ticks = sample((1, 2))
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        source,
        ticks,
        ledger=ledger,
        require_mixed_prefix=True,
        include_f5=True,
        include_joint_cocycle=True,
    )
    assert result.endpoint == scalar_physical(source, ticks)
    assert result.physical_ticks == ticks
    assert result.run_actions == 1
    assert ledger.counters.get("collatz_conditional_scheduler_certified_actions") == 1
    assert result.physical_f5 is not None
    assert result.physical_f5.apply(source) == result.endpoint % 5
    assert result.joint_action is not None
    assert result.joint_action.endpoint == result.endpoint


@pytest.mark.parametrize("cache_kind", ("mixed", "dyadic"))
def test_warm_root_parent_is_preferred_to_cold_conditional_discovery(
    cache_kind: str,
) -> None:
    from types import SimpleNamespace
    from unittest.mock import sentinel

    import number_compiler.sequences.collatz.temporal_mixed_execution as mixed

    source, ticks = sample((0, 1))
    ready = mixed.MixedRunExecutorState(
        source + 1,
        0,
        1,
        1,
        0,
        0,
        1,
        1,
        None,
        None,
    )
    mocked_mixed = (
        SimpleNamespace(executor_state=lambda: ready) if cache_kind == "mixed" else None
    )
    mocked_dyadic = ready if cache_kind == "dyadic" else None
    with (
        patch.object(mixed, "consume_cached_mixed_run", return_value=mocked_mixed),
        patch.object(
            mixed, "_consume_cached_root_dyadic_action", return_value=mocked_dyadic
        ),
        patch(
            "number_compiler.sequences.collatz.conditional_scheduler_adapter.issue_conditional_scheduler_candidate",
            side_effect=AssertionError("cold ring must not precede warm cache"),
        ),
    ):
        selected, table = mixed.consume_initial_mixed_route(
            source,
            ticks,
            control_bits=4096,
            templates=sentinel.templates,
            ledger=ResourceLedger(),
            d8_table=None,
            include_width=False,
            width_spine=sentinel.width_spine,
            include_joint=False,
            joint_builder=sentinel.joint_builder,
            parity_builder=None,
            macros=sentinel.macros,
            scratch=sentinel.scratch,
            normalized_f5=None,
            physical_f5=None,
        )
    assert selected is ready
    assert table is None


@pytest.mark.usefixtures("isolated_process_cache")
def test_warm_dyadic_parent_precedes_conditional_discovery(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.process_cache import clear_process_cache
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
    )

    clear_process_cache()
    source, ticks = sample((1, 3), 32)
    candidate = issue_candidate(source, ticks)
    assert candidate is not None and candidate.normalized_steps == 256
    assert candidate.endpoint == scalar_physical(source, ticks)
    # Publish an exact admitted parent through the cache's production owner.
    # This test concerns application order, independently of which cold
    # scheduler route first discovered the source's word.
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as macros:
        assert macros.remember(
            source, candidate.normalized_steps, candidate.odd_ticks, candidate.endpoint
        )
        cell = macros.lookup(source, 256)
        assert cell is not None and cell.width == 256
        physical_ticks = cell.width + cell.odd_symbols

    def reject_cold_discovery(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("a warm dyadic parent must win before cold discovery")

    monkeypatch.setattr(
        scheduler_adapter,
        "issue_conditional_scheduler_candidate",
        reject_cold_discovery,
    )
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        source, physical_ticks, ledger=ledger, shared_cache=True
    )
    assert result.endpoint == cell.apply(source)
    assert result.normalized_symbols == cell.width
    assert ledger.counters["collatz_hashlife_occurrence_applied_hits"] == 1
    assert (
        ledger.counters.get(
            _collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_DISCOVERY_ATTEMPTS, 0
        )
        == 0
    )
    clear_process_cache()


def test_short_named_family_workload_is_unchanged() -> None:
    # Includes complete and partial 421/4721/0563/26847/989/630/305/6305
    # selections and D8 sources without assuming a branch's family label.
    for source in range(1, 191):
        ticks = 29
        result = compile_collatz_temporal_run_quotient(
            source,
            ticks,
            ledger=ResourceLedger(),
        )
        assert result.endpoint == scalar_physical(source, ticks)
        assert result.odd_ticks + result.division_ticks == ticks


@pytest.mark.parametrize("shared", (False, True))
def test_public_root_term_consumes_complete_conditional_parent(shared: bool) -> None:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

    source, ticks = sample((0, 1))
    term = PoweredCollatzTerm(source, ticks, shared_cache=shared)
    try:
        endpoint = term.materialize(max_bits=8192)
        assert endpoint == scalar_physical(source, ticks)
        # Shared-cache roots may already have an exact, cheaper mixed parent.
        # The cold conditional bridge is mandatory only for the uncached route.
        if not shared:
            assert (
                term.resource_ledger.counters.get(
                    "collatz_conditional_scheduler_certified_actions"
                )
                == 1
            )
        # A completed parent must survive the exact source-image root scope.
        assert (
            term.resource_ledger.counters.get(
                "collatz_physical_temporal_run_quotient_compilations"
            )
            == 1
        )
    finally:
        if term._workspace is not None:
            term._workspace.dispose()


def test_shared_root_falls_through_to_conditional_when_legacy_parent_misses() -> None:
    import number_compiler.sequences.collatz.temporal_mixed_execution as mixed

    source, ticks = sample((0, 1))
    with (
        patch.object(mixed, "consume_cached_mixed_run", return_value=None),
        patch.object(mixed, "_consume_cached_root_dyadic_action", return_value=None),
        patch.object(mixed, "select_mixed_macro", return_value=(None, None)),
    ):
        ledger = ResourceLedger()
        result = compile_collatz_temporal_run_quotient(
            source,
            ticks,
            ledger=ledger,
            shared_cache=True,
            require_mixed_prefix=True,
        )
    assert result.endpoint == scalar_physical(source, ticks)
    assert result.run_actions == 1
    assert ledger.counters.get("collatz_conditional_scheduler_certified_actions") == 1


def test_public_joint_root_is_issued_from_the_same_admitted_parent() -> None:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

    source, ticks = sample((1, 2))
    term = PoweredCollatzTerm(source, ticks, shared_cache=True)
    try:
        term.prepare_joint_cocycle()
        observation = term.accumulator(97)
        root = term.true_root_morphism()
        # Either a warm cached parent or an admitted conditional one is valid.
        assert root.ticks == ticks == observation.physical_ticks
        assert root.first.value == source
        assert root.last.value == scalar_physical(source, ticks)
        assert root.port_action is not None
        root.validate()
    finally:
        if term._workspace is not None:
            term._workspace.dispose()


@pytest.mark.parametrize("motif", ((0, 1), (1, 2)))
@pytest.mark.parametrize("extra_ticks", (1, 124))
def test_partial_root_power_feeds_exact_residual_scheduler(
    motif: tuple[int, ...], extra_ticks: int
) -> None:
    source, powered_ticks = sample(motif)
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        source,
        powered_ticks + extra_ticks,
        ledger=ledger,
        require_mixed_prefix=True,
        include_f5=True,
        include_joint_cocycle=True,
        shared_cache=False,
    )
    assert result.endpoint == scalar_physical(source, powered_ticks + extra_ticks)
    assert result.physical_ticks == powered_ticks + extra_ticks
    assert result.run_actions >= 2
    assert ledger.counters.get("collatz_conditional_scheduler_certified_actions") == 1
    assert (
        ledger.counters.get("collatz_conditional_scheduler_physical_ticks")
        == powered_ticks
    )
    assert result.physical_f5 is not None
    assert result.physical_f5.apply(source) == result.endpoint % 5
    assert result.joint_action is not None
    assert result.joint_action.endpoint == result.endpoint
    # Residual D8 rows legitimately outlive the request; conditional scratch
    # and guard memos must not. Their ledger accounts are fully reconciled.
    remaining = tuple(
        owner for owner in ledger.inventory() if owner.entries or owner.nodes
    )
    assert {owner.name for owner in remaining} <= {
        "collatz-physical-d8-local-table",
        "collatz-physical-d8-width-prefix-table",
    }
    assert all(owner.accounting_delta == 0 for owner in remaining)


def test_shared_root_skips_unhelpful_partial_compilation() -> None:
    # Before the repair the CLI spent time certifying a 576-tick power, then
    # either discarded it or paid more than the cheaper balanced source route.
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

    source, _ = sample((0, 1))
    term = PoweredCollatzTerm(source, 700, shared_cache=True)
    try:
        assert term.materialize(max_bits=8192) == scalar_physical(source, 700)
        assert (
            term.resource_ledger.counters.get(
                "collatz_conditional_scheduler_discovery_attempts", 0
            )
            == 0
        )
    finally:
        if term._workspace is not None:
            term._workspace.dispose()


def test_guarded_source_port_reuses_other_admitted_fiber() -> None:
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
    )

    source, ticks = sample((0, 1))
    ledger = ResourceLedger()
    with CollatzDyadicMacros(ledger, shared_cache=True) as macros:
        scratch = RunArithmeticWorkspace.for_ledger(ledger, "conditional-cache-test")
        with scratch.scope():
            first = issue_conditional_scheduler_candidate(
                source, ticks, scratch=scratch, ledger=ledger, macros=macros
            )
            assert first is not None
            transported_source = source + first.port.guard.modulus
            assert first.port.admits(transported_source)
            with patch.object(
                conditional_graph,
                "try_compile_conditional_repeated_motif",
                side_effect=AssertionError("the exact guarded port should be reused"),
            ):
                transported = issue_conditional_scheduler_candidate(
                    transported_source,
                    ticks,
                    scratch=scratch,
                    ledger=ledger,
                    macros=macros,
                )
            assert transported is not None
            assert transported.port == first.port
            assert transported.endpoint == scalar_physical(transported_source, ticks)
            assert (
                ledger.counters.get(
                    "collatz_conditional_scheduler_guarded_cache_hits", 0
                )
                == 1
            )
    assert ledger.entries == ledger.nodes == 0


def test_same_source_memo_hit_uses_issued_observer_payload_without_rebuilding() -> None:
    from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
        UpperNumeratorF5Matrix,
    )
    from number_compiler.sequences.collatz.guarded_port_join import GuardedPortJoin
    from number_compiler.sequences.collatz.guarded_radix6_bridge import (
        GuardedRadix6Bridge,
    )
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
    )

    returns = 64
    residue, modulus = ConstantTail6305Ring.guard_residue(0, returns)
    # The odd lift adds one factor of 2 to x+1 and makes x == 3 mod 5.
    lift = 5 * (1 << 172) + 1
    source = residue + modulus * lift
    ticks = 4 * returns
    zero_tail = ConstantTail6305Ring.from_source(source)
    assert source % 10 == 3
    assert source.bit_length() >= 256
    assert (source + 1) % (1 << 130) == 0
    assert zero_tail.tail == 0 and zero_tail.admits(returns)
    ledger = ResourceLedger()
    with CollatzDyadicMacros(ledger, shared_cache=True) as macros:
        scratch = RunArithmeticWorkspace.for_ledger(ledger, "same-source-cache-test")
        with scratch.scope():
            first = issue_conditional_scheduler_candidate(
                source,
                ticks,
                scratch=scratch,
                ledger=ledger,
                macros=macros,
                include_f5=True,
                include_joint=True,
            )
            assert first is not None
            assert first.return_count == returns
            assert first.physical_ticks == ticks == 256
            assert first.joined_port is not None
            assert first.carry_program is not None
            assert first.upper_sturmian is not None

            def forbidden(*_args: object, **_kwargs: object) -> object:
                raise AssertionError("same-source cache hit rebuilt an observer")

            with (
                patch.object(GuardedPortJoin, "__post_init__", forbidden),
                patch.object(GuardedPortJoin, "authenticate_weighted_ports", forbidden),
                patch.object(
                    GuardedRadix6Bridge,
                    "demanded_zero_tail_sturmian_factor",
                    forbidden,
                ),
                patch.object(UpperNumeratorF5Matrix, "from_trace", forbidden),
                patch(
                    "number_compiler.sequences.collatz.guarded_radix6_bridge.certify_guarded_radix6_bridge",
                    forbidden,
                ),
            ):
                reused = issue_conditional_scheduler_candidate(
                    source,
                    ticks,
                    scratch=scratch,
                    ledger=ledger,
                    macros=macros,
                    include_f5=True,
                    include_joint=True,
                )
            assert reused is first
            assert (
                ledger.counters["collatz_conditional_scheduler_guarded_cache_hits"] == 1
            )
    assert ledger.entries == ledger.nodes == 0


def test_same_source_memo_hit_rejects_mutated_nested_carry_counts() -> None:
    import copy

    from number_compiler.sequences.collatz.source_closed_port_action import (
        MacroTraceGrammar,
    )
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
    )

    source, ticks = sample((0, 1))
    ledger = ResourceLedger()
    with CollatzDyadicMacros(ledger, shared_cache=True) as macros:
        scratch = RunArithmeticWorkspace.for_ledger(ledger, "tampered-cache-test")
        with scratch.scope():
            candidate = issue_conditional_scheduler_candidate(
                source,
                ticks,
                scratch=scratch,
                ledger=ledger,
                macros=macros,
                include_joint=True,
            )
            assert candidate is not None
            assert candidate.carry_program is not None
            with pytest.raises(ValueError, match="memo issuance seal is invalid"):
                macros.remember_conditional_port(
                    candidate=copy.copy(candidate), demand=2, coefficient_budget=8192
                )
            object.__setattr__(
                candidate.carry_program,
                "carry_tens",
                candidate.carry_program.carry_tens + 1,
            )
            with pytest.raises(ValueError, match="issuance seal is invalid"):
                issue_conditional_scheduler_candidate(
                    source,
                    ticks,
                    scratch=scratch,
                    ledger=ledger,
                    macros=macros,
                    include_joint=True,
                )
            object.__setattr__(
                candidate.carry_program,
                "carry_tens",
                candidate.carry_program.carry_tens - 1,
            )
            zero_count = next(
                name
                for name in (
                    "forced_six_reset_events",
                    "forced_six_div_remainders",
                    "port_punctures",
                    "matrix_compositions",
                    "matrix_squarings",
                    "scalar_steps",
                )
                if getattr(candidate.carry_program, name) == 0
            )
            assert type(getattr(candidate.carry_program, zero_count)) is int
            object.__setattr__(candidate.carry_program, zero_count, False)
            with pytest.raises(ValueError, match="issuance seal is invalid"):
                issue_conditional_scheduler_candidate(
                    source,
                    ticks,
                    scratch=scratch,
                    ledger=ledger,
                    macros=macros,
                    include_joint=True,
                )
            object.__setattr__(candidate.carry_program, zero_count, 0)
            assert candidate.tail_trace is not None
            assert candidate.tail_trace.left is not None
            nested = candidate.tail_trace.left
            object.__setattr__(nested, "left", nested)
            object.__setattr__(nested, "right", MacroTraceGrammar.leaf(()))
            object.__setattr__(nested, "letters", ())
            with pytest.raises(ValueError, match="memo issuance seal is invalid"):
                issue_conditional_scheduler_candidate(
                    source,
                    ticks,
                    scratch=scratch,
                    ledger=ledger,
                    macros=macros,
                    include_joint=True,
                )
    assert ledger.entries == ledger.nodes == 0


def test_negative_conditional_memo_is_exact_horizon_scoped() -> None:
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
    )

    source, ticks = sample((1, 2))
    ledger = ResourceLedger()
    with CollatzDyadicMacros(ledger, shared_cache=True) as macros:
        scratch = RunArithmeticWorkspace.for_ledger(ledger, "conditional-miss-test")
        with scratch.scope():
            with patch.object(
                conditional_graph,
                "try_compile_conditional_repeated_motif",
                return_value=None,
            ) as compile_probe:
                for horizon in (ticks, ticks, ticks + 1):
                    assert (
                        issue_conditional_scheduler_candidate(
                            source,
                            horizon,
                            scratch=scratch,
                            ledger=ledger,
                            macros=macros,
                        )
                        is None
                    )
            assert compile_probe.call_count == 2
            assert (
                ledger.counters.get(
                    "collatz_conditional_scheduler_negative_cache_hits", 0
                )
                == 1
            )
    assert ledger.entries == ledger.nodes == 0


def test_common_collatz_import_does_not_load_conditional_graph() -> None:
    import subprocess
    import sys

    code = (
        "import sys; "
        "import number_compiler.sequences.collatz.temporal_run_executor; "
        "assert 'number_compiler.sequences.collatz.conditional_border_moore' "
        "not in sys.modules; "
        "assert 'number_compiler.sequences.collatz.conditional_scheduler_adapter' "
        "not in sys.modules"
    )
    subprocess.run([sys.executable, "-c", code], check=True, timeout=10)


def test_pointed_fast_refusal_makes_no_large_discovery_reservation() -> None:
    # An ordinary >256-bit source ending in 3 does not satisfy any of the
    # finite driver congruences; the expensive cylinder is never constructed.
    source = (1 << 300) + 7
    assert source % 10 == 3
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "conditional-fast-test")
    with scratch.scope():
        with patch.object(
            CollatzTwoSidedCylinder,
            "from_pointed_source",
            side_effect=AssertionError("unqualified source reached cylinder"),
        ):
            assert (
                issue_conditional_scheduler_candidate(
                    source, 700, scratch=scratch, ledger=ledger
                )
                is None
            )
        assert ledger.counters.get("collatz_conditional_scheduler_fast_refusals") == 1
        assert (
            ledger.counters.get("collatz_conditional_scheduler_discovery_attempts", 0)
            == 0
        )
    assert ledger.entries == ledger.nodes == 0
