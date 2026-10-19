"""Adversarial authority and budget-fallback checks for edge macros."""

import pytest

from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as collatz_keys
from number_compiler.sequences.collatz.border_identity import (
    ENTRY_0563,
    ENTRY_421,
    ENTRY_26847_PHASES,
)
from number_compiler.sequences.collatz.boundary_macros import (
    BoundaryActionTemplateMemo,
    admit_routed_boundary_macro_plan,
    select_admitted_boundary_macro,
    validate_admitted_boundary_macro_plan,
)
from number_compiler.sequences.collatz.guarded_port_join import GuardedPortJoin
from number_compiler.sequences.collatz.joint_temporal_action import (
    CollatzJointTemporalBuilder,
)
from number_compiler.sequences.collatz.tape_width import (
    CollatzWidthSpineAccumulator,
)
from number_compiler.sequences.collatz.temporal_border_return_execution import (
    consume_border_return,
    consume_named_boundary,
)
from number_compiler.sequences.collatz.temporal_mixed_execution import (
    MixedRunExecutorState,
)
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)


@pytest.mark.parametrize(
    "source,remaining,tamper,error",
    (
        (164, 100, True, "admission authority"),
        (204, 100, False, "another source or clock"),
        (164, 99, False, "another source or clock"),
    ),
)
def test_invalid_plan_is_rejected_before_reservation(
    source: int, remaining: int, tamper: bool, error: str
) -> None:
    ledger = ResourceLedger(max_nodes=32)
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    width_spine = CollatzWidthSpineAccumulator(ledger, requested=False)
    plan = admit_routed_boundary_macro_plan(164, 100)
    assert plan is not None and plan.identity == ENTRY_421

    # Preserve the genuine source and clock while changing an action exponent.
    # The sealed issue tuple must reject this before normalized_symbols can
    # drive a large transient reservation.
    if tamper:
        object.__setattr__(plan, "repetitions", 1_000_000)
    state = MixedRunExecutorState(source, remaining, 0, 0, 0, 0, 0, 0, None, None)
    with (
        scratch.scope(),
        BoundaryActionTemplateMemo(ledger) as templates,
        CollatzJointTemporalBuilder(
            ledger, scratch, 164, requested=False, shared_cache=False
        ) as joint_builder,
        pytest.raises(ValueError, match=error),
    ):
        consume_named_boundary(
            state,
            plan,
            seed=164,
            ledger=ledger,
            scratch=scratch,
            control_bits=0,
            templates=templates,
            include_joint=False,
            width_spine=width_spine,
            joint_builder=joint_builder,
            parity_builder=None,
            macros=None,
            prior_lookup_enabled=False,
        )

    assert scratch.nodes == 0
    assert ledger.nodes == 0
    assert ledger.counters.get("collatz_physical_temporal_scratch_peak_bits", 0) == 0


def test_optional_border_preflight_preserves_scratch_for_exact_fallback() -> None:
    # The 6305 candidate from 190 takes 12 physical ticks. The independent
    # 0563 plan takes 9, and its 480-bit scratch bound fits exactly in 24 nodes.
    # Reserve 20 nodes for prior work; the optional border needs 25 and must
    # decline without releasing or corrupting that prior reservation.
    ledger = ResourceLedger(max_nodes=24)
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    width_spine = CollatzWidthSpineAccumulator(ledger, requested=False)
    state = MixedRunExecutorState(190, 13, 0, 0, 0, 0, 0, 0, None, None)
    fallback = admit_routed_boundary_macro_plan(state.current, state.remaining)
    assert fallback is not None
    assert (fallback.identity, fallback.repetitions, fallback.physical_ticks) == (
        ENTRY_0563,
        2,
        9,
    )

    with (
        scratch.scope(),
        CollatzJointTemporalBuilder(
            ledger, scratch, state.current, requested=False, shared_cache=False
        ) as joint_builder,
    ):
        scratch.require_bits(256)
        prior_nodes = scratch.nodes
        assert prior_nodes == ledger.nodes == 20

        next_state, border = consume_border_return(
            state,
            seed=state.current,
            ledger=ledger,
            scratch=scratch,
            control_bits=0,
            include_joint=False,
            width_spine=width_spine,
            joint_builder=joint_builder,
            parity_builder=None,
            macros=None,
            minimum_useful_physical_ticks=fallback.physical_ticks,
        )

        assert (next_state, border) == (None, None)
        assert scratch.nodes == prior_nodes
        assert ledger.nodes == prior_nodes
        assert (
            ledger.counters[
                "collatz_physical_border_return_candidate_alternate_route_fallbacks"
            ]
            == 1
        )

        # The retained prior allocation plus the admitted exact fallback's
        # scratch requirement still fits, so the optional refusal did not
        # poison the receiving query's lower-cost route.
        fallback_bits = 8 * (
            state.current.bit_length() + 4 * fallback.normalized_symbols + 32
        )
        scratch.require_bits(fallback_bits)
        assert scratch.nodes == ledger.nodes == 24
        action = select_admitted_boundary_macro(fallback)
        assert action.source == state.current
        assert action.physical_ticks == fallback.physical_ticks
        validate_admitted_boundary_macro_plan(fallback)


def test_named_boundary_consumer_reuses_its_pointed_pair_certificate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    width_spine = CollatzWidthSpineAccumulator(ledger, requested=False)
    state = MixedRunExecutorState(164, 100, 0, 0, 0, 0, 0, 0, None, None)
    plan = admit_routed_boundary_macro_plan(state.current, state.remaining)
    assert plan is not None

    def reject_duplicate_point_puncture(
        _joined: GuardedPortJoin, _source: int, *, check_last: bool = True
    ) -> object:
        raise AssertionError("named consumer rebuilt its certified pointed pair")

    monkeypatch.setattr(
        GuardedPortJoin, "require_pointed", reject_duplicate_point_puncture
    )
    with (
        scratch.scope(),
        BoundaryActionTemplateMemo(ledger) as templates,
        CollatzJointTemporalBuilder(
            ledger, scratch, state.current, requested=True, shared_cache=False
        ) as joint_builder,
    ):
        next_state, boundary, _ = consume_named_boundary(
            state,
            plan,
            seed=state.current,
            ledger=ledger,
            scratch=scratch,
            control_bits=0,
            templates=templates,
            include_joint=True,
            width_spine=width_spine,
            joint_builder=joint_builder,
            parity_builder=None,
            macros=None,
            prior_lookup_enabled=False,
        )

    assert next_state.current == boundary.endpoint
    assert ledger.counters[collatz_keys.COLLATZ_POINTED_PAIR_CERTIFICATE_REUSES] == 1


def test_border_return_consumer_reuses_its_pointed_pair_certificate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    width_spine = CollatzWidthSpineAccumulator(ledger, requested=False)
    state = MixedRunExecutorState(30, 9, 0, 0, 0, 0, 0, 0, None, None)

    def reject_duplicate_point_puncture(
        _joined: GuardedPortJoin, _source: int, *, check_last: bool = True
    ) -> object:
        raise AssertionError("border-return consumer rebuilt its pointed pair")

    monkeypatch.setattr(
        GuardedPortJoin, "require_pointed", reject_duplicate_point_puncture
    )
    with (
        scratch.scope(),
        CollatzJointTemporalBuilder(
            ledger, scratch, state.current, requested=True, shared_cache=False
        ) as joint_builder,
    ):
        next_state, border = consume_border_return(
            state,
            seed=state.current,
            ledger=ledger,
            scratch=scratch,
            control_bits=0,
            include_joint=True,
            width_spine=width_spine,
            joint_builder=joint_builder,
            parity_builder=None,
            macros=None,
        )

    assert next_state is not None and border is not None
    assert next_state.current == border.endpoint
    assert ledger.counters[collatz_keys.COLLATZ_POINTED_PAIR_CERTIFICATE_REUSES] == 1


@pytest.mark.parametrize(
    "phase,identity",
    (
        (0, ENTRY_26847_PHASES[0]),
        (1, ENTRY_26847_PHASES[1]),
        (2, ENTRY_26847_PHASES[2]),
        (3, ENTRY_26847_PHASES[3]),
        (4, ENTRY_26847_PHASES[4]),
    ),
)
@pytest.mark.parametrize("repetitions", (1, 2))
def test_rotated_edge_macro_innovation_accepts_short_and_powered_factors(
    phase: int, identity: object, repetitions: int
) -> None:
    source = 592 >> phase
    physical_ticks = 5 * repetitions + 1 - phase
    result = compile_collatz_temporal_run_quotient(
        source,
        physical_ticks,
        ledger=ResourceLedger(),
        include_innovation_tape=True,
        innovation_modulus=49,
        shared_cache=False,
    )

    expected = source
    for _ in range(physical_ticks):
        expected = 3 * expected + 1 if expected & 1 else expected // 2

    assert result.endpoint == expected
    assert result.first_boundary_macro is not None
    assert result.first_boundary_macro.identity == identity
    assert result.first_boundary_macro.repetitions == repetitions
    assert result.innovation_observation is not None
    assert result.innovation_observation.physical_ticks == physical_ticks
