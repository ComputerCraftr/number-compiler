"""Exact run arithmetic and its canonical scheduler integration."""

from dataclasses import replace
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.temporal_run_quotient import (
    F5_AFFINE_ALPHABET,
    CollatzAnonymousF5Fiber,
    CollatzPoweredRootVietaProgram,
    compile_collatz_temporal_run_quotient,
    root_fiber_certificate,
)
from tests.support.collatz_affine_fixtures import alternating_collatz_source_action


def test_runs_match_physical_clock_at_every_half_step() -> None:
    for seed in (1, 2, 7, 27, 63, 64, 127):
        expected, odd = seed, 0
        for ticks in range(65):
            result = compile_collatz_temporal_run_quotient(
                seed,
                ticks,
                ledger=ResourceLedger(),
                include_f5=True,
            )
            assert (result.endpoint, result.odd_ticks) == (expected, odd)
            assert result.division_ticks == ticks - odd
            assert result.physical_f5 is not None
            assert result.physical_f5.apply(seed) == expected % 5
            odd += expected & 1
            expected = 3 * expected + 1 if expected & 1 else expected // 2


def test_aggregate_counts_cannot_replace_the_pending_odd_port() -> None:
    seed, ticks = 931386509544713451, 1001
    expected, odd = seed, 0
    for _ in range(ticks):
        last = expected & 1
        odd += last
        expected = 3 * expected + 1 if last else expected // 2
    result = compile_collatz_temporal_run_quotient(seed, ticks, ledger=ResourceLedger())
    assert (result.endpoint, result.odd_ticks, result.division_ticks, result.phase) == (
        expected,
        odd,
        ticks - odd,
        last,
    )
    assert result.phase == 1
    # The downloaded carrier inferred this port from totals, which loses order.
    wrong_phase = int(result.odd_ticks > result.division_ticks)
    assert wrong_phase == 0
    with pytest.raises(ValueError, match="pending odd half-step"):
        replace(result, phase=wrong_phase)


def test_large_source_d8_batch_materializes_its_high_fiber_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz.temporal_dyadic import D8CylinderFrame

    # This regression is specifically about the D8 materialization route; the
    # independently tested source-certified chain may now own this same seed.
    monkeypatch.setattr(
        "number_compiler.sequences.collatz.temporal_run_executor.consume_unified_skew_chain",
        lambda *_args, **_kwargs: None,
    )

    seed = (1 << 131_072) + 27
    materialize = D8CylinderFrame.materialize
    observed: list[tuple[int, int]] = []

    def once(frame: D8CylinderFrame) -> int:
        observed.append((frame.source, frame.consumed))
        assert len(observed) == 1
        assert frame.source is seed
        assert frame.consumed <= 64
        return materialize(frame)

    monkeypatch.setattr(D8CylinderFrame, "materialize", once)
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        seed, 64, ledger=ledger, include_f5=True
    )
    expected, odd = seed, 0
    for _ in range(64):
        bit = expected & 1
        odd += bit
        expected = 3 * expected + 1 if bit else expected // 2
    assert (result.endpoint, result.odd_ticks) == (expected, odd)
    assert result.physical_f5 is not None
    assert result.physical_f5.apply(seed) == expected % 5
    assert len(observed) == 1
    assert ledger.counters["collatz_physical_temporal_dyadic_d8_pumps"] >= 3
    assert ledger.counters["collatz_physical_temporal_d8_frame_materializations"] == 1
    assert ledger.counters["collatz_physical_temporal_d8_source_window_bits"] > 0


def test_joint_d8_batch_materialization_is_single_and_fully_counted(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz.temporal_dyadic import D8CylinderFrame

    _, source = alternating_collatz_source_action(64, 131_072)
    original_materialize = D8CylinderFrame.materialize
    calls: list[int] = []

    def counted(frame: D8CylinderFrame) -> int:
        calls.append(frame.consumed)
        return original_materialize(frame)

    monkeypatch.setattr(D8CylinderFrame, "materialize", counted)
    ordinary_ledger = ResourceLedger()
    ordinary = compile_collatz_temporal_run_quotient(source, 96, ledger=ordinary_ledger)
    ordinary_calls = tuple(calls)
    assert ordinary_calls == (64,)
    assert ordinary_ledger.counters[
        "collatz_physical_temporal_d8_frame_materializations"
    ] == len(ordinary_calls)

    calls.clear()
    joint_ledger = ResourceLedger()
    joint = compile_collatz_temporal_run_quotient(
        source, 96, ledger=joint_ledger, include_joint_cocycle=True
    )
    joint_calls = tuple(calls)
    assert joint.endpoint == ordinary.endpoint
    assert joint_calls == ordinary_calls == (64,)
    assert joint_ledger.counters[
        "collatz_physical_temporal_d8_frame_materializations"
    ] == len(joint_calls)
    assert joint_ledger.counters["collatz_hashlife_joint_d8_batches"] == 1
    assert joint.joint_action is not None
    assert joint.joint_action.fields.steps == joint.normalized_symbols


def test_small_source_keeps_direct_d8_path(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz import temporal_run_executor as runs

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("small source allocated a cylinder cursor")

    monkeypatch.setattr(runs, "D8CylinderFrame", forbidden)
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(27, 64, ledger=ledger)
    assert result.endpoint == 1619
    # Route selection can fuse several former scalar/D8 actions into one
    # source-authenticated 6305 return. Assert the resulting action, not the
    # obsolete count of intermediate run records.
    assert ledger.counters["collatz_physical_boundary_6305R_macro_actions"] > 0
    assert result.division_ticks + result.odd_ticks == 64
    assert (
        ledger.counters.get("collatz_physical_temporal_d8_frame_materializations", 0)
        == 0
    )


def test_long_zero_and_one_runs_are_single_actions() -> None:
    zero = compile_collatz_temporal_run_quotient(1 << 512, 512, ledger=ResourceLedger())
    one = compile_collatz_temporal_run_quotient(
        (1 << 256) - 1, 512, ledger=ResourceLedger()
    )
    assert zero.endpoint == 1 and zero.run_actions == 1
    assert one.endpoint == 3**256 - 1 and one.run_actions == 1
    assert one.description_bits >= one.source.bit_length() + one.endpoint.bit_length()
    assert one.semantic_key == replace(one, run_actions=99).semantic_key
    with pytest.raises(IndexError):
        one.radix_digit(10, 10**9)


def test_anonymous_root_fiber_is_explicit_and_optional(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("deterministic endpoint enumerated anonymous roots")

    monkeypatch.setattr(CollatzAnonymousF5Fiber, "multiply", forbidden)
    monkeypatch.setattr(type(F5_AFFINE_ALPHABET), "__getitem__", forbidden)
    result = compile_collatz_temporal_run_quotient(27, 256, ledger=ResourceLedger())
    assert result.endpoint == 4
    assert result.root_certificate is None
    assert result.normalized_f5 is None
    monkeypatch.undo()
    certificate = root_fiber_certificate(8)
    assert (certificate.support_size, certificate.amplitude_square) == (20, 256)


def test_powered_vieta_construction_and_composition_do_not_evaluate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("symbolic root program evaluated its multiplicities")

    monkeypatch.setattr(CollatzAnonymousF5Fiber, "source_symbol_fiber", forbidden)
    monkeypatch.setattr(CollatzAnonymousF5Fiber, "multiply", forbidden)
    monkeypatch.setattr(type(F5_AFFINE_ALPHABET), "__getitem__", forbidden)
    program = CollatzPoweredRootVietaProgram(10**18)
    assert program.semantic_key == ("collatz-f5-vieta-power-v1", 10**18)
    assert program.square() == program.then(program)
    assert program.then(CollatzPoweredRootVietaProgram(0)) == program


def test_explicit_root_certificate_retains_all_scale_program_without_evaluation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("certificate evaluated its all-scale program")

    monkeypatch.setattr(CollatzPoweredRootVietaProgram, "evaluate", forbidden)
    ledger = ResourceLedger()
    certificate = root_fiber_certificate(10**18, ledger=ledger)
    assert certificate.powered_symbols == 10**18
    assert (
        certificate.depth,
        certificate.support_size,
        certificate.amplitude_square,
    ) == (8, 20, 256)
    assert ledger.counters["collatz_physical_temporal_root_cayley_products"] == 8
    assert ledger.counters["collatz_physical_temporal_root_vieta_programs"] == 1
    assert (
        ledger.counters["collatz_physical_temporal_root_vieta_powered_symbols"]
        == 10**18
    )


def test_powered_vieta_explicit_evaluation_and_coordinate_moments() -> None:
    program = CollatzPoweredRootVietaProgram(4)
    direct = CollatzAnonymousF5Fiber.identity()
    for _ in range(4):
        direct = direct.multiply(CollatzAnonymousF5Fiber.source_symbol_fiber())
    assert program.evaluate() == direct
    moments = program.vieta_moments(2)
    coordinates = tuple(
        5 * action.scale + action.offset for action in F5_AFFINE_ALPHABET
    )
    assert moments == tuple(
        sum(
            count * coordinate**degree
            for coordinate, count in zip(coordinates, direct.counts, strict=True)
        )
        for degree in range(3)
    )
    assert moments[0] == 16
    assert (
        CollatzPoweredRootVietaProgram(0).evaluate()
        == CollatzAnonymousF5Fiber.identity()
    )
    certificate = root_fiber_certificate(4)
    assert certificate.powered_multiplicity(F5_AFFINE_ALPHABET[0]) == direct.counts[0]


@pytest.mark.parametrize("symbols", [-1, True, 1.5])
def test_powered_vieta_requires_natural_exact_width(symbols: object) -> None:
    with pytest.raises(ValueError):
        CollatzPoweredRootVietaProgram(cast(int, symbols))


def test_run_contraction_retains_scheduler_authority_and_optional_support() -> None:
    term = PoweredCollatzTerm(27, 64)
    assert term.materialize(max_bits=100) == 1619
    workspace = term._source_image()
    assert len(workspace.support) == 1 and workspace.support[0].saturated
    counters = term._ledger.snapshot().counters
    assert counters["source_image_primitive_applications"] == 1
    assert counters["collatz_physical_run_contraction_publications"] == 1
    assert counters["collatz_physical_temporal_run_actions"] > 0
    assert counters.get("collatz_physical_transient_leaf_steps", 0) == 0
    assert counters.get("collatz_physical_temporal_root_cayley_products", 0) == 0
    assert sum(width for _, width, _ in workspace.segments()) == 64
    assert term.materialize(max_bits=100) == 1619
    image = workspace.image_node(workspace.root_payload)
    object.__setattr__(image.summary.transfer, "offset", 1620)
    with pytest.raises(ValueError):
        term.digit(0)


def test_run_publication_respects_node_budget() -> None:
    term = PoweredCollatzTerm(27, 64, max_context_nodes=1)
    with pytest.raises(BlockContextBudgetExceeded):
        term.materialize(max_bits=100)


def test_run_scratch_reuses_owner_and_rejects_nested_authority() -> None:
    from number_compiler.hashlife.execution.dyadic_return_runs import (
        RunArithmeticWorkspace,
    )

    ledger = ResourceLedger()
    for _ in range(10):
        compile_collatz_temporal_run_quotient(27, 64, ledger=ledger)
    owners = [
        row for row in ledger.inventory() if row.role == "run_arithmetic_workspace"
    ]
    assert len(owners) == 1
    assert owners[0].nodes == 0
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    with (
        scratch.scope(),
        pytest.raises(RuntimeError, match="already active"),
        scratch.scope(),
    ):
        pass
    assert not scratch.active and scratch.nodes == 0


def test_scratch_budget_rejects_before_valuation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz import temporal_dyadic as runs

    def forbidden(value: int) -> int:
        raise AssertionError("valuation ran before scratch budget reservation")

    monkeypatch.setattr(runs, "v2_positive", forbidden)
    ledger = ResourceLedger(max_nodes=1)
    with pytest.raises(BlockContextBudgetExceeded):
        compile_collatz_temporal_run_quotient(27, 64, ledger=ledger)
    assert ledger.nodes == ledger.entries == 0
    assert ledger.peak_nodes == 0


def test_scratch_is_released_on_success_and_arithmetic_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz import temporal_dyadic as runs

    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(27, 64, ledger=ledger)
    assert result.endpoint == 1619
    assert ledger.nodes == 3 * ledger.entries
    assert all(
        row.nodes == 0
        for row in ledger.inventory()
        if row.role == "run_arithmetic_workspace"
    )
    assert ledger.peak_nodes > 0

    def failed_valuation(value: int) -> int:
        raise ArithmeticError("injected failure after reservation")

    monkeypatch.setattr(runs, "v2_positive", failed_valuation)
    with pytest.raises(ArithmeticError, match="injected failure"):
        compile_collatz_temporal_run_quotient(27, 64, ledger=ledger)
    assert ledger.nodes == 3 * ledger.entries
    assert all(
        row.nodes == 0
        for row in ledger.inventory()
        if row.role == "run_arithmetic_workspace"
    )


def test_scratch_growth_refusal_releases_prior_reservation() -> None:
    ledger = ResourceLedger(max_nodes=40)
    with pytest.raises(BlockContextBudgetExceeded):
        compile_collatz_temporal_run_quotient((1 << 128) - 1, 256, ledger=ledger)
    assert ledger.peak_nodes > 0
    assert ledger.nodes == ledger.entries == 0
    assert ledger.counters.get("collatz_physical_temporal_one_run_pumps", 0) == 0


@pytest.mark.parametrize("seed,ticks", [(1 << 256, 128), ((1 << 128) - 1, 256)])
def test_homogeneous_horizon_selects_run_constructor(seed: int, ticks: int) -> None:
    term = PoweredCollatzTerm(seed, ticks)
    term.digit(0)
    counters = term._ledger.counters
    assert counters["collatz_physical_temporal_run_routes"] == 1
    assert counters["collatz_physical_temporal_run_actions"] == 1
    assert counters["collatz_physical_temporal_routing_operand_bits"] > 0
    assert counters.get("collatz_physical_temporal_balanced_routes", 0) == 0


def test_wide_mixed_source_requires_bounded_admission_before_run_compilation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from unittest.mock import Mock

    from number_compiler.sequences.collatz import temporal_run_quotient as runs

    compile_probe = Mock(wraps=runs.compile_collatz_temporal_run_quotient)
    monkeypatch.setattr(runs, "compile_collatz_temporal_run_quotient", compile_probe)
    seed, ticks = (1 << 255) | 0x15, 128
    expected = seed
    for _ in range(ticks):
        expected = 3 * expected + 1 if expected & 1 else expected // 2
    term = PoweredCollatzTerm(seed, ticks)
    assert term.materialize(max_bits=300) == expected
    assert compile_probe.call_count == 1
    assert compile_probe.call_args.kwargs["require_mixed_prefix"] is True
    assert term._ledger.counters["collatz_physical_temporal_balanced_routes"] == 1
    assert term._ledger.counters.get("collatz_physical_temporal_run_actions", 0) == 0


def test_huge_cycle_explicit_audit_and_support_only_expand_finite_prefix(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
    from number_compiler.hashlife.execution import dyadic_return_observers as observers
    from number_compiler.hashlife.execution.dyadic_return_images import (
        DyadicReturnImageWorkspace,
    )
    from number_compiler.hashlife.execution.dyadic_return_records import (
        DyadicReturnLaw,
        DyadicReturnSupportID,
    )
    from number_compiler.hashlife.execution.dyadic_return_transport import (
        balanced_residue_macro as support_prefix,
    )
    from number_compiler.resources import dyadic_return_payload_audit as payload_audit
    from number_compiler.resources.dyadic_return_balanced_audit import (
        _balanced_saturated_audit as audit_prefix,
    )
    from number_compiler.resources.payload_audit import audit_registered_payloads

    def bounded_audit(
        law: DyadicReturnLaw,
        source: int,
        width: int,
        ledger: ResourceLedger,
    ) -> tuple[SkewTransfer[int], int, int, int]:
        assert 0 < width <= 111
        return audit_prefix(law, source, width, ledger)

    def bounded_support(
        workspace: DyadicReturnImageWorkspace,
        width: int,
        residue: int,
    ) -> DyadicReturnSupportID:
        assert 0 < width <= 111
        return support_prefix(workspace, width, residue)

    monkeypatch.setattr(payload_audit, "_balanced_saturated_audit", bounded_audit)
    monkeypatch.setattr(observers, "balanced_residue_macro", bounded_support)
    term = PoweredCollatzTerm(27, 10**26)
    assert term.materialize(max_bits=8) == 4
    workspace = term._source_image()
    cycle = workspace.summary().cycle
    assert cycle is not None and cycle.entry_steps == 111
    report = audit_registered_payloads(term._ledger)
    assert report.unknown_payloads == report.forbidden_future_payloads == 0
    assert next(workspace.segments())[0] == 0
    assert len(workspace.demanded_support) == 1
