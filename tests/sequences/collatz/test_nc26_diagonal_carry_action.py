"""Exact, bounded source-window and diagonal-action regressions."""

from __future__ import annotations

import random
from collections.abc import Callable
from fractions import Fraction
from functools import partial

import pytest

from devtools.verification.oracles.sequence_arithmetic import (
    collatz_literal as physical_collatz_literal,
)
from number_compiler.arithmetic.polynomials.polynomial import (
    polynomial_multiply,
    trim_polynomial,
)
from number_compiler.hashlife.execution.dyadic_return_runs import (
    RunArithmeticWorkspace,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as collatz_keys
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.diagonal_carry_action import (
    CollatzDiagonalSeam,
)
from number_compiler.sequences.collatz.diagonal_source_window import (
    CollatzDiagonalWindow,
    source_window_checkpoint_steps,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalEndpointAction,
)
from number_compiler.sequences.collatz.innovation_input_tape import (
    ParityProgramBuilder,
)
from number_compiler.sequences.collatz.source_cylinder_cache import (
    CollatzDyadicMacros,
)
from number_compiler.sequences.collatz.tape_width import CollatzTapeWidthSummary
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)
from tests.support.reference_arithmetic import normalized_collatz_word


def _ignore_step() -> None:
    return None


def test_diagonal_source_windows_match_independent_physical_and_normalized_runs() -> (
    None
):
    rng = random.Random(26026)
    cases = [
        (1, 0),
        (1, 1),
        (3, 3),
        (27, 97),
        ((1 << 70) - 1, 512),
        (95 * (1 << 80) - 1, 1050),
    ]
    cases.extend((rng.randrange(1, 1 << 100), rng.randrange(1, 500)) for _ in range(24))
    for source, budget in cases:
        work: list[int] = []
        steps: list[int] = []
        reservations: list[int] = []
        window = CollatzDiagonalWindow.from_source_window(
            source,
            budget,
            retain_parity_mask=True,
            record_step=partial(steps.append, 1),
            reserve_bits=reservations.append,
            record_work=work.append,
        )
        expected_normalized, expected_word = normalized_collatz_word(
            source, window.action.steps
        )
        assert window.normalized_endpoint == expected_normalized
        assert window.physical_endpoint == physical_collatz_literal(
            source, window.physical_ticks
        )
        assert window.action.endpoint(source) == expected_normalized
        assert window.odd_symbols == sum(expected_word)
        assert window.parity_mask == sum(
            bit << i for i, bit in enumerate(expected_word)
        )
        assert len(steps) == window.action.steps
        assert len(work) >= window.action.steps + 1
        assert all(operand_bits > 0 for operand_bits in work)
        assert reservations and all(bits > 0 for bits in reservations)
        assert window.physical_ticks <= budget

    pending = CollatzDiagonalWindow.from_source_window(
        3,
        3,
        record_step=_ignore_step,
        reserve_bits=lambda _bits: None,
        record_work=lambda _bits: None,
    )
    assert pending.action.steps == 1
    assert pending.phase == 1
    assert pending.physical_ticks == 3
    assert pending.normalized_endpoint == 5
    assert pending.physical_endpoint == 16


def test_diagonal_window_reserves_before_any_symbol_work() -> None:
    work: list[int] = []

    def reject(_bits: int) -> None:
        raise MemoryError("request-local window reservation refused")

    with pytest.raises(MemoryError, match="reservation refused"):
        CollatzDiagonalWindow.from_source_window(
            (1 << 90) + 321,
            400,
            record_step=_ignore_step,
            reserve_bits=reject,
            record_work=work.append,
        )
    assert work == []


def test_production_window_is_offered_before_catalogue_candidate_veto() -> None:
    from number_compiler.resources.process_cache import clear_process_cache
    from number_compiler.sequences.collatz.temporal_unified_skew_execution import (
        has_unified_source_parent,
    )

    clear_process_cache()
    source = (1 << 200) + 931386509544713451
    ticks = 1000
    # The catalogue has a candidate here, but this is not an issued action.
    assert has_unified_source_parent(source, ticks)
    try:
        term = PoweredCollatzTerm(source, ticks, shared_cache=True)
        assert term.materialize(max_bits=1000) == physical_collatz_literal(
            source, ticks
        )
        counters = term.resource_ledger.counters
        assert (
            counters[collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NTH_DIAGONAL_SOURCE_WINDOWS]
            > 0
        )
        assert (
            counters[collatz_keys.COLLATZ_HASHLIFE_PRIMITIVE_STEPS]
            >= counters[
                collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NTH_DIAGONAL_PRODUCER_STEPS
            ]
        )
    finally:
        clear_process_cache()


def test_diagonal_source_window_retains_same_pass_aligned_prefixes() -> None:
    source = (1 << 200) + 931386509544713451
    work: list[int] = []
    steps: list[int] = []
    reservations: list[int] = []
    prefix_steps = source_window_checkpoint_steps(8, 256)
    assert prefix_steps == (8, 24, 56, 120, 248, 256)
    assert source_window_checkpoint_steps(0, 256) == (8, 16, 32, 64, 128, 256)
    window = CollatzDiagonalWindow.from_source_window(
        source,
        1000,
        max_normalized=256,
        retain_parity_mask=True,
        prefix_steps=prefix_steps,
        record_step=partial(steps.append, 1),
        reserve_bits=reservations.append,
        record_work=work.append,
    )

    prefixes = window.prefixes
    assert tuple(prefix.action.steps for prefix in prefixes) == prefix_steps
    assert all(
        prefix.action.endpoint(source) == prefix.normalized_endpoint
        for prefix in prefixes
    )
    assert all(
        prefix.odd_symbols
        == sum(normalized_collatz_word(source, prefix.action.steps)[1])
        for prefix in prefixes
    )
    assert len(steps) == window.action.steps
    assert reservations and len(work) > window.action.steps

    unmasked_steps: list[int] = []
    unmasked = CollatzDiagonalWindow.from_source_window(
        source,
        1000,
        max_normalized=256,
        prefix_steps=prefix_steps,
        record_step=partial(unmasked_steps.append, 1),
        reserve_bits=lambda _bits: None,
        record_work=lambda _bits: None,
    )
    assert len(unmasked_steps) == len(steps)
    assert tuple(
        (prefix.action.steps, prefix.odd_symbols, prefix.normalized_endpoint)
        for prefix in unmasked.prefixes
    ) == tuple(
        (prefix.action.steps, prefix.odd_symbols, prefix.normalized_endpoint)
        for prefix in prefixes
    )

    def reject_prefix_reservation(_bits: int) -> None:
        raise MemoryError("prefix reservation refused")

    with pytest.raises(MemoryError, match="prefix reservation"):
        CollatzDiagonalWindow.from_source_window(
            source,
            1000,
            max_normalized=256,
            prefix_steps=prefix_steps,
            record_step=_ignore_step,
            reserve_bits=reject_prefix_reservation,
            record_work=work.append,
        )


def test_diagonal_window_certificate_binds_the_copied_fields() -> None:
    window = CollatzDiagonalWindow.from_source_window(
        (1 << 80) + 321,
        300,
        retain_parity_mask=True,
        record_step=_ignore_step,
        reserve_bits=lambda _bits: None,
        record_work=lambda _bits: None,
    )
    endpoint = window.normalized_endpoint
    object.__setattr__(window, "normalized_endpoint", endpoint + 1)
    with pytest.raises(ValueError, match="changed|coordinates"):
        window.require_issued()
    object.__setattr__(window, "normalized_endpoint", endpoint)
    window.require_issued()


def test_same_pass_window_parity_is_published_as_one_exact_factor() -> None:
    source = 95 * (1 << 80) - 1
    window = CollatzDiagonalWindow.from_source_window(
        source,
        400,
        retain_parity_mask=True,
        record_step=_ignore_step,
        reserve_bits=lambda _bits: None,
        record_work=lambda _bits: None,
    )
    endpoint, expected_word = normalized_collatz_word(source, window.action.steps)
    ledger = ResourceLedger()
    with ParityProgramBuilder(source, ledger) as builder:
        builder.append_diagonal_window(
            window,
            reserve_bits=lambda _bits: None,
            max_width=512,
        )
        program = builder.finish(
            endpoint,
            steps=window.action.steps,
            one_symbols=window.odd_symbols,
        )
        assert program.producer_issued
        observed_word = tuple(
            bit
            for factor in program.factors
            for _ in range(factor.repetitions)
            for bit in factor.motif
        )
        assert observed_word == expected_word


def test_wide_root_scheduler_consumes_windows_and_short_root_stays_lazy() -> None:
    source = (1 << 70) - 1
    ticks = 512
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        source,
        ticks,
        ledger=ledger,
        prefer_source_closed_d8=True,
    )
    assert result.endpoint == physical_collatz_literal(source, ticks)
    assert result.physical_ticks == ticks
    assert (
        ledger.counters.get(
            collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NTH_DIAGONAL_SOURCE_WINDOWS, 0
        )
        > 0
    )
    assert ledger.counters.get(
        collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NTH_DIAGONAL_PRODUCER_STEPS, 0
    ) >= ledger.counters.get(
        collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NTH_DIAGONAL_CERTIFIED_SYMBOLS, 0
    )
    assert (
        ledger.counters.get(
            collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NTH_DIAGONAL_PRODUCER_OPERAND_BITS,
            0,
        )
        > 0
    )

    short_ledger = ResourceLedger()
    short = compile_collatz_temporal_run_quotient(
        27,
        64,
        ledger=short_ledger,
        prefer_source_closed_d8=True,
    )
    assert short.endpoint == physical_collatz_literal(27, 64)
    assert (
        short_ledger.counters.get(
            collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NTH_DIAGONAL_PRODUCER_STEPS, 0
        )
        == 0
    )


def test_large_source_window_advances_the_published_prefix_cursor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.process_cache import clear_process_cache

    seed = (1 << 1100) + 931386509544713451
    observed_root_d256: list[tuple[int, int]] = []
    source_window_field_demands: list[bool] = []
    original_observe = CollatzDyadicMacros.observe
    original_window_factory = CollatzDiagonalWindow.from_source_window

    def check_window_factory(
        owner: type[CollatzDiagonalWindow],
        source: int,
        physical_budget: int,
        *,
        max_normalized: int = 256,
        retain_parity_mask: bool = False,
        retain_field_action: bool = True,
        prefix_steps: tuple[int, ...] = (),
        record_step: Callable[[], None],
        reserve_bits: Callable[[int], None],
        record_work: Callable[[int], None],
    ) -> CollatzDiagonalWindow:
        if owner is not CollatzDiagonalWindow:
            raise AssertionError("window factory was rebound to a foreign class")
        window = original_window_factory(
            source,
            physical_budget,
            max_normalized=max_normalized,
            retain_parity_mask=retain_parity_mask,
            retain_field_action=retain_field_action,
            prefix_steps=prefix_steps,
            record_step=record_step,
            reserve_bits=reserve_bits,
            record_work=record_work,
        )
        source_window_field_demands.append(retain_field_action)
        assert not retain_field_action
        assert type(window.action) is DyadicTerminalEndpointAction
        return window

    def record_observe(
        owner: CollatzDyadicMacros,
        source: int,
        width: int,
        ones: int,
        endpoint: int,
        *,
        anchor: int,
        tape_width_summary: CollatzTapeWidthSummary | None = None,
    ) -> None:
        if source == seed and width == 256:
            observed_root_d256.append((ones, endpoint))
        original_observe(
            owner,
            source,
            width,
            ones,
            endpoint,
            anchor=anchor,
            tape_width_summary=tape_width_summary,
        )

    monkeypatch.setattr(
        CollatzDiagonalWindow, "from_source_window", classmethod(check_window_factory)
    )
    monkeypatch.setattr(CollatzDyadicMacros, "observe", record_observe)
    clear_process_cache()
    try:
        ledger = ResourceLedger()
        result = compile_collatz_temporal_run_quotient(
            seed,
            2048,
            ledger=ledger,
            shared_cache=True,
            prefer_source_closed_d8=True,
        )
        assert result.endpoint == physical_collatz_literal(seed, 2048)
        assert (
            ledger.counters[
                collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NTH_DIAGONAL_SOURCE_WINDOWS
            ]
            > 0
        )
        assert source_window_field_demands
        # The source-window producer assembles D256 from aligned adjacent
        # chunks. The next iteration must not republish that cumulative action
        # directly from the original seed.
        assert observed_root_d256 == []

        receiving_seed = seed + (1 << 1200)
        warm_ledger = ResourceLedger()
        warm_result = compile_collatz_temporal_run_quotient(
            receiving_seed,
            2048,
            ledger=warm_ledger,
            shared_cache=True,
            prefer_source_closed_d8=True,
        )
        assert warm_result.endpoint == physical_collatz_literal(receiving_seed, 2048)
        assert (
            warm_ledger.counters.get(
                "collatz_hashlife_occurrence_applied_parent_hits", 0
            )
            > 0
        )
    finally:
        clear_process_cache()


def test_wide_powered_term_consumes_same_pass_window_with_innovation() -> None:
    source = (1 << 70) - 1
    ticks = 512
    term = PoweredCollatzTerm(source, ticks, shared_cache=False)
    term.prepare_joint_cocycle()
    term.prepare_innovation_tape(complete_word=True, modulus=49)
    workspace = term.source_image()
    joint = workspace.joint_action
    observation = workspace.innovation_observation
    assert joint is not None
    assert observation is not None
    assert observation.producer_issued
    assert observation.source == source
    assert observation.physical_ticks == ticks
    assert joint.endpoint == physical_collatz_literal(source, ticks)
    assert joint.physical_ticks == ticks
    assert workspace.first_boundary_macro is not None
    assert (
        term.resource_ledger.counters.get(
            collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NTH_DIAGONAL_SOURCE_WINDOWS, 0
        )
        > 0
    )
    assert (
        term.resource_ledger.counters.get(
            collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NTH_DIAGONAL_CERTIFIED_SYMBOLS, 0
        )
        > 0
    )


def test_innovation_root_keeps_first_border_and_joins_same_pass_window() -> None:
    source = (1 << 70) - 1
    ticks = 512
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        source,
        ticks,
        ledger=ledger,
        include_joint_cocycle=True,
        include_innovation_tape=True,
        innovation_modulus=49,
        prefer_source_closed_d8=True,
    )
    assert result.endpoint == physical_collatz_literal(source, ticks)
    assert result.first_boundary_stamp is not None
    assert result.first_boundary_macro is not None
    assert result.innovation_observation is not None
    assert result.joint_action is not None
    assert result.joint_action.endpoint == result.endpoint
    assert (
        ledger.counters.get(
            collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NTH_DIAGONAL_SOURCE_WINDOWS, 0
        )
        > 0
    )


def test_diagonal_seam_carries_and_weighted_laurent_are_exact_and_stale_safe() -> None:
    term = PoweredCollatzTerm(3, 2, shared_cache=False)
    term.prepare_joint_cocycle()
    workspace = term.source_image()
    action = workspace.joint_action
    assert action is not None
    seam = term.diagonal_carry_seam()
    assert type(seam) is CollatzDiagonalSeam
    assert (seam.source, seam.normalized_endpoint, seam.physical_endpoint) == (3, 5, 5)

    scratch = RunArithmeticWorkspace.for_ledger(
        term.resource_ledger, "collatz_diagonal_test"
    )
    with scratch.scope():
        assert seam.phase == 0
        assert seam.phase_fraction(
            3, reserve_bits=scratch.require_bits, max_width=4096
        ) == Fraction(5, 8)
        width = seam.required_macro_width
        carries = seam.macro_carries(
            width, reserve_bits=scratch.require_bits, max_width=4096
        )
        gamma = seam.macro_laurent_defect_from_carries(carries, max_width=4096)
        raw = tuple(
            action.fields.gain * ((seam.source >> i) & 1)
            + ((action.fields.offset >> i) & 1)
            for i in range(width)
        )
        shifted_endpoint = tuple(
            0
            if i < seam.normalized_steps
            else (seam.normalized_endpoint >> (i - seam.normalized_steps)) & 1
            for i in range(width)
        )
        quotient_product = polynomial_multiply((-2, 1), gamma)
        coefficient_difference = tuple(
            shifted_endpoint[i] - raw[i] for i in range(width)
        )
        assert coefficient_difference == tuple(
            quotient_product[i] if i < len(quotient_product) else 0
            for i in range(width)
        )

        field = seam.field(
            seam.required_field_width,
            reserve_bits=scratch.require_bits,
            max_width=4096,
        )
        assert field.digits[:3] == (1, 0, 1)
        for index, (multiply, addition) in enumerate(
            zip(
                field.multiply_carries,
                field.addition_carries,
                strict=True,
            ),
            start=1,
        ):
            low = seam.normalized_endpoint & ((1 << index) - 1)
            expected_multiply = (3 * low + 1) // (1 << index)
            expected_addition = (
                expected_multiply
                - (2 * low) // (1 << index)
                - (low + 1) // (1 << index)
            )
            assert multiply == expected_multiply
            assert addition == expected_addition
        weighted = seam.weighted_laurent_defect(
            moving_cut=seam.normalized_steps,
            reserve_bits=scratch.require_bits,
            max_width=4096,
        )
        assert trim_polynomial(
            polynomial_multiply((-2, 1), weighted.carry_coefficients)
        ) == trim_polynomial(weighted.endpoint_defect)

    workspace.dispose()
    with pytest.raises(ValueError, match="stale|authority"):
        seam.field(3, reserve_bits=lambda _bits: None, max_width=4096)
