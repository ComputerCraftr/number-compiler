"""Source authority and exact arithmetic for the NC19 carry projections."""

from __future__ import annotations

from collections.abc import Generator
from contextlib import contextmanager

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.hashlife.execution.dyadic_return_actions import append_source
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnSourceRecord,
)
from number_compiler.hashlife.execution.dyadic_return_runs import (
    RunArithmeticWorkspace,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.arithmetic_images import (
    AntihydraArithmeticImageWorkspace,
)
from number_compiler.sequences.antihydra.mahler_carry_quotient import (
    IssuedWeightedCarry,
    issued_weighted_carry,
    project_weighted_carry,
)
from number_compiler.sequences.antihydra.mahler_x15_source_morphism import (
    X15CarryMorphism,
    two_parent_x15_floor,
)


def _literal(ticks: int) -> tuple[int, int, int, int]:
    centered = 7
    delta = minimum = odd_h_steps = 0
    for _ in range(ticks):
        bit = centered & 1
        delta += 3 * bit - 1
        minimum = min(minimum, delta)
        odd_h_steps += 1 - bit
        centered = (3 * centered + bit) >> 1
    return centered, delta, minimum, odd_h_steps


def _digits(value: int, width: int) -> list[int]:
    result: list[int] = []
    for _ in range(width):
        value, digit = divmod(value, 10)
        result.append(digit)
    return result


def _carry_tape(digits: list[int], multiplier: int) -> list[int]:
    """Independent decimal long-multiplication reference."""
    carries: list[int] = []
    carry = 0
    for digit in digits[:-1]:
        carry, _remainder = divmod(multiplier * digit + carry, 10)
        carries.append(carry)
    return carries


@contextmanager
def _issued(
    ticks: int,
) -> Generator[
    tuple[
        AntihydraArithmeticImageWorkspace,
        IssuedWeightedCarry,
        RunArithmeticWorkspace,
    ]
]:
    ledger = ResourceLedger()
    workspace = AntihydraArithmeticImageWorkspace(ledger, ticks, shared_cache=False)
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "nc19-weighted-carry-test")
    try:
        with scratch.scope():
            carry = project_weighted_carry(workspace, reserve_bits=scratch.require_bits)
            yield workspace, carry, scratch
    finally:
        workspace.dispose()


@pytest.mark.parametrize("ticks", (0, 1, 6, 64, 128))
def test_weighted_carry_matches_literal_centered_and_physical_orbits(
    ticks: int,
) -> None:
    with _issued(ticks) as (workspace, carry, _scratch):
        endpoint, delta, minimum, odd_h_steps = _literal(ticks)
        assert (
            carry.endpoint(7),
            carry.delta,
            carry.minimum,
            carry.odd_h_steps,
        ) == (endpoint, delta, minimum, odd_h_steps)
        assert carry.innovation == (endpoint << ticks) - 3**ticks * 7
        physical = carry.physical_transfer
        assert physical.offset == (carry.innovation + carry.denominator - carry.gain)
        numerator = physical.upper * 8 + physical.offset
        assert not numerator & (physical.lower - 1)
        assert numerator >> ticks == workspace.endpoint() == endpoint + 1


def test_cold_producer_uses_authenticated_origin_and_request_local_blocks() -> None:
    ledger = ResourceLedger()
    workspace = AntihydraArithmeticImageWorkspace(ledger, 128, shared_cache=False)
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "nc19-cold-producer-test")
    try:
        origin = workspace.scheduler.source_image_origin(
            workspace, workspace.root_source
        )
        source = workspace.scheduler.source_image_view(workspace, origin)
        with scratch.scope():
            carry = issued_weighted_carry(
                workspace,
                source,
                workspace.root_action,
                reserve_bits=scratch.require_bits,
            )
            assert carry.endpoint(7) == workspace.endpoint() - 1
            assert carry.cap_hat is None
        counters = ledger.counters
        requests = counters["antihydra_arithmetic_weighted_carry_requests"]
        block_requests = counters["antihydra_arithmetic_weighted_carry_block_requests"]
        block_hits = counters["antihydra_arithmetic_weighted_carry_block_hits"]
        block_misses = counters["antihydra_arithmetic_weighted_carry_block_misses"]
        leaf_steps = counters["antihydra_arithmetic_weighted_carry_leaf_steps"]
        assert requests >= 1
        assert block_requests > 0
        assert block_hits + block_misses == block_requests
        assert 0 < leaf_steps <= requests * 128
        assert counters["antihydra_arithmetic_weighted_carry_operand_bits"] > 0
    finally:
        workspace.dispose()


def test_failed_cold_producer_publishes_shared_scheduler_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    workspace = AntihydraArithmeticImageWorkspace(ledger, 128, shared_cache=False)
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "nc19-cold-failure-test")
    try:
        origin = workspace.scheduler.source_image_origin(
            workspace, workspace.root_source
        )
        source = workspace.scheduler.source_image_view(workspace, origin)
        counters_before = ledger.counters
        requests_before = counters_before.get(
            "antihydra_arithmetic_weighted_carry_block_requests", 0
        )
        misses_before = counters_before.get(
            "antihydra_arithmetic_weighted_carry_block_misses", 0
        )
        steps_before = counters_before.get(
            "antihydra_arithmetic_weighted_carry_leaf_steps", 0
        )

        def fail_after_shared_work(
            owner: AntihydraArithmeticImageWorkspace,
            _width: int,
            _residue: int,
            *,
            retain_cache: bool,
        ) -> None:
            assert not retain_cache
            owner.ledger.bump(f"{owner.counter_prefix}_finite_block_lookups", 2)
            owner.ledger.bump(f"{owner.counter_prefix}_finite_block_misses", 2)
            owner.ledger.bump(f"{owner.counter_prefix}_transient_leaf_steps", 3)
            raise RuntimeError("injected weighted carry construction failure")

        monkeypatch.setattr(
            "number_compiler.sequences.antihydra.mahler_carry_quotient."
            "balanced_residue_effect",
            fail_after_shared_work,
        )
        with scratch.scope(), pytest.raises(RuntimeError, match="injected weighted"):
            issued_weighted_carry(
                workspace,
                source,
                workspace.root_action,
                reserve_bits=scratch.require_bits,
            )
        counters = ledger.counters
        assert (
            counters["antihydra_arithmetic_weighted_carry_block_requests"]
            - requests_before
            == 2
        )
        assert (
            counters["antihydra_arithmetic_weighted_carry_block_misses"] - misses_before
            == 2
        )
        assert (
            counters["antihydra_arithmetic_weighted_carry_leaf_steps"] - steps_before
            == 3
        )
    finally:
        workspace.dispose()


def test_x15_morphism_keeps_raw_floor_and_physical_iteration_distinct() -> None:
    with _issued(6) as (_workspace, carry, scratch):
        morphism = carry.x15_morphism(reserve_bits=scratch.require_bits)
        cut = morphism.coupled_integer_cut()
        endpoint, _delta, _minimum, _odd = _literal(6)
        raw_quotient, raw_remainder = divmod(3**6 * 8, 2**6)
        assert (cut.raw_quotient, cut.raw_remainder) == (
            raw_quotient,
            raw_remainder,
        )
        assert cut.physical_endpoint == endpoint + 1
        assert cut.raw_quotient > cut.physical_endpoint
        assert cut.floor_correction == (
            raw_remainder + cut.denominator * (raw_quotient - cut.physical_endpoint)
        )
        scaled = morphism.scaled_integer_pair(reserve_bits=scratch.require_bits)
        assert scaled.raw_numerator - scaled.floor_numerator == (
            scaled.physical_numerator
        )


def test_two_parent_x15_recurrence_checks_both_polynomial_forms() -> None:
    result = two_parent_x15_floor(7, 108, 3, 4)
    assert result.future == 1624
    assert result.remainder_correction == 3
    with pytest.raises(ArithmeticError, match="different sources"):
        two_parent_x15_floor(7, 109, 3, 4)


def test_composed_x15_validation_does_not_recompose_coefficients(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    workspace = AntihydraArithmeticImageWorkspace(ledger, 1, shared_cache=False)
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "nc19-x15-join-test")
    try:
        first_origin = workspace.scheduler.source_image_origin(
            workspace, workspace.root_source
        )
        first_source = workspace.scheduler.source_image_view(workspace, first_origin)
        second_id = append_source(
            workspace,
            DyadicReturnSourceRecord(0, 1, 6, None, None, None, 0, True),
        )
        second_origin = workspace.scheduler.source_image_origin(workspace, second_id)
        second_source = workspace.scheduler.source_image_view(workspace, second_origin)
        with scratch.scope():
            first = issued_weighted_carry(
                workspace,
                first_source,
                workspace.root_action,
                reserve_bits=scratch.require_bits,
            ).x15_morphism(reserve_bits=scratch.require_bits)
            second = issued_weighted_carry(
                workspace,
                second_source,
                workspace.root_action,
                reserve_bits=scratch.require_bits,
            ).x15_morphism(reserve_bits=scratch.require_bits)
            joined = first.then(second, reserve_bits=scratch.require_bits)

            def forbidden(*_args: object, **_kwargs: object) -> None:
                raise AssertionError("completed x15 validation recomposed coefficients")

            monkeypatch.setattr(SkewTransfer, "then", forbidden)
            joined.require_issued()
            assert joined.endpoint == second.endpoint
    finally:
        workspace.dispose()


def test_recomputed_self_snapshot_cannot_forge_x15_issuance() -> None:
    with _issued(1) as (_workspace, carry, scratch):
        genuine = carry.x15_morphism(reserve_bits=scratch.require_bits)
        forged = object.__new__(X15CarryMorphism)
        for name in (
            "source",
            "ticks",
            "gain",
            "denominator",
            "endpoint",
            "floor_correction",
            "_carry",
            "_parents",
            "_owner",
            "_issuer",
            "_certificate",
        ):
            object.__setattr__(forged, name, getattr(genuine, name))
        object.__setattr__(forged, "innovation", genuine.innovation + 2)
        object.__setattr__(
            forged,
            "centered_skew",
            SkewTransfer(genuine.gain, genuine.innovation + 2, genuine.denominator),
        )
        object.__setattr__(forged, "_snapshot", forged.publication_payload())
        with pytest.raises(ValueError, match="not issued"):
            forged.require_issued()


def test_diagonal_field_uses_same_raw_and_physical_source_seam() -> None:
    with _issued(3) as (_workspace, carry, scratch):
        morphism = carry.x15_morphism(reserve_bits=scratch.require_bits)
        field = morphism.diagonal_tower().packed_field(
            12,
            max_columns=32,
            max_observer_terms=32,
            reserve_bits=scratch.require_bits,
            moduli=(99, 101),
        )
        assert field.source_h == 8
        assert field.endpoint_h == 27
        assert field.spatial_columns == 12
        assert field.vectors.columns == 12
        assert field.vectors.lane_value(3, "physical_floor_digit_correction") == 5
        assert (
            sum(
                field.vectors.lane_value(index, "physical_floor_digit_correction")
                for index in range(12)
            )
            == 5
        )
        assert tuple(item.modulus for item in field.projection_moduli) == (99, 101)
        assert field.temporal_intermediate_rows == 0


@pytest.mark.parametrize("ticks", (0, 1, 4, 32))
def test_diagonal_columns_match_independent_exact_power_fields(ticks: int) -> None:
    columns = ticks + 4
    with _issued(ticks) as (_workspace, carry, scratch):
        field = (
            carry.x15_morphism(reserve_bits=scratch.require_bits)
            .diagonal_tower()
            .packed_field(
                columns,
                max_columns=64,
                max_observer_terms=64,
                reserve_bits=scratch.require_bits,
                moduli=(99, 101),
            )
        )
        endpoint_h = _literal(ticks)[0] + 1
        raw_digits = _digits(15**ticks * 8, columns + 1)
        physical_digits = _digits(10**ticks * endpoint_h, columns + 1)
        next_physical_digits = _digits(
            10 ** (ticks + 1) * ((3 * endpoint_h) // 2), columns + 1
        )
        raw_carries = {
            multiplier: _carry_tape(raw_digits, multiplier)
            for multiplier in (14, 15, 210, 225)
        }
        physical_carries = {
            multiplier: _carry_tape(physical_digits, multiplier)
            for multiplier in (15, 210, 225)
        }
        vectors = field.vectors
        for index in range(columns):
            raw_digit = raw_digits[index]
            physical_digit = physical_digits[index]
            previous_cr15 = 0 if index == 0 else raw_carries[15][index - 1]
            previous_cp15 = 0 if index == 0 else physical_carries[15][index - 1]
            _raw_quotient, raw_next = divmod(15 * raw_digit + previous_cr15, 10)
            _physical_quotient, physical_unrounded = divmod(
                15 * physical_digit + previous_cp15, 10
            )
            local_floor = 5 * (endpoint_h & 1) if index == ticks else 0
            cr15 = raw_carries[15][index]
            cr14 = raw_carries[14][index]
            cr210 = raw_carries[210][index]
            cr225 = raw_carries[225][index]
            cp15 = physical_carries[15][index]
            cp210 = physical_carries[210][index]
            cp225 = physical_carries[225][index]
            raw_borrow = cr225 - cr210 - cr15
            physical_borrow = cp225 - cp210 - cp15
            raw_borrow_15 = cr15 - cr14
            expected = {
                "raw_digit": raw_digit,
                "physical_digit": physical_digit,
                "raw_next_digit": raw_next,
                "physical_next_digit": physical_unrounded - local_floor,
                "physical_floor_digit_correction": local_floor,
                "raw_carry_15": cr15,
                "physical_carry_15": cp15,
                "raw_borrow_225_15": raw_borrow,
                "physical_borrow_225_15": physical_borrow,
                "raw_borrow_15_1": raw_borrow_15,
                "raw_digit_decrease": int(
                    raw_digits[index + 1] > (15 * raw_digits[index + 1] + cr15) % 10
                ),
            }
            assert expected["physical_next_digit"] == next_physical_digits[index]
            assert {
                name: vectors.lane_value(index, name) for name in expected
            } == expected


def test_nonroot_h7_four_tick_cut_keeps_raw35_physical33_and_k39() -> None:
    ledger = ResourceLedger()
    workspace = AntihydraArithmeticImageWorkspace(ledger, 4, shared_cache=False)
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "nc19-h7-cut-test")
    try:
        source_id = append_source(
            workspace,
            DyadicReturnSourceRecord(7, 4, 0, None, None, None, 0, True),
        )
        origin = workspace.scheduler.source_image_origin(workspace, source_id)
        source = workspace.scheduler.source_image_view(workspace, origin)
        with scratch.scope():
            carry = issued_weighted_carry(
                workspace,
                source,
                workspace.root_action,
                reserve_bits=scratch.require_bits,
            )
            morphism = carry.x15_morphism(reserve_bits=scratch.require_bits)
            cut = morphism.coupled_integer_cut()
            assert (cut.raw_quotient, cut.physical_endpoint) == (35, 33)
            assert cut.floor_correction == 39
            assert morphism.floor_correction == 39
    finally:
        workspace.dispose()


def test_complete_diagonal_width_refuses_before_field_vectors() -> None:
    with _issued(64) as (_workspace, carry, scratch):
        tower = carry.x15_morphism(reserve_bits=scratch.require_bits).diagonal_tower()
        with pytest.raises(BlockContextBudgetExceeded, match="observer budget"):
            tower.packed_field(
                0,
                max_columns=8,
                max_observer_terms=8,
                reserve_bits=scratch.require_bits,
            )


def test_mutated_carry_cannot_issue_x15_or_diagonal_authority() -> None:
    with _issued(8) as (_workspace, carry, scratch):
        object.__setattr__(carry, "innovation", carry.innovation + 1)
        with pytest.raises(ValueError, match="not issued|root image|altered"):
            carry.require_issued()
        with pytest.raises(ValueError, match="not issued|root image|altered"):
            carry.x15_morphism(reserve_bits=scratch.require_bits)


def test_recomputed_self_snapshot_cannot_forge_cold_carry_issuance() -> None:
    ledger = ResourceLedger()
    workspace = AntihydraArithmeticImageWorkspace(ledger, 1, shared_cache=False)
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "nc19-forged-carry-test")
    try:
        origin = workspace.scheduler.source_image_origin(
            workspace, workspace.root_source
        )
        source = workspace.scheduler.source_image_view(workspace, origin)
        with scratch.scope():
            genuine = issued_weighted_carry(
                workspace,
                source,
                workspace.root_action,
                reserve_bits=scratch.require_bits,
            )
            forged = object.__new__(IssuedWeightedCarry)
            for name in (
                "width",
                "residue",
                "delta",
                "minimum",
                "odd_h_steps",
                "gain",
                "denominator",
                "cap_hat",
                "forced_mod4",
                "first_centered_bit",
                "last_centered_bit",
                "_workspace",
                "_source_image",
                "_source",
                "_action",
                "_binding",
                "_centered_source",
                "_projection_payload",
            ):
                object.__setattr__(forged, name, getattr(genuine, name))
            object.__setattr__(forged, "innovation", 3)
            object.__setattr__(forged, "skew", SkewTransfer(3, 3, 2))
            object.__setattr__(forged, "_issuer", object())
            object.__setattr__(forged, "_snapshot", forged.publication_payload())
            with pytest.raises(ValueError, match="not issued"):
                forged.require_issued()
    finally:
        workspace.dispose()
