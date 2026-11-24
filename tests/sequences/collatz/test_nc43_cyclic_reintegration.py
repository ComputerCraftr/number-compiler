"""NC43 regression gates: no consumed-cut allocation, and physical authority."""

from __future__ import annotations

from builtins import pow as integer_pow

import pytest

from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz import cyclic_diagonal
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.cyclic_abc_grammar import CyclicGuardedRow
from number_compiler.sequences.collatz.cyclic_diagonal import CyclicDefectGuard
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)


def test_moving_upper_response_powers_only_the_rebased_physical_ring(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Signed non-unit decimal delta: 3 - 8 = -5. Independent source cylinder.
    row = CyclicGuardedRow("001")
    modulus = 1 << 4200
    source = (-4 * integer_pow(-5, -1, modulus)) % modulus + modulus
    admission = row.admitted_prefix(source, 7000, maximum_steps=4000)
    assert admission is not None and admission.action.steps == 4000
    expected = source
    for _ in range(4000):
        expected = (3 * expected + 1) // 2 if expected & 1 else expected // 2

    for radix in (2, 10):
        moduli: list[int] = []

        def bounded_power(
            base: int,
            exponent: int,
            mod: int,
            *,
            selected_radix: int = radix,
            seen: list[int] = moduli,
        ) -> int:
            seen.append(mod)
            assert mod <= abs(admission.guard.action.delta) * selected_radix**10
            return integer_pow(base, exponent, mod)

        monkeypatch.setattr(cyclic_diagonal, "pow", bounded_power, raising=False)
        port = admission.projected_upper_action(
            4000, radix, 4002, 8, reserve_bits=lambda _: None
        )
        assert moduli
        assert port.apply(source // radix**4002) == expected // radix**2 % radix**8


def test_infinite_guard_moving_port_without_materializing_the_consumed_cut(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    guard = CyclicDefectGuard(CyclicGuardedRow("10").laurent_action, 1)
    assert guard.first_mismatch is None
    horizon = 10**60
    for radix in (2, 10):

        def bounded_power(
            base: int, exponent: int, mod: int, *, selected_radix: int = radix
        ) -> int:
            assert mod <= selected_radix**10
            return integer_pow(base, exponent, mod)

        monkeypatch.setattr(cyclic_diagonal, "pow", bounded_power, raising=False)
        response = guard.upper_response(horizon, radix, horizon + 2, 8)
        expected_gain = integer_pow(3, horizon // 2, radix**8)
        if radix == 10:
            expected_gain *= integer_pow(5, horizon, radix**8)
        assert response.gain == expected_gain % radix**8
        assert response.carry == 0


def test_all_witness_bearing_projections_retain_the_selected_physical_macro() -> None:
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        352164,
        30,
        ledger=ledger,
        include_innovation_tape=True,
        innovation_modulus=49,
        require_boundary_witness=True,
        include_f5=True,
        include_joint_cocycle=True,
        include_width_spine=True,
    )
    result.validate_boundary_producer_stamp()
    assert result.first_boundary_stamp is not None
    assert result.first_boundary_stamp.occurrence[:3] == (0, 352164, 7)
    assert result.first_boundary_macro is not None
    assert result.first_boundary_macro.endpoint == 99047
    assert result.endpoint == 713954
    assert result.run_actions == 2
    assert ledger.counters["collatz_cyclic_grammar_admitted_actions"] == 1
    assert ledger.counters["collatz_cyclic_grammar_classifications_elided"] == 13
    assert result.joint_action is not None
    assert result.innovation_observation is not None
    assert result.normalized_f5 is not None
    assert (
        result.normalized_f5.apply(352164)
        == result.joint_action.normalized_endpoint % 5
    )
    assert ledger.nodes == ledger.entries == 0


def test_live_moving_band_reserves_before_guard_and_reuses_sealed_endpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = PoweredCollatzTerm(1486, 24, shared_cache=False)
    term.prepare_joint_cocycle()
    workspace = term.source_image()
    try:
        seam = term.diagonal_carry_seam()
        scratch = RunArithmeticWorkspace.for_ledger(term.resource_ledger, "nc43-band")

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("allocated a second guard")

        def refuse(_bits: int) -> None:
            raise MemoryError("reservation refused")

        monkeypatch.setattr(CyclicDefectGuard, "__post_init__", forbidden)
        with pytest.raises(MemoryError, match="reservation refused"):
            seam.cyclic_moving_band(
                10, 8, 4, normalized_offset=7, reserve_bits=refuse, max_width=128
            )
        with scratch.scope():
            assert (
                seam.cyclic_moving_band(
                    10, 15, 4, reserve_bits=scratch.require_bits, max_width=128
                )
                == 536
            )
    finally:
        workspace.dispose()


def test_live_seam_rejects_a_replaced_cyclic_phase() -> None:
    term = PoweredCollatzTerm(1486, 24, shared_cache=False)
    term.prepare_joint_cocycle()
    workspace = term.source_image()
    try:
        seam = term.diagonal_carry_seam()
        joint = workspace.joint_action
        assert joint is not None
        fields = joint.fields
        original = fields.cyclic_phase
        assert original is not None
        forged = (original[0], (original[1] + 1) % len(original[0]))
        assert forged != original
        object.__setattr__(fields, "_cyclic_phase", forged)
        object.__setattr__(fields, "_issued_cyclic_phase", forged)
        with pytest.raises(ValueError, match="altered source authority"):
            seam.require_issued()
    finally:
        workspace.dispose()
