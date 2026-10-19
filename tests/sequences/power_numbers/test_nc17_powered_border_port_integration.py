"""Regression tests for authoritative, source-guarded powered matrix CLI joins.

The modular trace and tripling actions are source-only: none of these tests
asserts that a prime or composite certificate was recovered from a low window.
"""

from dataclasses import replace
from typing import cast

import pytest

from number_compiler.sequences.power_numbers.fermat_boundary_macros import FermatClockId
from number_compiler.sequences.power_numbers.mersenne_trace_port_matrix import (
    trace_squaring_power,
)
from number_compiler.sequences.power_numbers.numbers import (
    FermatNumberSpec,
    MersenneNumberSpec,
)


@pytest.mark.parametrize("index", (0, 1, 2, 3, 5, 6, 16))
@pytest.mark.parametrize("base,position", ((2, 8), (5, 2), (7, 1), (10, 3)))
@pytest.mark.validation
def test_fermat_clocked_ports_match_independent_modular_exponent(
    index: int, base: int, position: int
) -> None:
    _assert_fermat_clocked_ports(index, base, position)


def test_fermat_clocked_ports_cover_unit_radix_and_clock_boundaries() -> None:
    cases: tuple[tuple[int, int, int], ...] = (
        (0, 2, 8),
        (2, 5, 2),
        (3, 7, 1),
        (16, 10, 3),
    )
    for index, base, position in cases:
        _assert_fermat_clocked_ports(index, base, position)


def _assert_fermat_clocked_ports(index: int, base: int, position: int) -> None:
    level = (1 << index) - 1
    matrix = FermatNumberSpec(index).demand_fermat_powered_port_matrix(
        level, 47, base=base, position=position
    )
    modulus = base ** (position + 1)
    start: int = pow(3, 1 << level, modulus)
    assert matrix.producer_verified
    assert matrix.source_residue == start
    assert matrix.endpoint_residue == start * pow(3, 47, modulus) % modulus
    low: int = start % (base**position)
    assert matrix.conditional_endpoints == tuple(
        (low + digit * base**position) * pow(3, 47, modulus) % modulus
        for digit in range(base)
    )
    assert matrix.punctures[0].tick == 0
    assert matrix.punctures[-1].tick == 47
    for port in matrix.punctures:
        actual: int = start * pow(3, port.tick, modulus) % modulus
        assert port.source_residue == actual
        assert port.carry_in == (3 * (actual % (base**position))) // (base**position)
        assert port.carry_out == (3 * actual) // modulus
        for clock in matrix.macro.clocks:
            assert dict(port.clock_residues)[clock.identity] == (
                pow(3, (1 << level) + port.tick, clock.modulus)
                if level <= 6
                else pow(
                    3, pow(2, level, clock.exponent_period) + port.tick, clock.modulus
                )
                if clock.modulus not in (99, 198, 9900)
                else pow(3, (1 << level) + port.tick, clock.modulus)
            )


def test_fermat_squaring_and_false_join_rejection() -> None:
    spec = FermatNumberSpec(5)
    level = 31
    one = spec.demand_fermat_powered_port_matrix(level, 1, base=10, position=8)
    doubled = one.power_of_two(12)
    direct = spec.demand_fermat_powered_port_matrix(level, 4096, base=10, position=8)
    assert (doubled.source_residue, doubled.endpoint_residue) == (
        direct.source_residue,
        direct.endpoint_residue,
    )
    assert doubled.conditional_endpoints == direct.conditional_endpoints
    assert doubled.physical_steps == 4096
    assert direct.packet()["causal_rows_constructed"] is False
    assert len(direct.punctures) <= 16
    with pytest.raises(ValueError, match="not chronologically adjacent"):
        one.then(one.rebase(3))
    other = spec.demand_fermat_powered_port_matrix(level, 1, base=10, position=8)
    with pytest.raises(ValueError, match="incompatible owner or domain"):
        one.then(other.rebase(1))
    copied = replace(one, endpoint_residue=one.endpoint_residue)
    assert not copied.producer_verified
    with pytest.raises(ValueError, match="unissued"):
        copied.packet()


def test_fermat_join_consumes_issued_children_without_recompiling(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.power_numbers import fermat_powered_port_matrix

    spec = FermatNumberSpec(5)
    first = spec.demand_fermat_powered_port_matrix(31, 5, base=10, position=8)
    later = first.rebase(first.physical_offset + first.physical_steps)
    expected = spec.demand_fermat_powered_port_matrix(31, 10, base=10, position=8)

    def unexpected_root_power(_level: int, _modulus: int, _period: int) -> int:
        raise AssertionError("child-summary join recomputed the Fermat source root")

    monkeypatch.setattr(
        fermat_powered_port_matrix,
        "exact_three_power_residue",
        unexpected_root_power,
    )
    joined = first.then(later)
    assert joined.producer_verified
    assert joined.source_residue == expected.source_residue
    assert joined.endpoint_residue == expected.endpoint_residue
    assert joined.conditional_endpoints == expected.conditional_endpoints
    assert joined.physical_offset == 0 and joined.physical_steps == 10
    ticks = tuple(point.tick for point in joined.punctures)
    assert ticks == tuple(sorted(set(ticks)))
    assert ticks[0] == 0 and ticks[-1] == 10


def test_fermat_registry_issued_before_matrix_has_actual_carry_clocks() -> None:
    matrix = FermatNumberSpec(5).demand_fermat_powered_port_matrix(
        31, 4, base=10, position=4
    )
    names = cast(tuple[str, ...], matrix.packet()["macro_registry"])
    assert {
        "B2-LTE",
        "D10-C4",
        "D10-C20",
        "D10-C100",
        "Q5-125",
        "Q7-49",
        "D10-99",
        "D10-198",
        "D10-9900",
        "PIVOT-XOR",
    } <= set(names)
    assert matrix.packet()["source_guard_admitted"]
    assert matrix.packet()["primality_authority"] is False
    assert tuple(
        dict(matrix.macro.puncture(i))[FermatClockId.DECIMAL_2_DIGITS] for i in range(4)
    ) == (
        61,
        83,
        49,
        47,
    )
    copied = replace(matrix.macro, root_residue9900=matrix.macro.root_residue9900)
    assert not copied.producer_verified
    with pytest.raises(ValueError, match="unissued"):
        copied.puncture(0)


def test_fermat_macro_and_dependent_matrix_bind_full_source_authority() -> None:
    from number_compiler.sequences.power_numbers.fermat_boundary_macros import (
        issue_algebraic_root,
    )
    from number_compiler.sequences.power_numbers.three_power_signed_border_action import (
        SourceWeightedTriplingAction,
    )

    matrix = FermatNumberSpec(2).demand_fermat_powered_port_matrix(
        3, 4, base=10, position=3
    )
    macro = matrix.macro
    assert type(macro.source) is SourceWeightedTriplingAction
    assert macro.producer_verified and matrix.producer_verified

    # This issued algebraic root has the same public Fermat index and level as
    # the signed radial source, but it has no authenticated high radial ports.
    # Rebinding cannot preserve either the macro seal or a dependent matrix.
    object.__setattr__(macro, "source", issue_algebraic_root(2, 3))
    assert not macro.producer_verified
    assert not matrix.producer_verified


def test_large_fermat_root_keeps_low_clock_without_fabricated_high_radial_guard() -> (
    None
):
    matrix = FermatNumberSpec(16).demand_fermat_powered_port_matrix(
        65535, 4096, base=10, position=8
    )
    packet = matrix.packet()
    assert packet["source_cylinder_verified"] is False
    assert packet["root_radial_guard_verified"] is False
    assert packet["primality_authority"] is False
    names = cast(tuple[str, ...], packet["macro_registry"])
    assert "R3-UNRESOLVED" in names
    assert "PIVOT-XOR" not in names
    assert packet["selected_endpoint_residue"] == (
        pow(3, pow(2, 65535, 4 * 10**8) + 4096, 10**9)
    )


@pytest.mark.parametrize("base,position", ((2, 7), (5, 3), (7, 2), (10, 2)))
@pytest.mark.parametrize("steps", (1, 2, 3, 7, 37, 256, 4096))
def test_mersenne_trace_exact_vs_direct_and_modular_clocks(
    base: int,
    position: int,
    steps: int,
) -> None:
    spec = MersenneNumberSpec(31)
    matrix = spec.demand_mersenne_trace_matrix(steps, base=base, position=position)
    modulus = base ** (position + 1)
    source: int = (2 * (pow(2, spec.exponent, modulus) - 1)) % modulus
    low: int = source % (base**position)
    for initial in range(base):
        value: int = low + initial * base**position
        for _ in range(min(steps, 37)):
            value = (value * value - 2) % modulus
        if steps <= 37:
            assert matrix.conditional_endpoints[initial] == value
    assert matrix.source_residue == source
    assert matrix.producer_verified
    assert matrix.endpoint_residue == trace_squaring_power(
        source, steps, base, position + 1
    )
    for port in matrix.punctures:
        direct: int = source
        for _ in range(min(port.tick, 64)):
            direct = (direct * direct - 2) % modulus
        if port.tick <= 64:
            assert port.residue == direct
        assert port.lower_borrow in (0, 1)
        assert all(
            dict(port.clock_residues)[c.identity] == c.at(port.tick)
            for c in matrix.macro.clocks
        )


def test_mersenne_conditional_squaring_and_guarded_joins() -> None:
    spec = MersenneNumberSpec(31)
    one = spec.demand_mersenne_trace_matrix(1, base=10, position=8)
    current = one
    for _ in range(12):
        current = current.square()
    direct = spec.demand_mersenne_trace_matrix(4096, base=10, position=8)
    assert current.endpoint_residue == direct.endpoint_residue
    assert current.conditional_endpoints == direct.conditional_endpoints
    assert current.packet()["primality_authority"] is False
    assert len(current.punctures) <= 16
    assert current.packet()["source_trace"] == 2 * ((pow(2, 31, 10**9) - 1) % 10**9)
    assert "trace" not in one.packet()
    assert "port_punctures" not in one.packet()
    traced = spec.demand_mersenne_trace_matrix(8, base=10, position=2).packet(
        trace=True
    )
    trace = cast(dict[str, object], traced["trace"])
    residues = cast(tuple[int, ...], trace["residues"])
    assert len(residues) == 9
    assert "port_punctures" in trace
    with pytest.raises(ValueError, match="64"):
        current.packet(trace=True)
    with pytest.raises(ValueError, match="not chronologically adjacent"):
        one.then(one.rebase(3))
    with pytest.raises(ValueError, match="incompatible owner or domain"):
        one.then(spec.demand_mersenne_trace_matrix(1, base=10, position=8).rebase(1))
    copied = replace(one, source_residue=one.source_residue)
    assert not copied.producer_verified
    with pytest.raises(ValueError, match="unissued"):
        copied.packet()


def test_mersenne_join_consumes_issued_children_without_recompiling(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.power_numbers import mersenne_trace_port_matrix

    spec = MersenneNumberSpec(31)
    first = spec.demand_mersenne_trace_matrix(3, base=10, position=8)
    later = first.rebase(first.offset + first.steps)
    expected = spec.demand_mersenne_trace_matrix(6, base=10, position=8)

    def unexpected_trace_power(
        _start: int, _steps: int, _base: int, _places: int
    ) -> int:
        raise AssertionError("child-summary join recomputed a trace power")

    monkeypatch.setattr(
        mersenne_trace_port_matrix,
        "trace_squaring_power",
        unexpected_trace_power,
    )
    joined = first.then(later)
    assert joined.producer_verified
    assert joined.source_residue == expected.source_residue
    assert joined.endpoint_residue == expected.endpoint_residue
    assert joined.conditional_endpoints == expected.conditional_endpoints
    assert joined.offset == 0 and joined.steps == 6
    assert tuple(point.tick for point in joined.punctures) == (0, 1, 2, 4, 6)


@pytest.mark.parametrize("exponent", (0, 1))
def test_mersenne_trace_accepts_small_mathematical_source_roots(exponent: int) -> None:
    from number_compiler.sequences.power_numbers.mersenne_trace_port_matrix import (
        demand_mersenne_trace_matrix,
    )

    matrix = demand_mersenne_trace_matrix(exponent, 3, base=10, position=2)
    modulus = 10**3
    source = 2 * (pow(2, exponent, modulus) - 1) % modulus
    expected = source
    for _ in range(3):
        expected = (expected * expected - 2) % modulus
    assert matrix.source_residue == source
    assert matrix.endpoint_residue == expected


def test_mersenne_clock_ids_own_source_moduli_and_packet_labels(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.power_numbers.mersenne_trace_port_matrix import (
        CertifiedTraceClock,
        MersenneClockId,
        issue_mersenne_trace_macro,
    )

    macro = issue_mersenne_trace_macro(31)
    assert macro.producer_verified
    residues = dict(macro.source_trace_residues)
    original = CertifiedTraceClock.at
    calls: list[MersenneClockId] = []

    def counted(clock: CertifiedTraceClock, tick: int) -> int:
        calls.append(clock.identity)
        return original(clock, tick)

    monkeypatch.setattr(CertifiedTraceClock, "at", counted)
    puncture = dict(macro.puncture(0))
    assert calls == [clock.identity for clock in macro.clocks]
    assert set(residues) == {clock.identity for clock in macro.clocks}
    for identity, source in macro.source_trace_residues:
        assert type(identity) is MersenneClockId
        assert source == 2 * (
            pow(2, macro.candidate_exponent, identity.modulus) - 1
        ) % (identity.modulus)
        clock = next(clock for clock in macro.clocks if clock.identity is identity)
        assert clock.modulus == identity.modulus
        assert clock.name == identity.display_label
        assert clock.at(0) == source == puncture[identity]

    identity = macro.source_trace_residues[0][0]
    for field_name, forged_value in (("modulus", 1), ("display_label", "forged")):
        with pytest.raises(AttributeError):
            setattr(identity, field_name, forged_value)


def test_mersenne_trace_rejects_unverified_exponent_period(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.power_numbers import mersenne_trace_port_matrix

    def false_period(_base: int, _places: int) -> int:
        return 1

    monkeypatch.setattr(mersenne_trace_port_matrix, "sl2_order_upper", false_period)
    with pytest.raises(ArithmeticError, match="matrix identity"):
        trace_squaring_power(0, 0, 10, 2)


def test_mersenne_source_residue_rejects_unverified_exponent_period(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.power_numbers import source_matrix
    from number_compiler.sequences.power_numbers.source_matrix import (
        checked_dyadic_matrix_power,
        demand_unwrapped_inner_digit_stencil,
    )

    def false_period(
        matrix: tuple[int, int, int, int],
        steps: int,
        modulus: int,
        _proposed_period: int,
    ) -> tuple[tuple[int, int, int, int], int, int]:
        return checked_dyadic_matrix_power(matrix, steps, modulus, 1)

    monkeypatch.setattr(source_matrix, "checked_dyadic_matrix_power", false_period)

    with pytest.raises(ArithmeticError, match="matrix identity"):
        demand_unwrapped_inner_digit_stencil("mersenne", 1023, 7, 10, (0,))


@pytest.mark.parametrize("level,modulus", ((0, 2), (1, 7), (4, 100)))
def test_mersenne_source_period_check_is_included_in_work_counts(
    level: int,
    modulus: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields.morphism_core import (
        binary_power_composition_count,
    )
    from number_compiler.sequences.power_numbers import source_matrix
    from number_compiler.sequences.power_numbers.mersenne_trace_port_matrix import (
        sl2_order_upper,
    )
    from number_compiler.sequences.power_numbers.source_matrix import (
        checked_dyadic_matrix_power,
        demand_unwrapped_inner_digit_stencil,
    )

    parameter = 1023
    places = {2: 1, 7: 1, 100: 2}[modulus]
    base = {2: 2, 7: 7, 100: 10}[modulus]
    positions = tuple(range(places))
    matrix_compositions = 0

    def count_checked_power(
        matrix: tuple[int, int, int, int],
        steps: int,
        selected_modulus: int,
        proposed_period: int,
    ) -> tuple[tuple[int, int, int, int], int, int]:
        nonlocal matrix_compositions
        result = checked_dyadic_matrix_power(
            matrix, steps, selected_modulus, proposed_period
        )
        matrix_compositions += result[2]
        return result

    monkeypatch.setattr(
        source_matrix, "checked_dyadic_matrix_power", count_checked_power
    )

    observed = demand_unwrapped_inner_digit_stencil(
        "mersenne", parameter, level, base, positions
    )
    work = observed.work
    period = sl2_order_upper(base, places)
    reduced_exponent = pow(2, level, period)
    expected_matrix_count = binary_power_composition_count(
        period
    ) + binary_power_composition_count(reduced_exponent)
    assert work.scalar_power_compositions == binary_power_composition_count(level)
    assert (
        work.matrix_power_compositions == expected_matrix_count == matrix_compositions
    )

    expected_trace = 4 % observed.work.modulus
    for _ in range(level + 1):
        expected_trace = (expected_trace * expected_trace - 2) % observed.work.modulus
    reconstructed = sum(
        digit * base**position
        for position, digit in zip(positions, observed.digits, strict=True)
    )
    assert reconstructed == expected_trace


def test_checked_dyadic_matrix_power_accepts_identity_period_one() -> None:
    from number_compiler.sequences.power_numbers.source_matrix import (
        checked_dyadic_matrix_power,
    )

    result, scalar_count, matrix_count = checked_dyadic_matrix_power(
        (1, 0, 0, 1), 4096, 7, 1
    )
    assert result == (1, 0, 0, 1)
    assert scalar_count == 0
    assert matrix_count == 1


def test_legacy_finite_row_snapshot_budget_rejects_before_source_construction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    def unexpected_source(*args: object, **kwargs: object) -> object:
        raise AssertionError("oversized finite rows must not compile a radial source")

    monkeypatch.setattr(
        FermatNumberSpec, "demand_three_power_signed_border_action", unexpected_source
    )
    with pytest.raises(BlockContextBudgetExceeded, match="powered port matrix"):
        FermatNumberSpec(5).demand_three_power_causal_border_matrix(
            31, 4096, base=10, position=8
        )


def test_fermat_and_mersenne_compact_cli_at_advertised_horizon(
    capsys: pytest.CaptureFixture[str],
) -> None:
    import json

    from number_compiler.api.cli import main

    for family, index in (("fermat", 5), ("mersenne", 31)):
        assert (
            main(
                [
                    family,
                    "--nth",
                    str(index),
                    "--no-value",
                    "--info",
                    "temporal.matrix",
                    "--temporal-matrix-steps",
                    "4096",
                    "--temporal-matrix-digit-position",
                    "8",
                    "--format",
                    "json",
                ]
            )
            == 0
        )
        packet = json.loads(capsys.readouterr().out)["info"]["temporal.matrix"]
        assert packet["status"] == "available"
        assert packet["horizon"]["ticks"] == 4096
        assert packet["horizon"]["unit"] == (
            "ordinary-tripling-ticks" if family == "fermat" else "trace-squaring-steps"
        )
        assert packet["primality_authority"] is False
        assert "port_punctures" not in packet
        assert "trace" not in packet
        assert len(packet["macro_registry"]) >= 8
        assert packet["execution_authority"] is False

        assert (
            main(
                [
                    family,
                    "--nth",
                    str(index),
                    "--no-value",
                    "--info",
                    "temporal.matrix.trace",
                    "--temporal-matrix-steps",
                    "64",
                    "--temporal-matrix-digit-position",
                    "8",
                    "--format",
                    "json",
                ]
            )
            == 0
        )
        traced_packet = json.loads(capsys.readouterr().out)["info"][
            "temporal.matrix.trace"
        ]
        assert len(traced_packet["trace"]["port_punctures"]) <= 8
        assert traced_packet["primality_authority"] is False


@pytest.mark.parametrize("index", (0, 1, 2, 3))
def test_physical_radial_interval_transports_real_leading_digits(index: int) -> None:
    level = (1 << index) - 1
    matrix = FermatNumberSpec(index).demand_fermat_powered_port_matrix(
        level, 64, base=10, position=2
    )
    macro = matrix.macro
    for tick in range(65):
        port = macro.radial_at(tick)
        exact = str(pow(3, (1 << level) + tick))
        assert port.exact_width == len(exact)
        assert port.guaranteed_word is None or exact.startswith(port.guaranteed_word)
        assert port.guaranteed_places == len(port.guaranteed_word or "")
    assert macro.radial_at(0).guaranteed_word is not None


def test_later_high_radial_families_are_guards_not_invented_physical_periods() -> None:
    matrix = FermatNumberSpec(5).demand_fermat_powered_port_matrix(
        31, 4096, base=10, position=8
    )
    ports = {p.tick: p.radial for p in matrix.punctures}
    assert ports[8].guaranteed_word == "27"
    assert ports[8].named_family == "27"
    assert ports[64].guaranteed_word == "144"
    assert ports[64].named_family == "14"
    assert ports[1024].guaranteed_word == "15"
    assert ports[1024].named_family == "15"
    assert all(p.exact_width is not None for p in ports.values())
    assert {p.tick: p.radial for p in matrix.punctures} == {
        p.tick: matrix.macro.radial_at(p.tick) for p in matrix.punctures
    }


def test_mersenne_modular_trace_rejects_oversized_places_before_allocation() -> None:
    with pytest.raises(ValueError, match="place budget"):
        trace_squaring_power(4, 4096, 10, 1_000_000_000)


def test_mersenne_compile_reuses_checked_endpoint_and_puncture_powers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.power_numbers import mersenne_trace_port_matrix
    from number_compiler.sequences.power_numbers.temporal_matrix_support import (
        dyadic_puncture_offsets,
    )

    exponent, base, position, offset, steps = 31, 10, 2, 3, 8
    places = position + 1
    modulus = base**places
    seed_matrix = MersenneNumberSpec(exponent).demand_mersenne_trace_matrix(
        steps, base=base, position=position
    )
    macro = seed_matrix.macro
    initial = macro.source_trace(base, places)

    def direct(start: int, count: int) -> int:
        value = start
        for _ in range(count):
            value = (value * value - 2) % modulus
        return value

    expected_root = direct(initial, offset)
    expected_endpoint = direct(expected_root, steps)
    expected_punctures = tuple(
        direct(initial, offset + tick) for tick in dyadic_puncture_offsets(steps)
    )

    original_power = mersenne_trace_port_matrix.trace_squaring_power
    calls: list[tuple[int, int, int, int]] = []

    def counted_power(
        start: int, count: int, selected_base: int, selected_places: int
    ) -> int:
        calls.append((start, count, selected_base, selected_places))
        return original_power(start, count, selected_base, selected_places)

    monkeypatch.setattr(
        mersenne_trace_port_matrix, "trace_squaring_power", counted_power
    )
    matrix = seed_matrix.rebase(offset)

    assert matrix.source_residue == expected_root
    assert matrix.endpoint_residue == expected_endpoint
    assert tuple(port.residue for port in matrix.punctures) == expected_punctures
    assert calls.count((initial, offset, base, places)) == 1
    # The pointed endpoint also supplies the selected conditional row and
    # final puncture, so its checked power is performed exactly once.
    assert calls.count((expected_root, steps, base, places)) == 1
    assert (initial, offset + steps, base, places) not in calls
    assert len(calls) == 14


def test_fermat_clock_declarations_share_construction_and_recheck_puncture(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.power_numbers.fermat_boundary_macros import (
        FermatClockLaw,
        issue_algebraic_root,
        issue_fermat_border_macro,
    )
    from number_compiler.sequences.power_numbers.three_power_outer_inner_cyclotomic import (
        FermatOuterCyclotomicClock,
    )

    original = FermatOuterCyclotomicClock.from_level
    calls: list[tuple[int, int]] = []

    def counted(level: int, offset: int = 0) -> FermatOuterCyclotomicClock:
        calls.append((level, offset))
        return original(level, offset)

    monkeypatch.setattr(FermatOuterCyclotomicClock, "from_level", counted)
    source = issue_algebraic_root(3, 7)
    macro = issue_fermat_border_macro(source)
    # Construction shares one source clock; publication independently checks
    # its puncture without caching or suppressing that forensic validation.
    assert calls == [(7, 0), (7, 0)]
    assert macro.producer_verified
    for clock in macro.clocks:
        identity = clock.identity
        assert type(identity) is FermatClockId
        assert clock.name == identity.display_label
        assert clock.source_residue == pow(3, 128, identity.modulus)
        assert clock.at(3) == pow(3, 131, identity.modulus)
        if identity.law is FermatClockLaw.EULER_TRIPLING:
            period = identity.exponent_period
            assert period is not None
            assert pow(3, period, identity.modulus) == 1
        else:
            assert identity.exponent_period is None
    for field_name, value in (("modulus", 1), ("display_label", "forged")):
        with pytest.raises(AttributeError):
            setattr(FermatClockId.DECIMAL_2_DIGITS, field_name, value)


def test_issued_fermat_macro_rejects_changed_clock_arithmetic(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.power_numbers.fermat_boundary_macros import (
        issue_algebraic_root,
        issue_fermat_border_macro,
    )

    macro = issue_fermat_border_macro(issue_algebraic_root(3, 7))
    identity = FermatClockId.DECIMAL_2_DIGITS
    assert macro.producer_verified
    with monkeypatch.context() as changed:
        changed.setattr(
            identity, "_value_", (identity.law, 1000, 400, identity.display_label)
        )
        assert not macro.producer_verified
        with pytest.raises(ValueError, match="unissued"):
            macro.clock(identity)
    assert macro.producer_verified
