"""Source-authenticated inward temporal harmonics, not a prime predicate."""

import pytest

from number_compiler.arithmetic.carry.tripling_transfer import (
    IDENTITY,
    compose_transfer,
    digit_transfer,
)
from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec
from number_compiler.sequences.power_numbers.three_power_bilateral_border import (
    _carry_h5,
)
from number_compiler.sequences.power_numbers.three_power_inward_phase_bank import (
    _certified_temporal_signal_periods,
    demand_inward_temporal_phase_bank,
    radix_phase_parameters,
)


def test_decimal_position_orbits_are_exact_and_nested() -> None:
    expected = [1, 4, 20, 100, 500, 2500]
    for k, period in enumerate(expected, start=1):
        pre, got = radix_phase_parameters(10, k)
        assert got == period
        assert pre == max(2, k - 2)
        modulus = 10**k
        for level in (pre, pre + 1, pre + 7, pre + period // 2):
            assert pow(3, 1 << level, modulus) == pow(
                3, pow(2, level + period, 2 ** max(2, k - 2) * 5 ** (k - 1)), modulus
            )
        signal_periods = _certified_temporal_signal_periods(10, k - 1)
        assert signal_periods is not None
        assert dict(signal_periods)["joint"] == period
        assert all(period % value == 0 for _, value in signal_periods)


def test_binary_eventual_transient_is_not_pumped_early() -> None:
    for depth in (1, 2, 8, 16, 64):
        transient, period = radix_phase_parameters(2, depth)
        assert period == 1
        mature = demand_inward_temporal_phase_bank(2, transient, depth)
        assert mature.source_prefix == 1
        assert mature.joint_future_phase == 0
        if transient > 1:
            immature = demand_inward_temporal_phase_bank(2, 1, depth)
            assert immature.joint_future_phase is None


def test_real_source_digits_carries_and_h5_exact_small_levels() -> None:
    for level in range(2, 9):
        full = 3 ** (1 << level)  # independent small-instance audit oracle
        for base in (2, 10):
            depth = min(20, (full.bit_length() if base == 2 else len(str(full))))
            bank = demand_inward_temporal_phase_bank(base, level, depth)
            assert bank.source_prefix == full % base**depth
            carry = 0
            transfer = IDENTITY
            for j, port in enumerate(bank.positions):
                digit = (full // base**j) % base
                assert digit == port.digit
                assert port.carry_in == carry
                transfer = compose_transfer(transfer, digit_transfer(base, digit))
                carry = (3 * digit + carry) // base
                assert port.carry_out == carry
                assert port.transfer == digit_transfer(base, digit)
                assert (port.low_carry_h5, port.high_carry_h5) == _carry_h5((carry,), j)
            assert bank.transfer_between(0, depth) == transfer
            assert bank.exact_ingress_at(depth) == carry
            assert bank.carry_h5 == _carry_h5(bank.carry_vector, 0)


def test_f4_f5_inward_temporal_separators() -> None:
    rows = {
        (4, 14): (81, 681, 2, 2),
        (4, 15): (61, 761, 1, 2),
        (5, 30): (81, 481, 2, 1),
        (5, 31): (61, 361, 1, 1),
    }
    for (index, level), (two, three, carry2, carry3) in rows.items():
        spec = FermatNumberSpec(index)
        original = spec.demand_three_power_bilateral_border(level)
        phased = spec.demand_three_power_inward_phase_quotient(level)
        decimal = phased.decimal_phase_bank
        binary = phased.binary_phase_bank
        assert decimal is not None and binary is not None
        assert decimal.source_prefix % 100 == two
        assert decimal.source_prefix % 1000 == three
        assert decimal.carry_vector[1] == carry2
        assert decimal.carry_vector[2] == carry3
        assert decimal.positions[2].source_period == 20
        assert decimal.positions[2].source_phase == (level - 2) % 20
        assert decimal.joint_moore_period == 2500
        assert phased.binary_middle.possible_actions
        assert phased.decimal_middle.possible_actions
        assert set(phased.binary_middle.possible_actions) <= set(
            original.binary.allowed_middle_actions
        )
        assert set(phased.decimal_middle.possible_actions) <= set(
            original.decimal.allowed_middle_actions
        )
        assert phased.partial_signed_fermat_contribution == (
            binary.partial_signed_fermat_contribution(index)
        )
        assert phased.terminal_status == "UNKNOWN"
        assert phased.bilateral.level == original.level == level


def test_phase_joint_adaptive_consumer_is_authoritative() -> None:
    for index, level in ((4, 14), (5, 30)):
        spec = FermatNumberSpec(index)
        adaptive = spec.demand_adaptive_three_power_interior(
            level, ((0, 128), (500, 16))
        )
        combined = adaptive.bilateral_source_constraints(
            phase_binary_places=64,
            phase_decimal_places=6,
            decimal_windows=((12, 4), (60, 4)),
        )
        assert combined.binary_phase_bank is not None
        assert combined.decimal_phase_bank is not None
        assert combined.binary_middle.possible_actions
        assert combined.decimal_middle.possible_actions
        assert combined.terminal_status == "UNKNOWN"


def test_temporal_power_is_dyadic_squaring_not_tripling() -> None:
    for base, depth in ((2, 40), (10, 6)):
        bank = demand_inward_temporal_phase_bank(base, 14, depth)
        advanced = bank.temporal_power(1)
        assert advanced.source_prefix == bank.source_prefix**2 % (base**depth)
        assert advanced.source_prefix != (3 * bank.source_prefix) % (base**depth)
        jumped = bank.temporal_power(10**6)
        assert jumped.source_phase is not None
        assert jumped.preperiod <= jumped.level
        assert (
            jumped.source_prefix
            == demand_inward_temporal_phase_bank(base, 14 + 10**6, depth).source_prefix
        )
        with pytest.raises(ValueError):
            bank.temporal_power(-1)


def test_carry_and_walsh_equal_does_not_determine_signed_fold() -> None:
    # Two distinct interiors with identical action, same terminal carry and
    # both *whole-middle* H5 packets.  Their Fermat-fold contributions differ.
    signatures: dict[tuple[object, ...], int] = {}
    found = None
    for value in range(1 << 10):
        action = IDENTITY
        carry = 0
        carries = []
        for j in range(10):
            bit = (value >> j) & 1
            action = compose_transfer(action, digit_transfer(2, bit))
            carry = (3 * bit + carry) // 2
            carries.append(carry)
        harmonic = tuple(
            (p.phi2, p.phi3_a, p.phi3_b) for p in _carry_h5(tuple(carries), 0)
        )
        signature = (action, carry, harmonic)
        prior = signatures.get(signature)
        if prior is not None and prior != value and prior % 257 != value % 257:
            found = (prior, value)
            break
        signatures[signature] = value
    assert found == (7, 56)
    assert 7 % 257 != 56 % 257


def test_phase_precision_budget_and_false_source_checks() -> None:
    with pytest.raises(ValueError, match="precision"):
        demand_inward_temporal_phase_bank(10, 14, 513)
    with pytest.raises(ValueError, match="radix"):
        radix_phase_parameters(7, 4)
    with pytest.raises(ValueError):
        FermatNumberSpec(4).demand_three_power_inward_phase_quotient(
            14, phase_decimal_places=1
        )


@pytest.mark.parametrize("kind", ["copy", "alias", "nested"])
def test_inward_source_authority_rejects_forgery(kind: str) -> None:
    from dataclasses import replace

    bank = demand_inward_temporal_phase_bank(10, 14, 3)
    if kind == "copy":
        bank = replace(bank)
    elif kind == "alias":
        object.__setattr__(bank, "base", 10.0)
    else:
        object.__setattr__(bank.positions[0], "digit", 99)
    assert not bank.producer_verified
    with pytest.raises(ValueError, match="unissued or changed"):
        bank.temporal_power(1)


def test_temporal_power_reuses_complete_observer_partition(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.power_numbers.three_power_inward_phase_bank as owner

    bank = owner.demand_inward_temporal_phase_bank(10, 14, 6)

    def forbidden(*args: object, **kwargs: object) -> object:
        raise AssertionError("warm temporal advance rediscovered finite orbit")

    monkeypatch.setattr(owner, "minimize_finite_orbit", forbidden)
    target = bank.temporal_power(10**6)
    assert target.producer_verified
    assert tuple(p.moore_periods for p in target.positions) == tuple(
        p.moore_periods for p in bank.positions
    )
    assert target.source_prefix == pow(3, pow(2, target.level, 16 * 5**5), 10**6)


def test_interior_rejects_foreign_phase_and_window_authority() -> None:
    from dataclasses import replace

    spec = FermatNumberSpec(4)
    first = spec.demand_three_power_inward_phase_quotient(14)
    second = spec.demand_three_power_inward_phase_quotient(15)
    with pytest.raises(ValueError, match="another source border"):
        replace(first, decimal_middle=second.decimal_middle)
    with pytest.raises(ValueError, match="another source occurrence"):
        replace(first, decimal_phase_bank=second.decimal_phase_bank)


def test_inward_bank_point_read_does_not_scan_unused_positions() -> None:
    bank = demand_inward_temporal_phase_bank(10, 14, 4)
    expected = bank.carry_vector[0]
    object.__setattr__(bank.positions[3], "digit", 99)
    assert bank.exact_ingress_at(1) == expected
    with pytest.raises(
        ValueError, match="changed inward phase bank: selected position"
    ):
        bank.transfer_between(0, bank.depth)


def test_inward_bank_rejects_changed_selected_position() -> None:
    bank = demand_inward_temporal_phase_bank(10, 14, 3)
    object.__setattr__(bank.positions[1], "digit", 99)
    with pytest.raises(
        ValueError, match="changed inward phase bank: selected position"
    ):
        bank.transfer_between(1, 2)


def test_harmonic_issuer_is_bound_to_the_exact_record_type() -> None:
    from number_compiler.sequences.power_numbers._harmonic_authority import (
        harmonic_payload,
        issue_harmonic,
        new_harmonic_issuer,
    )

    bank = demand_inward_temporal_phase_bank(10, 14, 2)
    wrong_issuer = new_harmonic_issuer(type(bank.positions[0]))
    with pytest.raises(TypeError, match="does not own"):
        issue_harmonic(bank, harmonic_payload(bank), issuer=wrong_issuer)


def test_oversized_source_level_is_rejected_before_period_construction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.power_numbers.three_power_inward_phase_bank as owner

    def forbidden(*args: object, **kwargs: object) -> object:
        raise AssertionError("period descriptors were built before source admission")

    monkeypatch.setattr(owner, "_certified_temporal_signal_periods", forbidden)
    with pytest.raises(ValueError, match="source level exceeds"):
        demand_inward_temporal_phase_bank(10, 1 << 4096, 1)


def test_harmonic_snapshot_preflights_children_and_checks_flat_node_count(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.power_numbers._harmonic_authority as authority
    from number_compiler.arithmetic.contracts.iterative_queries import (
        enter_ordered_children,
    )

    def guarded_schedule(
        stack: list[tuple[object, bool]],
        active: set[int],
        parent: object,
        children: tuple[object, ...],
    ) -> None:
        assert len(children) < 1_000
        enter_ordered_children(stack, active, parent, children)

    monkeypatch.setattr(authority, "enter_ordered_children", guarded_schedule)
    wide_payload = (tuple(range(authority._MAX_SNAPSHOT_NODES)),)
    with pytest.raises(ValueError, match="snapshot budget"):
        authority.snapshot_harmonic_payload(wide_payload)

    payload = (1, 2)
    snapshot = authority.snapshot_harmonic_payload(payload)
    inconsistent_count = authority.HarmonicSnapshot(
        snapshot.tokens,
        snapshot.retained_nodes + 1,
        snapshot.retained_bytes,
    )
    assert not authority.harmonic_snapshot_matches(payload, inconsistent_count)
