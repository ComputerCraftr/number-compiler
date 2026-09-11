from number_compiler.arithmetic.carry.carry_itinerary import (
    LiveCarryItinerary,
    PairParityChannels,
    adaptive_cyclic_memory_horizon,
    adaptive_negacyclic_memory_horizon,
    adaptive_zplus1_memory_horizon,
    carry_from_threshold_itinerary,
    carry_threshold_itinerary,
    cyclic_class_sums,
    cyclic_growth_operator_rank,
    digit_pair_sum_fiber_size,
    even_width_palindrome_has_z_plus_one_factor,
    growth_run_itinerary,
    negacyclic_class_sums,
    negacyclic_pair_advance,
    negacyclic_transport_kernel,
    pair_field_preimage_count,
    polynomial_growth_operator_rank,
    reverse_add_base_pm_advance,
    reverse_add_base_pm_residues,
    reverse_add_base_squared_minus_one_residue,
    threshold_reset_count,
    zplus1_jet,
    zplus1_jet_advance,
)
from number_compiler.arithmetic.carry.event_memory import (
    carry_field,
    forcing_event,
    pair_step,
)


def _pair_from_int(value: int, base: int = 10) -> tuple[int, ...]:
    digits = []
    n = value
    while n:
        digits.append(n % base)
        n //= base
    digits = digits or [0]
    return tuple(digits[i] + digits[-1 - i] for i in range(len(digits)))


def _reverse_int(value: int, base: int = 10) -> int:
    digits = []
    n = value
    while n:
        digits.append(n % base)
        n //= base
    digits = digits or [0]
    out = 0
    for digit in digits:
        out = out * base + digit
    return out


def test_threshold_itinerary_is_exact_last_event_carry_coordinate() -> None:
    for base in range(3, 17):
        for pair in (
            tuple(range(base - 1, base + 2)),
            tuple([0, base - 1, 2 * (base - 1), base - 1, 0]),
        ):
            symbols = carry_threshold_itinerary(pair, base=base)
            assert carry_from_threshold_itinerary(symbols) == carry_field(
                pair, base=base
            )
            assert threshold_reset_count(symbols) == sum(v != base - 1 for v in pair)


def test_additive_digit_hyperbolic_fibers_are_already_quotiented_by_pair_field() -> (
    None
):
    assert [digit_pair_sum_fiber_size(s, base=10) for s in (0, 1, 9, 10, 17, 18)] == [
        1,
        2,
        10,
        9,
        2,
        1,
    ]
    pair = _pair_from_int(196)
    assert pair == (7, 18, 7)
    assert pair_field_preimage_count(pair, base=10) == 7
    # All seven fixed-width choices of end digits summing to seven have the same pair field
    # and therefore the same canonical pair successor; retaining a/b lanes would
    # reintroduce information the pair quotient has already eliminated.
    successors = set()
    for a in range(1, 8):
        b = 7 - a
        n = 100 * a + 90 + b
        p = _pair_from_int(n)
        assert p == pair
        successors.add(pair_step(p, 10)[0])
    assert len(successors) == 1


def test_z2_cyclic_pair_channels_advance_exactly_with_event_recurrence() -> None:
    pair = _pair_from_int(196)
    state = PairParityChannels.from_values(pair, modulus=32)
    for _ in range(128):
        target, growth = pair_step(pair, 10)
        event = forcing_event(pair, target, growth)
        state = state.advance(event, growth)
        assert (state.even, state.odd) == cyclic_class_sums(target, 2, 32)
        if growth:
            # The linear old-state contribution to the alternating z=-1 mode
            # is exactly zero; only the new event remains.
            e = PairParityChannels.from_values(event, modulus=32)
            assert state.alternating == e.alternating
        pair = target


def test_mod99_coordinate_enters_exact_six_cycle_for_decimal_196() -> None:
    n = 196
    residues = []
    plus_zero_at = None
    for step in range(15):
        width = len(str(n))
        minus, plus = reverse_add_base_pm_residues(n, width, base=10)
        residues.append(
            reverse_add_base_squared_minus_one_residue(minus, plus, base=10)
        )
        assert residues[-1] == n % 99
        if plus == 0 and plus_zero_at is None:
            plus_zero_at = step
        predicted = reverse_add_base_pm_advance(minus, plus, width, base=10)
        nxt = n + _reverse_int(n)
        assert predicted == reverse_add_base_pm_residues(nxt, len(str(nxt)), base=10)
        n = nxt
    assert plus_zero_at == 3
    assert residues[3:15] == [11, 22, 44, 88, 77, 55] * 2


def test_even_width_symmetric_pair_polynomial_has_z_plus_one_factor() -> None:
    pair = _pair_from_int(1675)
    assert len(pair) == 4 and pair == pair[::-1]
    assert even_width_palindrome_has_z_plus_one_factor(pair)
    assert sum(((-1) ** i) * value for i, value in enumerate(pair)) == 0


def test_prime_polynomial_growth_operator_exposes_rank_collapse_and_f2_nilpotence() -> (
    None
):
    # z^2=1: I+shift has rank one over odd fields, and over F2 its square is zero.
    assert cyclic_growth_operator_rank(2, 5, power=1) == 1
    assert cyclic_growth_operator_rank(2, 5, power=2) == 1
    assert cyclic_growth_operator_rank(2, 2, power=1) == 1
    assert cyclic_growth_operator_rank(2, 2, power=2) == 0
    # z^4=1 over F2 gives a four-step nilpotent growth operator.
    assert cyclic_growth_operator_rank(4, 2, power=3) > 0
    assert cyclic_growth_operator_rank(4, 2, power=4) == 0


def test_irreducible_prime_polynomials_do_not_create_growth_forgetting() -> None:
    # F2: z^2+z+1 is irreducible and 1+z is therefore a unit.
    assert polynomial_growth_operator_rank((1, 1, 1), 2, power=1) == 2
    assert polynomial_growth_operator_rank((1, 1, 1), 2, power=8) == 2
    # F3: z^2+1 is irreducible and again gives full rank.
    assert polynomial_growth_operator_rank((1, 0, 1), 3, power=1) == 2
    # Rank loss comes from the z+1 primary factor, not from a generic prime polynomial.
    assert polynomial_growth_operator_rank((1, 1), 2, power=1) == 0
    assert polynomial_growth_operator_rank((1, 2, 1), 3, power=1) == 1
    assert polynomial_growth_operator_rank((1, 2, 1), 3, power=2) == 0


def test_negacyclic_mod101_style_quotient_advances_exactly_and_two_growths_gain_factor_two() -> (
    None
):
    pair = _pair_from_int(196)
    state = negacyclic_class_sums(pair, 2, 32)
    for _ in range(128):
        target, growth = pair_step(pair, 10)
        event = forcing_event(pair, target, growth)
        state = negacyclic_pair_advance(state, event, growth, modulus=32)
        assert state == negacyclic_class_sums(target, 2, 32)
        pair = target
    # In z^2=-1, (1+z)^2=2z exactly.
    assert negacyclic_transport_kernel(2, 0, 2, modulus=32) == (0, 2)
    assert negacyclic_transport_kernel(2, 0, 10, modulus=32) == (0, 0)


def test_zplus1_primary_jet_is_exact_and_growth_is_literal_shift() -> None:
    pair = _pair_from_int(196)
    for degree in (1, 2, 4, 8):
        state = zplus1_jet(pair, degree, 32)
        current = pair
        for _ in range(96):
            target, growth = pair_step(current, 10)
            event = forcing_event(current, target, growth)
            state = zplus1_jet_advance(state, event, growth, modulus=32)
            assert state == zplus1_jet(target, degree, 32)
            current = target


def test_primary_and_negacyclic_memory_are_schedule_adaptive_on_196_trace() -> None:
    pair = _pair_from_int(196)
    growths = []
    for _ in range(256):
        pair, growth = pair_step(pair, 10)
        growths.append(growth)
    # Degree-k primary jets forget once either five no-growths or k growths occurred.
    for degree in (1, 2, 4, 8):
        horizons = [
            adaptive_zplus1_memory_horizon(growths, endpoint, degree=degree, bits=5)
            for endpoint in range(20, len(growths) + 1)
        ]
        assert all(h is not None for h in horizons)
        assert max(h for h in horizons if h is not None) < 20
    # z^2=-1 additionally converts every pair of growths into 2-adic decay.
    horizons = [
        adaptive_negacyclic_memory_horizon(growths, endpoint, classes=2, bits=5)
        for endpoint in range(20, len(growths) + 1)
    ]
    assert all(h is not None for h in horizons)
    assert max(h for h in horizons if h is not None) < 20


def test_adaptive_cyclic_memory_is_far_shorter_than_fixed_20_on_196_trace() -> None:
    pair = _pair_from_int(196)
    growths = []
    for _ in range(256):
        pair, growth = pair_step(pair, 10)
        growths.append(growth)
    for classes, max_expected in ((1, 5), (2, 6), (4, 9), (8, 11)):
        horizons = [
            adaptive_cyclic_memory_horizon(growths, endpoint, classes=classes, bits=5)
            for endpoint in range(20, len(growths) + 1)
        ]
        assert all(h is not None for h in horizons)
        assert max(h for h in horizons if h is not None) <= max_expected
        assert max(h for h in horizons if h is not None) < 20


def test_growth_run_itinerary_is_base4_weighted_time_coordinate_on_196_trace() -> None:
    pair = _pair_from_int(196)
    growths = []
    for _ in range(512):
        pair, growth = pair_step(pair, 10)
        growths.append(growth)
    runs = growth_run_itinerary(growths)
    assert runs
    assert max(runs) <= 3
    # Every completed epoch contributes r growth transitions plus one no-growth.
    completed_steps = sum(r + 1 for r in runs)
    trailing = len(growths) - completed_steps
    assert 0 <= trailing <= 3


def test_fixed20_event_window_has_exact_dead_prefix_on_closed_196_schedule() -> None:
    from number_compiler.arithmetic.carry.carry_itinerary import (
        live_event_suffix_length,
    )
    from number_compiler.arithmetic.carry.event_memory import forcing_event_from_carry

    pair = _pair_from_int(196)
    events = []
    lengths = []
    for _ in range(320):
        c = carry_field(pair, base=10)
        events.append(forcing_event_from_carry(c, base=10))
        pair, _growth = pair_step(pair, 10)
        if len(events) >= 20:
            live = live_event_suffix_length(events[-20:], base=10)
            assert 1 <= live <= 20
            lengths.append(live)
    assert max(lengths[100:]) <= 11
    assert sum(lengths[100:]) / len(lengths[100:]) < 9.0


def test_live_carry_itinerary_self_prunes_and_advances_without_discarded_rows() -> None:
    pair = _pair_from_int(196)
    seed_carries = []
    for _ in range(20):
        seed_carries.append(carry_field(pair, base=10))
        pair, _ = pair_step(pair, 10)
    live = LiveCarryItinerary.seed(seed_carries, base=10)
    rows = []
    for _ in range(300):
        assert live.pair == pair
        rows.append(live.row_count)
        live = live.advance()
        pair, _ = pair_step(pair, 10)
    assert max(rows[100:]) <= 11
    assert sum(rows[100:]) / len(rows[100:]) < 9.0
    assert live.dropped_rows > 250


def test_live_carry_itinerary_generalizes_across_bases_3_through_16() -> None:
    from number_compiler.arithmetic.carry.event_memory import event_memory_horizon

    for base in range(3, 17):
        value = 2 * base**2 + (base - 1) * base + 1
        pair = _pair_from_int(value, base)
        carries = []
        for _ in range(event_memory_horizon(base)):
            carries.append(carry_field(pair, base=base))
            pair, _ = pair_step(pair, base)
        live = LiveCarryItinerary.seed(carries, base=base)
        for _ in range(24):
            assert live.pair == pair
            live = live.advance()
            pair, _ = pair_step(pair, base)
