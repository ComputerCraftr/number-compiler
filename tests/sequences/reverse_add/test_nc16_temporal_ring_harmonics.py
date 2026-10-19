"""NC16 reverse/add-only macro ring, born/dying carries and inner masks."""

from __future__ import annotations

from dataclasses import replace
from math import comb
from random import Random

import pytest

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    value_carry_fn,
)
from number_compiler.arithmetic.fields.decimal_pair_partition import (
    DECIMAL_PAIR_BANDS,
    DecimalPairBand,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.sequences.reverse_add.macro_conditioned_harmonics import (
    all_reverse_add_macro_harmonics,
)
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from number_compiler.sequences.reverse_add.symmetric_carry_filter import (
    filter_symmetric_transfer,
)
from number_compiler.sequences.reverse_add.temporal_inward_constraints import (
    ReverseInwardConstraints,
)
from number_compiler.sequences.reverse_add.temporal_ring_channels import (
    ReverseTemporalRingChannel,
    checked_temporal_ring_channel,
)
from number_compiler.sequences.reverse_add.temporal_ring_harmonics import (
    ReverseAddTemporalRingBank,
)
from tests.support.reverse_add_source_data import reverse_add_source_data


@pytest.mark.parametrize("options", [(1, 1), (1, 2, 2), (9, 9)])
def test_digit_domain_duplicates_are_idempotent(options: tuple[int, ...]) -> None:
    constraints = ReverseInwardConstraints((2,))
    constraints.constrain_digit(0, 1, options)
    assert constraints.digit_domain(0, 1) == tuple(sorted(set(options)))


@pytest.mark.parametrize("options", [True, (True,), (), (-1,), (10,)])
def test_digit_domain_rejects_non_decimal_options(
    options: int | tuple[int, ...],
) -> None:
    constraints = ReverseInwardConstraints((2,))
    with pytest.raises(ValueError):
        constraints.constrain_digit(0, 1, options)


def test_symmetric_filter_matches_all_small_assignments_and_stops_at_first_reset() -> (
    None
):
    domains = ((8, 9), (9, 10))
    center = (8, 10)
    allowed = (CarryFn.CONST0, CarryFn.CONST1)
    filtered = filter_symmetric_transfer(domains, allowed, center=center)

    assignments = tuple(
        (first, second, middle)
        for first in domains[0]
        for second in domains[1]
        for middle in center
    )

    def transfer(values: tuple[int, ...]) -> CarryFn:
        for value in values:
            action = value_carry_fn(value, 10)
            if action is not CarryFn.ID:
                return action
        return CarryFn.ID

    supported = tuple(row for row in assignments if transfer(row) in allowed)
    assert filtered.possible_transfers == tuple(
        action
        for action in CarryFn
        if any(transfer(row) is action for row in assignments) and action in allowed
    )
    assert filtered.supported_pairs == tuple(
        tuple(
            value for value in domain if any(row[index] == value for row in supported)
        )
        for index, domain in enumerate(domains)
    )
    assert filtered.supported_center == tuple(
        value for value in center if any(row[2] == value for row in supported)
    )

    # Once the outer pair is a reset, a later inner reset cannot replace it.
    impossible = filter_symmetric_transfer(((8,), (10,)), (CarryFn.CONST1,))
    assert impossible.possible_transfers == ()
    assert impossible.supported_pairs == ((), ())


def successor(x: int) -> int:
    return x + int(str(x)[::-1])


def pair(x: int, position: int) -> int:
    word = str(x)
    return int(word[position]) + int(word[-position - 1])


def band(s: int) -> DecimalPairBand:
    return (
        DecimalPairBand.LT_LOW
        if s <= 4
        else DecimalPairBand.LT_HIGH
        if s <= 8
        else DecimalPairBand.EQ
        if s == 9
        else DecimalPairBand.GT_LOW
        if s <= 14
        else DecimalPairBand.GT_HIGH
    )


def owner_for(x: int) -> tuple[ResourceLedger, ReversePairQ19OutputOwner]:
    ledger = ResourceLedger()
    return ledger, ReversePairQ19OutputOwner(ledger, digits_lsd(x, 10), base=10)


def gen196(n: int) -> int:
    x = 196
    for _ in range(n):
        x = successor(x)
    return x


def test_all_96_reverse_add_cycles_have_independent_f5_powers() -> None:
    catalogue = all_reverse_add_macro_harmonics()
    assert len(catalogue) == 96
    assert sum(action.duration for action in catalogue) == 1461
    for action in catalogue:
        assert action.growth >= 1
        assert not action.future_source_certified
        for k in (0, 1, 2, 7):
            for i in (0, 1, 2, 3):
                expected = (
                    pow(2, action.quiet * k, 5)
                    * (comb(action.growth * k, i) if i <= action.growth * k else 0)
                ) % 5
                assert action.homogeneous_coefficient_mod5(i, repeats=k) == expected
        assert all(phase.admitted_middle for phase in action.carry_safety_phases())
        assert action.homogeneous_mode_mod5(4) == 0


def test_generation_79_certified_ring_has_two_sided_phase_harmonics() -> None:
    x = gen196(79)
    ledger, owner = owner_for(x)
    try:
        ring = owner.authorize_temporal_ring_bank(
            owner.initial,
            steps=9,
            window_digits=3,
            positions=tuple(range(8)),
            source_pair_prefix=8,
        )
        # A module issuer token alone is not enough: even a byte-for-byte
        # replacement must be the exact ring retained by this Q19 owner.
        with pytest.raises(ValueError):
            replace(ring)
        first = ring.bank_words[0]
        changed_lane = None if first.lanes[0] is not None else 0
        changed_words = (
            replace(first, lanes=(changed_lane, *first.lanes[1:])),
            *ring.bank_words[1:],
        )
        with pytest.raises(ValueError):
            replace(ring, bank_words=changed_words)
        issued_words = ring.bank_words
        object.__setattr__(ring, "bank_words", changed_words)
        with pytest.raises(ValueError):
            ring.harmonic(0, DecimalPairBand.LT_HIGH)
        object.__setattr__(ring, "bank_words", issued_words)
        ring.harmonic(0, DecimalPairBand.LT_HIGH)
        assert ring.macro is not None
        assert ring.certificate.growth_word == (0, 1, 0, 0, 1, 0, 1, 0, 1)
        assert ring.macro.growth == 4
        assert ring.macro.quiet == 5
        assert ring.macro.homogeneous_mode_mod5(4) == 0
        assert ring.widths[0] == 38 and ring.widths[-1] == 42
        assert (
            ledger.counters[
                _reverse_add_keys.REVERSE_Q19_INWARD_SYMMETRIC_FILTER_VALUE_VISITS
            ]
            > 0
        )
        assert ring.harmonic(0, DecimalPairBand.LT_HIGH).forced_count == 9
        with pytest.raises(TypeError):
            checked_temporal_ring_channel("lt_high")
        original_band_value = DecimalPairBand.LT_HIGH.value
        object.__setattr__(DecimalPairBand.LT_HIGH, "_value_", "tampered")
        try:
            with pytest.raises(ValueError):
                ring.harmonic(0, DecimalPairBand.LT_HIGH)
        finally:
            object.__setattr__(DecimalPairBand.LT_HIGH, "_value_", original_band_value)
        assert len(ring.phase_pair_domains) == 8
        assert all(
            len(domain) >= 1 for row in ring.phase_pair_domains for domain in row
        )
        assert ring.harmonic(0, ReverseTemporalRingChannel.F5).forced_count == 9
        assert not ring.temporal_repeat_certified
        assert not ring.complete_integer_certified
        values = [x]
        for _ in range(9):
            values.append(successor(values[-1]))
        for position in range(8):
            orbit = ring.orbit(position)
            harmonics = {
                channel: ring.harmonic(position, channel)
                for channel in DECIMAL_PAIR_BANDS
            }
            for t in range(9):
                coeff = pair(values[t], position)
                assert coeff % 5 in orbit.pair_f5[t]
                assert (
                    coeff in ring.phase_pair_domains[ring.positions.index(position)][t]
                )
                assert band(coeff) in orbit.selected_bands[t]
                for channel, harmonic in harmonics.items():
                    observed = harmonic.lanes[t]
                    if observed is not None:
                        assert observed == int(band(coeff) == channel)
        with pytest.raises(ValueError):
            ring.then(ring)
        period, count = ring.formal_repeated_output(0, DecimalPairBand.LT_HIGH, 10**18)
        assert len(period) == 9 and count == 10**18
        owner.dispose()
        with pytest.raises(ValueError):
            ring.harmonic(0, DecimalPairBand.LT_HIGH)
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_validated_pair_domains_check_full_ring_authority_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    x = gen196(79)
    ledger, owner = owner_for(x)
    try:
        certificate = owner.certify_border_growth(
            owner.initial, steps=9, window_digits=3
        )
        ring = certificate.temporal_ring_bank(
            positions=tuple(range(8)), source_pair_prefix=8
        )
        original_check = ReverseAddTemporalRingBank.validate
        checks = 0

        def counted_check(record: ReverseAddTemporalRingBank) -> None:
            nonlocal checks
            checks += 1
            original_check(record)

        monkeypatch.setattr(ReverseAddTemporalRingBank, "validate", counted_check)
        domains = ring.validated_pair_domains()
        assert checks == 1
        assert len(domains) == len(ring.positions) == 8
        assert all(
            source == row[0] and target == row[-1]
            for (source, target), row in zip(
                domains, ring.phase_pair_domains, strict=True
            )
        )

        original_domains = ring.phase_pair_domains
        changed = (((), *original_domains[0][1:]), *original_domains[1:])
        object.__setattr__(ring, "phase_pair_domains", changed)
        with pytest.raises(ValueError):
            ring.validated_pair_domains()
        assert checks == 2
        object.__setattr__(ring, "phase_pair_domains", original_domains)
        assert len(ring.validated_pair_domains()) == 8
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


@pytest.mark.parametrize("start", [48, 50, 52, 54])
def test_nested_92_28_macro_and_93_exit_are_derived_from_source(start: int) -> None:
    x = gen196(start)
    assert str(x).startswith("92") and str(x).endswith("28")
    ledger, owner = owner_for(x)
    try:
        cert = owner.certify_border_growth(owner.initial, steps=2, window_digits=3)
        assert cert.outer_pairs[0] == cert.outer_pairs[2] == (9, 8)
        # A one-digit return is NOT a proof of a return of the two-digit tile.
        assert cert.window_tiles[-1] is None
        ring = cert.temporal_ring_bank(
            positions=(0, 1, 2, 3),
            include_source_digits=True,
        )
        assert ring.macro is not None
        values = [x, successor(x), successor(successor(x))]
        for pos in ring.positions:
            orbit = ring.orbit(pos)
            for t in range(2):
                assert orbit.pair_f5[t] == (pair(values[t], pos) % 5,)
                assert ring.phase_pair_domains[ring.positions.index(pos)][t] == (
                    pair(values[t], pos),
                )
                assert orbit.selected_bands[t] == (band(pair(values[t], pos)),)
        # In this last case third-pair GT forcing causes 93, not 92.
        if start == 54:
            assert str(values[-1]).startswith("93")
        else:
            assert str(values[-1]).startswith("92")
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_44_88_carry_birth_phase_is_not_2rev10() -> None:
    x = gen196(31)
    ledger, owner = owner_for(x)
    try:
        ring = owner.authorize_temporal_ring_bank(
            owner.initial,
            steps=2,
            positions=(0, 1, 2, 3),
            window_digits=3,
            include_source_digits=True,
        )
        values = [x, successor(x)]
        assert str(values[0]).startswith("44")
        assert str(values[1]).startswith("88")
        expected_widths = (
            len(str(x)),
            len(str(values[1])),
            len(str(successor(values[1]))),
        )
        assert ring.widths == expected_widths
        assert all(
            ring.orbit(i).selected_bands[1] == (band(pair(values[1], i)),)
            for i in ring.positions
        )
        assert any(
            (1,) in ring.orbit(i).low_birth + ring.orbit(i).reflected_birth
            for i in ring.positions
        )
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_true_digit_orbits_with_random_sources_and_width_shifts() -> None:
    rng = Random(20261016)
    for _ in range(55):
        w = rng.randrange(3, 16)
        x = rng.randrange(10 ** (w - 1), 10**w)
        ledger, owner = owner_for(x)
        try:
            ring = owner.authorize_temporal_ring_bank(
                owner.initial,
                steps=1,
                window_digits=1,
                positions=tuple(range(min(w // 2, 5))),
                include_source_digits=True,
            )
            nxt = successor(x)
            system = ring.certificate.inward_temporal_constraints(
                include_source_digits=True
            )
            system.propagate()
            assert system.widths == (w, len(str(nxt)))
            for i in range(min(w // 2, 5)):
                assert system.pair_domain(0, i) == (pair(x, i),)
                assert system.pair_domain(1, i) == (pair(nxt, i),)
                assert ring.orbit(i).selected_bands[0] == (band(pair(x, i)),)
        finally:
            owner.dispose()
            assert ledger.entries == ledger.nodes == 0


def test_later_q19_source_is_rebased_not_replayed() -> None:
    ledger, owner = owner_for(196)
    try:
        later = owner.apply_pair_step(owner.initial)
        cert = owner.certify_border_growth(later, steps=3, window_digits=1)
        ring = cert.temporal_ring_bank(
            start=1, duration=2, positions=(0,), source_pair_prefix=1
        )
        assert ring.widths == (4, 4, 5)
        assert ring.start == 1 and ring.duration == 2
        assert ring.orbit(0).selected_bands[0] == (band(pair(1675, 0)),)
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_finite_action_composition_requires_exact_source_and_width_seam() -> None:
    x = gen196(79)
    ld, owner = owner_for(x)
    try:
        cert = owner.certify_border_growth(owner.initial, steps=9, window_digits=3)
        a = cert.temporal_ring_bank(
            start=0, duration=4, positions=(0, 1), source_pair_prefix=2
        )
        b = cert.temporal_ring_bank(
            start=4, duration=5, positions=(0, 1), source_pair_prefix=2
        )
        together = a.then(b)
        assert together.duration == 9 and together.widths == a.widths + b.widths[1:]
        assert together.macro is not None
        assert together.target_pair_domain(0) == b.target_pair_domain(0)
        for i in (0, 1):
            for channel in (
                DecimalPairBand.LT_LOW,
                DecimalPairBand.GT_HIGH,
                DecimalPairBand.EQ,
                ReverseTemporalRingChannel.CARRY_XOR,
            ):
                assert together.harmonic(i, channel).lanes == (
                    a.harmonic(i, channel).lanes + b.harmonic(i, channel).lanes
                )
        with pytest.raises(ValueError):
            b.then(a)
    finally:
        owner.dispose()
        assert ld.entries == ld.nodes == 0


def test_source_driven_temporal_matrix_uses_changing_inner_carries() -> None:
    from number_compiler.sequences.reverse_add.conditional_pair_ring import (
        input_driven_moore_classes,
    )

    x = gen196(79)
    ledger, owner = owner_for(x)
    try:
        ring = owner.authorize_temporal_ring_bank(
            owner.initial,
            steps=9,
            window_digits=3,
            positions=(0, 1, 2),
            include_source_digits=True,
        )
        values = [x]
        for _ in range(9):
            values.append(successor(values[-1]))
        for position in (0, 1, 2):
            action = ring.conditional_input_action(position)
            assert action.duration == 9
            assert action.growth_count == 4
            initial = pair(values[0], position)
            assert action.targets[initial] == pair(values[-1], position)
            counts = tuple(
                sum(band(pair(v, position)) == name for v in values[1:])
                for name in DECIMAL_PAIR_BANDS
            )
            assert action.band_counts[initial] == counts
            assert not action.physical_input_repeat_certified
        from number_compiler.sequences.reverse_add.conditional_pair_ring import (
            ConditionalRingPairAction,
            RingPairLetter,
        )

        port = RingPairLetter(1, 0, None, 0, 0)
        classes = input_driven_moore_classes((port,), observation="coefficient")
        assert len(classes) == 19 and len(set(classes)) == 19
        action = ConditionalRingPairAction.letter(port)
        huge = action.formal_power(10**18)
        assert huge.duration == 10**18
        assert not huge.physical_input_repeat_certified
        assert huge.targets[0] == 0
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_all_local_pair_input_ports_match_true_reverse_add() -> None:
    from number_compiler.sequences.reverse_add.conditional_pair_ring import (
        RingPairLetter,
    )

    rng = Random(102016)
    checked = 0
    for _ in range(175):
        w = rng.randrange(3, 35)
        x = rng.randrange(10 ** (w - 1), 10**w)
        w, sums, carries, growth, target_pairs = reverse_add_source_data(x)
        limit = min((w - 1) // 2, 12)
        for pos in range(limit):
            prev = sums[pos - 1] if growth and pos else None
            port = RingPairLetter(pos, growth, prev, carries[pos], carries[w - 1 - pos])
            assert port.successor(sums[pos]) == target_pairs[pos]
            checked += 1
    assert checked >= 700


def test_spatial_walsh64_reuses_forced_gt_bank_and_refuses_unknown_lanes() -> None:
    x = int("1" * 145)
    ld, owner = owner_for(x)
    try:
        ring = owner.authorize_temporal_ring_bank(
            owner.initial,
            steps=1,
            window_digits=3,
            positions=tuple(range(64)),
            include_source_digits=True,
        )
        assert ring.harmonic(0, DecimalPairBand.LT_LOW).lanes == (1,)
        assert ring.spatial_walsh64_mod5(DecimalPairBand.LT_LOW) == (4,) + (0,) * 63
        assert ring.spatial_walsh64_mod5(DecimalPairBand.GT_HIGH) == (0,) * 64
        with pytest.raises(ValueError):
            ring.spatial_walsh64_mod5(ReverseTemporalRingChannel.F5)
    finally:
        owner.dispose()
        assert ld.entries == ld.nodes == 0


def test_source_certified_temporal_bank_forces_ring_f5_orbit_without_replay() -> None:
    """The reverse/add GT-bank supplies an *input* to the inward ring, not an observer."""
    from tests.support.reverse_add_banks import source_guarded_periodic_temporal_bank

    with source_guarded_periodic_temporal_bank() as (_ledger, owner, cert, bank):
        pos = bank.coordinate
        unconstrained = cert.temporal_ring_bank(positions=(pos,))
        assert len(unconstrained.target_pair_domain(pos)) > 1
        ring = bank.temporal_ring_bank(positions=(pos,))
        expected = tuple(bank.at(t) for t in range(bank.steps + 1))
        assert ring.phase_pair_domains[0] == tuple((s,) for s in expected)
        assert ring.target_pair_domain(pos) == (expected[-1],)
        assert ring.harmonic(pos, ReverseTemporalRingChannel.F5).lanes == tuple(
            s % 5 for s in expected[:-1]
        )
        assert ring.harmonic(pos, DecimalPairBand.GT_HIGH).lanes == tuple(
            int(15 <= s <= 18) for s in expected[:-1]
        )
        forced = ring.diagnostic()["forced_lanes"]
        unconstrained_forced = unconstrained.diagnostic()["forced_lanes"]
        assert isinstance(forced, int)
        assert isinstance(unconstrained_forced, int)
        assert forced > unconstrained_forced
        # Verify the bank's real physical source (and its growth shifts)
        # against an entirely separate scalar decimal recurrence.
        x = int("".join(str(d) for d in owner._digits[::-1]))
        for t, coeff in enumerate(expected):
            assert pair(x, pos) == coeff
            if t < bank.steps:
                x = successor(x)
        assert ring.complete_integer_certified is False
        assert ring.temporal_repeat_certified is False


def test_temporal_ring_work_counters_track_construction_not_observation() -> None:
    ledger, owner = owner_for(196)
    try:
        certificate = owner.certify_border_growth(
            owner.initial, steps=1, window_digits=1
        )
        ring_nodes_before = sum(
            account.nodes
            for account in ledger.inventory()
            if account.role == "reverse_pair_q19_temporal_ring_bank"
        )
        ring = certificate.temporal_ring_bank(
            duration=1,
            positions=(0,),
            max_cells=128,
        )
        cells = ledger.counters[
            _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_CONSTRAINT_CELLS
        ]
        rounds = ledger.counters[
            _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_PROPAGATION_ROUNDS
        ]
        lane_visits = ledger.counters[
            _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_OUTPUT_LANE_VISITS
        ]
        assert cells > 0 and rounds > 0 and lane_visits > 0
        assert ring.retained_auxiliary_array_nodes == (
            sum(1 + len(row) for row in ring.center_domains)
            + len(ring.global_residues99)
            + len(ring.global_residues198)
        )
        ring_accounts = tuple(
            account
            for account in ledger.inventory()
            if account.role == "reverse_pair_q19_temporal_ring_bank"
        )
        assert len(ring_accounts) == 1
        assert (
            ring_accounts[0].nodes - ring_nodes_before
            >= ring.retained_auxiliary_array_nodes
        )

        ring.diagnostic()
        ring.harmonic(0, ReverseTemporalRingChannel.F5)
        ring.harmonic(0, DecimalPairBand.LT_HIGH)
        assert (
            ledger.counters[
                _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_CONSTRAINT_CELLS
            ]
            == cells
        )
        assert (
            ledger.counters[
                _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_PROPAGATION_ROUNDS
            ]
            == rounds
        )
        assert (
            ledger.counters[
                _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_OUTPUT_LANE_VISITS
            ]
            == lane_visits
        )

        with pytest.raises(ValueError, match="width tape"):
            certificate.temporal_ring_bank(
                duration=1,
                positions=(0,),
                max_cells=1,
            )
        assert (
            ledger.counters[_reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_FAILURES] == 1
        )
        assert (
            ledger.counters[
                _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_CONSTRAINT_CELLS
            ]
            == cells
        )
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_temporal_ring_marks_finite_horizon_and_center_refusals() -> None:
    from number_compiler.sequences.reverse_add.temporal_ring_harmonics import (
        ReverseTemporalRingRefused,
    )

    ledger, owner = owner_for(196)
    try:
        certificate = owner.certify_border_growth(
            owner.initial, steps=1, window_digits=1
        )
        with pytest.raises(ReverseTemporalRingRefused, match="horizon"):
            certificate.temporal_ring_bank(duration=2, positions=(0,))
        with pytest.raises(ReverseTemporalRingRefused, match="center"):
            certificate.temporal_ring_bank(duration=1, positions=(2,))
        assert (
            ledger.counters[_reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_FAILURES] == 2
        )
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_periodic_bank_cannot_bypass_wrong_certified_border_owner() -> None:
    """A different owner/certificate cannot supply conditional inlet authority."""
    from tests.support.reverse_add_banks import source_guarded_periodic_temporal_bank

    with source_guarded_periodic_temporal_bank() as (_ledger, _owner, _cert, bank):
        other_ledger, other_owner = owner_for(17071)
        try:
            other_cert = other_owner.certify_border_growth(
                other_owner.initial, steps=2, window_digits=1
            )
            with pytest.raises(ValueError):
                other_cert.temporal_ring_bank(positions=(0,), bank_action=bank)
        finally:
            other_owner.dispose()
            assert other_ledger.entries == other_ledger.nodes == 0


def test_universal_width_power_is_sparse_source_root_work_and_releases_scratch() -> (
    None
):
    from number_compiler.sequences.reverse_add.border_carry_safety import (
        BorderTile,
        border_bilateral_port,
    )
    from number_compiler.sequences.reverse_add.diagonal_growth_bank import (
        BorderWidthPowerRefused,
    )

    ledger, owner = owner_for(196)
    try:
        certificate = owner.certify_border_growth(
            owner.initial, steps=3, window_digits=1
        )
        tile = certificate.window_tiles[0]
        assert tile is not None

        # Independent short-horizon reference expands the finite universal
        # border alternatives directly; the production owner composes sparse
        # min/max relation powers instead.
        frontier = {tile: (0, 0)}
        for _ in range(3):
            next_frontier: dict[BorderTile, tuple[int, int]] = {}
            for source_tile, (low, high) in frontier.items():
                for edge in border_bilateral_port(source_tile).alternatives:
                    prior = next_frontier.get(edge.target)
                    candidate = low + edge.growth, high + edge.growth
                    next_frontier[edge.target] = (
                        candidate
                        if prior is None
                        else (min(prior[0], candidate[0]), max(prior[1], candidate[1]))
                    )
            frontier = next_frontier
        expected = (
            min(bounds[0] for bounds in frontier.values()),
            max(bounds[1] for bounds in frontier.values()),
        )

        baseline = ledger.entries, ledger.nodes
        bounds = certificate.universal_border_width_bounds(3)
        assert (bounds.min_growth, bounds.max_growth) == expected
        assert bounds.reachable_border_states == len(frontier)
        assert bounds.constructed_border_states >= 1
        assert bounds.relation_edges >= bounds.constructed_border_states - 1
        assert ledger.entries == baseline[0] and ledger.nodes == baseline[1]
        assert ledger.counters[_reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_STATES] >= 1
        assert (
            ledger.counters[_reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_STATE_VISITS]
            >= 1
        )

        no_op = certificate.universal_border_width_bounds(0)
        assert no_op.constructed_border_states == 0
        assert no_op.relation_edges == no_op.composition_pairs == 0
        assert ledger.entries == baseline[0] and ledger.nodes == baseline[1]

        with pytest.raises(BorderWidthPowerRefused):
            certificate.universal_border_width_bounds(2, max_edges=1)
        assert ledger.entries == baseline[0] and ledger.nodes == baseline[1]
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0
