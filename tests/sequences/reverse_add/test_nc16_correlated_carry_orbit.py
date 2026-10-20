"""NC16 joint border-to-inner F5/carry action and phase correlation tests."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace
from itertools import product
from random import Random
from typing import cast
from unittest.mock import patch

import pytest

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    compose_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.border_carry_safety import (
    BorderTile,
    bilateral_cycle_letter,
)
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from number_compiler.sequences.reverse_add.temporal_carry_phase import (
    CertifiedCarryPhase,
)
from number_compiler.sequences.reverse_add.temporal_carry_wire import (
    restrict_middle_carry_wire,
)
from number_compiler.sequences.reverse_add.temporal_inward_constraints import (
    ReverseInwardConstraints,
)
from tests.support.private_attributes import private_test_attribute


def _successor(number: int) -> int:
    return number + int(str(number)[::-1])


def _source(n: int) -> int:
    x = 196
    for _ in range(n):
        x = _successor(x)
    return x


def _owner(value: int) -> tuple[ResourceLedger, ReversePairQ19OutputOwner]:
    ledger = ResourceLedger()
    return ledger, ReversePairQ19OutputOwner(ledger, digits_lsd(value, 10), base=10)


def _true_middle_map(source: int, k: int) -> CarryFn:
    digits = digits_lsd(source, 10)
    width = len(digits)
    output = CarryFn.ID
    for i in range(k, width - k):
        s = digits[i] + digits[width - 1 - i]
        output = compose_carry_fn(value_carry_fn(s, 10), output)
    return output


def test_first_reset_filter_projects_all_spatial_pair_domains() -> None:
    # Even width permits a true all-9 wire; an odd central coefficient
    # is even and necessarily destroys an EQ=9 wire.
    id_even = restrict_middle_carry_wire(6, 2, ((9,),), (CarryFn.ID,))
    assert id_even.transfers == (CarryFn.ID,)
    assert id_even.possible_first_resets == (-1,)
    with pytest.raises(ValueError):
        restrict_middle_carry_wire(7, 2, ((9,), (9,)), (CarryFn.ID,))
    # A mixed odd-center row is malformed input, not a request to silently
    # discard the odd coefficient and keep its even neighbor.
    with pytest.raises(ValueError, match="odd center domain"):
        restrict_middle_carry_wire(7, 2, ((9,), (2, 3)))
    with pytest.raises(ValueError):
        restrict_middle_carry_wire(7, 2, ((9,), (2, True)))

    # If only RESET0 is admitted and the candidate center is LT or GT,
    # EQ wire propagation must force the outer inner pair to EQ and the
    # center to LT, not simply invent a high=0 carry.
    lt = restrict_middle_carry_wire(7, 2, ((9, 13), (2, 14)), (CarryFn.CONST0,))
    assert lt.pair_domains == ((9,), (2,))
    assert lt.possible_first_resets == (1,)
    gt = restrict_middle_carry_wire(7, 2, ((9, 13), (2, 14)), (CarryFn.CONST1,))
    assert gt.pair_domains == ((9, 13), (2, 14))
    assert gt.possible_first_resets == (0, 1)
    assert gt.reset_witnesses == ((0, CarryFn.CONST1), (1, CarryFn.CONST1))


def test_first_reset_positions_remain_correlated_with_the_transfer() -> None:
    # Position 0 can only select RESET0; position 1 can only select RESET1.
    # The separate marginals are both {0,1}, which loses this distinction.
    wire = restrict_middle_carry_wire(
        6,
        1,
        ((8, 9), (9, 10)),
        (CarryFn.CONST0, CarryFn.CONST1),
    )
    assert wire.transfers == (CarryFn.CONST0, CarryFn.CONST1)
    assert wire.possible_first_resets == (0, 1)
    assert wire.reset_witnesses == (
        (0, CarryFn.CONST0),
        (1, CarryFn.CONST1),
    )

    # Admitting ID in the codomain is not evidence that an all-EQ seam is
    # present in these domains. The only actual assignment starts with 8.
    forced_reset = restrict_middle_carry_wire(6, 1, ((8,), (10,)), tuple(CarryFn))
    assert forced_reset.transfers == (CarryFn.CONST0,)
    assert forced_reset.reset_witnesses == ((0, CarryFn.CONST0),)
    assert forced_reset.possible_first_resets == (0,)


def test_finite_future_class_keeps_projected_f5_without_raw_domain_overrefinement() -> (
    None
):
    from number_compiler.sequences.reverse_add.temporal_ring_harmonics import (
        carry_phase_observation,
    )

    port = bilateral_cycle_letter(BorderTile(1, 1, 6), BorderTile(1, 7, 7), 0)
    base_wire = restrict_middle_carry_wire(6, 1, ((8,), (9,)), port.admitted_middle)
    base_phase = CertifiedCarryPhase(0, 6, port, base_wire)

    def phase(domains: tuple[tuple[int, ...], ...]) -> CertifiedCarryPhase:
        return replace(
            base_phase,
            middle_wire=replace(base_wire, pair_domains=domains),
        )

    left = carry_phase_observation((phase(((8,), (9,))),))
    different_f5 = carry_phase_observation((phase(((7,), (9,))),))
    same_f5 = carry_phase_observation((phase(((3,), (9,))),))
    assert left != different_f5
    assert left == same_f5


def test_exact_regular_projection_matches_bruteforce_small_middle_words() -> None:
    rng = Random(20261016)
    maps = (CarryFn.CONST0, CarryFn.ID, CarryFn.CONST1)
    for width in (5, 6, 7, 8, 9):
        k = 1
        center = (width + 1) // 2 - k
        for _ in range(90):
            domain_rows: list[tuple[int, ...]] = []
            for j in range(center):
                candidates = (
                    range(0, 19, 2) if width & 1 and j == center - 1 else range(19)
                )
                domain = tuple(s for s in candidates if rng.randrange(4) == 0)
                domain_rows.append(domain or (rng.choice(tuple(candidates)),))
            domains: tuple[tuple[int, ...], ...] = tuple(domain_rows)
            subset: tuple[CarryFn, ...] = tuple(fn for fn in maps if rng.randrange(2))
            if not subset:
                subset = (rng.choice(maps),)
            supported: set[CarryFn] = set()
            supported_coeffs: list[set[int]] = [set() for _ in range(center)]
            reset_witnesses: set[tuple[int, CarryFn]] = set()
            for values in product(*domains):
                if width & 1 and values[-1] % 2:
                    continue
                fn = CarryFn.ID
                for v in (
                    values + values[-2::-1] if width & 1 else values + values[::-1]
                ):
                    fn = compose_carry_fn(value_carry_fn(v, 10), fn)
                if fn in subset:
                    supported.add(fn)
                    for j, val in enumerate(values):
                        supported_coeffs[j].add(val)
                    reset = next(
                        (j for j, value in enumerate(values) if value != 9), None
                    )
                    if reset is None:
                        reset_witnesses.add((-1, CarryFn.ID))
                    else:
                        reset_witnesses.add(
                            (
                                reset,
                                CarryFn.CONST0 if values[reset] < 9 else CarryFn.CONST1,
                            )
                        )
            if not supported:
                with pytest.raises(ValueError):
                    restrict_middle_carry_wire(width, k, domains, subset)
            else:
                projection = restrict_middle_carry_wire(width, k, domains, subset)
                assert set(projection.transfers) == supported
                assert tuple(set(row) for row in projection.pair_domains) == tuple(
                    supported_coeffs
                )
                assert set(projection.reset_witnesses) == reset_witnesses


def test_source_port_is_same_carry_action_for_both_borders() -> None:
    rng = Random(691196)
    for _ in range(500):
        width = rng.randrange(5, 48)
        source = rng.randrange(10 ** (width - 1), 10**width)
        k = rng.randrange(1, min(6, (width - 1) // 2) + 1)
        n = _successor(source)
        b = 10**k
        tile = BorderTile(k, source // 10 ** (width - k), source % b)
        next_tile = BorderTile(k, n // 10 ** (len(str(n)) - k), n % b)
        port = bilateral_cycle_letter(tile, next_tile, len(str(n)) - width)
        correct_map = _true_middle_map(source, k)
        assert correct_map in port.admitted_middle
        d = digits_lsd(source, 10)
        sums = tuple(d[i] + d[width - 1 - i] for i in range(k, (width + 1) // 2))
        projection = restrict_middle_carry_wire(
            width, k, tuple((v,) for v in sums), port.admitted_middle
        )
        assert projection.transfers == (correct_map,)
        assert projection.input_output(port.low_carry) == (
            apply_carry_fn(correct_map, port.low_carry),
        )


def test_solver_excludes_invalid_inner_gt_or_eq_wire() -> None:
    # The first inner pair is {EQ, GT}, the second is {LT, GT}.
    # With a required RESET0, this forces EQ then LT.
    system = ReverseInwardConstraints((7, 7))
    system.constrain_pair(0, 2, (9, 13))
    system.constrain_pair(0, 3, (2, 14))
    system.constrain_middle_transfer(0, 2, (CarryFn.CONST0,))
    system.propagate()
    assert system.middle_transfer_domain(0, 2) == (CarryFn.CONST0,)
    assert system.pair_domain(0, 2) == (9,)
    assert system.pair_domain(0, 3) == (2,)
    assert system.middle_carry_wire(0, 2).possible_first_resets == (1,)


def test_middle_projection_reuses_only_unchanged_domains() -> None:
    visits = 0

    def count_visit() -> None:
        nonlocal visits
        visits += 1

    system = ReverseInwardConstraints((9, 9), on_middle_filter_visit=count_visit)
    system.constrain_middle_transfer(0, 1, tuple(CarryFn))
    recompute = cast(
        Callable[[], None], private_test_attribute(system, "_middle_constraints")
    )
    recompute()
    first_visits = visits
    assert first_visits > 0

    # The stored projection is a fixed point for identical pair domains and
    # transfer maps. Endpoint carries are still joined on every invocation.
    recompute()
    assert visits == first_visits

    current = system.pair_domain(0, 2)
    assert len(current) > 1
    system.constrain_pair(0, 2, current[0])
    recompute()
    assert visits > first_visits
    assert system.pair_domain(0, 2) == (current[0],)


def test_g79_ring_retains_two_sided_correlated_maps_with_no_q19_replay() -> None:
    x = _source(79)
    ledger, owner = _owner(x)
    try:
        with (
            patch.object(
                ReversePairQ19OutputOwner,
                "apply_pair_step",
                side_effect=AssertionError("physical Q19 step"),
            ),
            patch.object(
                ReversePairQ19OutputOwner,
                "apply_punctured_pair_block",
                side_effect=AssertionError("physical T4"),
            ),
        ):
            cert = owner.certify_border_growth(owner.initial, steps=9, window_digits=3)
            ring = cert.temporal_ring_bank(
                positions=(0, 1, 2, 3, 4, 5, 6, 7), source_pair_prefix=8
            )
            word = ring.conditional_carry_word()
            assert word.duration == 9 and word.growth == 4
            assert word.entry_border == word.exit_border
            assert ring.carry_wire_phases
            assert any(len(row) > 1 for row in ring.carry_wire_phases)
            assert word.exit_width == 42
            # A locally self-consistent copy is not a phase issued by this
            # ring bank, even though the live border certificate is shared.
            copied_phases = tuple(replace(phase) for phase in word.phases)
            with pytest.raises(ValueError, match="source-issued"):
                replace(word, phases=copied_phases)
            retained_phase = word.phases[0]
            retained_wire = retained_phase.middle_wire
            object.__setattr__(
                retained_phase, "middle_wire", replace(retained_wire, pair_domains=())
            )
            try:
                with pytest.raises(ValueError, match="altered"):
                    word.validate()
            finally:
                object.__setattr__(retained_phase, "middle_wire", retained_wire)
            word.validate()
            powers = word.conditional_power(10**12)
            assert powers.duration == 9 * 10**12
            assert powers.conditional_width() == 38 + 4 * 10**12
            assert not powers.physical_repeat_certified
            assert powers.phase(0).middle_transfers == word.phases[0].middle_transfers
            value = x
            for t in range(9):
                phase = word.phases[t]
                assert _true_middle_map(value, 1) in phase.middle_transfers
                assert (
                    len(str(_successor(value))) - len(str(value)) == phase.port.growth
                )
                value = _successor(value)
        first = cert.temporal_ring_bank(start=0, duration=4, positions=(0, 1))
        second = cert.temporal_ring_bank(start=4, duration=5, positions=(0, 1))
        joined = first.then(second)
        assert len(joined.carry_wire_phases) == 9
        assert joined.conditional_carry_word().growth == 4
        assert (
            first.conditional_carry_word().then(second.conditional_carry_word()).growth
            == 4
        )
        diag = ring.diagnostic()
        correlated = diag["correlated_carry_phases"]
        reset_ports = diag["middle_first_reset_ports"]
        assert type(correlated) is int and correlated >= 9
        assert isinstance(reset_ports, (tuple, list))
        reset_port_rows = cast(tuple[object, ...] | list[object], reset_ports)
        assert len(reset_port_rows) >= 9
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0
    with pytest.raises(ValueError):
        word.conditional_power(1)
    with pytest.raises(ValueError):
        word.validate()


def test_real_92_28_macro_exits_when_internal_reset_changes() -> None:
    for generation in (48, 50, 52, 54):
        x = _source(generation)
        ld, owner = _owner(x)
        try:
            ring = owner.authorize_temporal_ring_bank(
                owner.initial,
                steps=2,
                window_digits=3,
                positions=(0, 1, 2),
                include_source_digits=True,
            )
            word = ring.conditional_carry_word()
            assert word.growth == 1
            assert word.entry_border == word.exit_border
            assert any(phase.middle_transfers for phase in word.phases)
            next_val = _successor(_successor(x))
            if generation == 54:
                assert str(next_val).startswith("93")
                # K=2 is not falsely certified as the same border return.
                with pytest.raises(ValueError):
                    ring.conditional_carry_word(border_digits=2)
        finally:
            owner.dispose()
            assert ld.entries == ld.nodes == 0
