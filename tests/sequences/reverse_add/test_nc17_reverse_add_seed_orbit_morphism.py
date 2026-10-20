"""Pointed source-root reverse/add temporal composition and cyclotomic ports."""

from collections.abc import Generator
from contextlib import contextmanager
from copy import copy
from dataclasses import replace
from random import Random

import pytest

from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.reverse_add import (
    temporal_seed_morphism as _seed_morphism,
)
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from number_compiler.sequences.reverse_add.temporal_seed_morphism import (
    CertifiedReverseAddSeedMorphism,
    certified_completed_reverse_add_seed_morphism,
)
from tests.support.reverse_add_source_data import iterate_reverse_add as _literal


def _check(record: CertifiedReverseAddSeedMorphism, seed: int) -> int:
    record.validate()
    value = _literal(seed, record.last.generation)
    text = str(value)
    last = record.last
    assert last.width == len(text)
    assert last.residue99 == value % 99
    assert last.residue198 == value % 198
    assert "".join(str(record.digit_at(i)) for i in reversed(range(last.width))) == text
    s = (last.width - last.center_width) // 2
    centered = text[::-1][s : s + last.center_width][::-1]
    assert "".join(map(str, last.center)) == centered
    center_number = int(centered)
    assert last.exterior99 == (value - center_number * 10**s) % 99
    assert last.exterior198 == (value - center_number * 10**s) % 198
    # Reconstruct the *source* Q19 addition coefficients independently of
    # the target normalized digits, and check the NC16 correlated carry port.
    prior = str(_literal(seed, last.generation - 1))[::-1]
    pair = tuple(int(prior[i]) + int(prior[-i - 1]) for i in range(len(prior)))
    k = min(3, (len(pair) - 1) // 2)

    def carry(values: tuple[int, ...], initial: int) -> int:
        c = initial
        for coeff in values:
            c = (coeff + c) // 10
        return c

    assert last.border_pairs == k
    assert last.first_pair_sum == pair[0]
    assert last.low_border_carry == carry(pair[:k], 0)
    assert last.middle_carry_map == (
        carry(pair[k : len(pair) - k], 0),
        carry(pair[k : len(pair) - k], 1),
    )
    assert last.upper_border_ingress == carry(
        pair[k : len(pair) - k],
        last.low_border_carry,
    )
    assert last.first_non9_from_upper == next(
        (i for i in range(k, (len(pair) + 1) // 2) if pair[i] != 9), None
    )
    assert not record.logarithmic_q19_power_certified
    assert not record.physical_repeat_certified
    assert record.q19_block_applications >= 1
    return last.width


@contextmanager
def _term(seed: int, generation: int) -> Generator[ReverseAddPoweredTerm, None, None]:
    """Dispose per-test scheduler owners even when an assertion fails."""
    term = ReverseAddPoweredTerm(seed, generation)
    try:
        yield term
    finally:
        workspace = term.published_workspace
        if workspace is not None:
            workspace.dispose()
            if workspace.audit_snapshot().cleanup_complete:
                object.__setattr__(term, "_workspace", None)
                object.__setattr__(term, "_workspace_identity", None)
        if term.resource_ledger.entries or term.resource_ledger.nodes:
            raise AssertionError("reverse temporal test leaked ledger resources")


@pytest.mark.parametrize(
    ("seed", "exponent"),
    (
        (196, 0),
        (196, 1),
        (196, 3),
        (196, 6),
        (295, 2),
        (0, 4),
        (9, 5),
        (807, 2),
    ),
)
def test_source_root_square_independent_reference(seed: int, exponent: int) -> None:
    n = 1 + (1 << exponent)
    with _term(seed, n) as term:
        record = term.temporal_seed_orbit_morphism_power_of_two(exponent)
        assert record.physical_interval == (1, n)
        _check(record, seed)


def test_composition_and_next_true_intermediate_root() -> None:
    with _term(196, 33) as term:
        first = term.temporal_seed_orbit_morphism(2)
        latter = term.temporal_seed_orbit_morphism(3, start=3)
        combined = first.then(latter)
        assert combined.physical_interval == (1, 6)
        _check(combined, 196)
        p = term.temporal_seed_orbit_morphism(1)
        for _ in range(5):
            p = p.square()
        assert p.physical_interval == (1, 33)
        _check(p, 196)
        assert p.q19_block_applications == 10


def test_cross_owner_gap_and_mutation_refused() -> None:
    with _term(196, 16) as a, _term(196, 16) as b:
        block = a.temporal_seed_orbit_morphism(2)
        other = b.temporal_seed_orbit_morphism(2, start=3)
        with pytest.raises(ValueError, match="not issued"):
            copy(block).validate()
        with pytest.raises(ValueError):
            block.then(other)
        with pytest.raises(ValueError):
            block.then(a.temporal_seed_orbit_morphism(1, start=5))
        with pytest.raises(ValueError):
            replace(block).validate()
        seal = object.__getattribute__(block, "_seal")
        object.__setattr__(block, "_seal", object())
        with pytest.raises(ValueError):
            block.validate()
        object.__setattr__(block, "_seal", seal)
        block.validate()
        untouched = block.q19_block_applications
        object.__setattr__(block, "q19_block_applications", -1)
        with pytest.raises(ValueError):
            block.validate()
        object.__setattr__(block, "q19_block_applications", untouched)
        block.validate()
        real_center = block.last.center
        object.__setattr__(block.last, "center", (4,))
        with pytest.raises(ValueError):
            block.validate()
        object.__setattr__(block.last, "center", real_center)
        block.validate()


def test_source_interval_bounds_and_no_fast_claim() -> None:
    with _term(196, 9) as term:
        for kwargs in (
            {"start": 0, "steps": 1},
            {"start": 1, "steps": 0},
            {"start": 9, "steps": 1},
        ):
            with pytest.raises(ValueError):
                term.temporal_seed_orbit_morphism(**kwargs)
        with pytest.raises(ValueError):
            term.temporal_seed_orbit_morphism_power_of_two(6)
        with pytest.raises(ValueError):
            term.temporal_seed_orbit_morphism_power_of_two(25)


def test_disposed_q19_owner_invalidates_returned_morphism() -> None:
    with _term(196, 4) as term:
        record = term.temporal_seed_orbit_morphism(1)
        term.source_workspace().dispose()
        with pytest.raises(ValueError, match="disposed Q19"):
            record.validate()


def test_seed_morphism_reuses_endpoint_after_stream_demand(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with _term(196, 17) as term:
        expected = tuple(term.iter_digits())
        workspace = term.source_workspace()
        owner = workspace.adapter.audit_snapshot().q19_owner
        image = workspace.audit_snapshot().image
        assert owner is not None and image is not None
        view = workspace.scheduler.source_image_core().view(image)
        payload = workspace.adapter.validate_view(view)
        endpoint = payload.pair_output
        assert endpoint is not None
        before = workspace.ledger.snapshot().counters

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("warm observer reapplied a Q19 temporal block")

        monkeypatch.setattr(ReversePairQ19OutputOwner, "apply_pair_step", forbidden)
        monkeypatch.setattr(
            ReversePairQ19OutputOwner, "apply_punctured_pair_block", forbidden
        )
        record = certified_completed_reverse_add_seed_morphism(term)
        after = workspace.ledger.snapshot().counters
        assert record.last.occurrence is endpoint
        assert record.terminal_occurrence_reused
        assert record.q19_block_applications == 0
        temporal_keys = (
            "reverse_q19_primitive_pair_applications",
            "reverse_q19_punctured_t2_applications",
            "reverse_q19_punctured_t4_applications",
        )
        assert all(after.get(key, 0) == before.get(key, 0) for key in temporal_keys)
        assert tuple(term.iter_digits()) == expected


def test_seed_morphism_first_shares_endpoint_with_later_stream(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with _term(196, 17) as term:
        record = certified_completed_reverse_add_seed_morphism(term)
        workspace = term.source_workspace()
        assert not record.terminal_occurrence_reused
        assert record.q19_block_applications > 0
        before = workspace.ledger.snapshot().counters

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("stream demand rebuilt the published Q19 endpoint")

        monkeypatch.setattr(ReversePairQ19OutputOwner, "apply_pair_step", forbidden)
        monkeypatch.setattr(
            ReversePairQ19OutputOwner, "apply_punctured_pair_block", forbidden
        )
        assert tuple(term.iter_digits()) == tuple(
            int(digit) for digit in str(_literal(196, 17))[::-1]
        )
        after = workspace.ledger.snapshot().counters
        temporal_keys = (
            "reverse_q19_primitive_pair_applications",
            "reverse_q19_punctured_t2_applications",
            "reverse_q19_punctured_t4_applications",
        )
        assert all(after.get(key, 0) == before.get(key, 0) for key in temporal_keys)


def test_repeated_completed_demand_reuses_exact_word_fiber_projection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with _term(196, 17) as term:
        first = certified_completed_reverse_add_seed_morphism(term)
        workspace = term.source_workspace()
        before = workspace.ledger.snapshot().counters
        payload = audit_registered_payloads(workspace.ledger)
        assert (payload.forbidden_future_payloads, payload.unknown_payloads) == (0, 0)
        assert before[_reverse_add_keys.REVERSE_Q19_WORD_FIBER_DAG_NODES_VISITED] > 0
        assert (
            before[_reverse_add_keys.REVERSE_Q19_WORD_FIBER_INTERVAL_NODES_VISITED] > 0
        )

        def forbid_refold(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("warm fiber demand refolded the Q19 output SLP")

        monkeypatch.setattr(_seed_morphism, "fold_slp_dag", forbid_refold)
        monkeypatch.setattr(_seed_morphism, "fold_slp_interval", forbid_refold)
        second = certified_completed_reverse_add_seed_morphism(term)
        after = workspace.ledger.snapshot().counters

        assert second.first is first.first
        assert second.last is first.last
        assert (
            after[_reverse_add_keys.REVERSE_Q19_WORD_FIBER_CACHE_HITS]
            == before.get(_reverse_add_keys.REVERSE_Q19_WORD_FIBER_CACHE_HITS, 0) + 2
        )
        for key in (
            _reverse_add_keys.REVERSE_Q19_WORD_FIBER_DAG_NODES_VISITED,
            _reverse_add_keys.REVERSE_Q19_WORD_FIBER_INTERVAL_NODES_VISITED,
        ):
            assert after[key] == before[key]


def test_independent_outer_carry_witnesses_are_not_a_radius_one_stencil() -> None:
    left = int("8" + "4" * 9 + "5" * 9 + "0")
    right = left + 2
    assert str(left)[4:16] == str(right)[4:16]
    a, b = _literal(left, 1), _literal(right, 1)
    assert (
        str(a)[len(str(a)) // 2 - 2 : len(str(a)) // 2 + 2]
        != str(b)[len(str(b)) // 2 - 2 : len(str(b)) // 2 + 2]
    )
    for seed, _target in [(left, a), (right, b)]:
        with _term(seed, 2) as term:
            obs = term.temporal_seed_orbit_morphism(1)
            _check(obs, seed)


def test_no_scalar_replay_or_integer_materialization(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("scalar/materialization path must not be selected")

    monkeypatch.setattr(ReverseAddPoweredTerm, "materialize", forbidden)
    monkeypatch.setattr(ReverseAddPoweredTerm, "iter_digits", forbidden)
    with _term(196, 65) as term:
        record = term.temporal_seed_orbit_morphism_power_of_two(6)
        assert record.physical_interval == (1, 65)
        _check(record, 196)


def test_random_source_and_offset_port_differentials() -> None:
    rng = Random(6196)
    for _ in range(6):
        seed = rng.randrange(1, 10**10)
        start = rng.randrange(1, 9)
        steps = rng.randrange(1, 7)
        with _term(seed, start + steps) as term:
            record = term.temporal_seed_orbit_morphism(steps, start=start)
            _check(record, seed)
