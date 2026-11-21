"""Independent checks for the source-closed mixed-adic 2rev10 consumer."""

from __future__ import annotations

import json
import random

import pytest
from pytest import CaptureFixture

from number_compiler.api.cli import main
from number_compiler.api.json_output import is_object_sequence, is_string_object_mapping
from number_compiler.api.number_api import NumberCompiler, ProjectedNumberTerm
from number_compiler.api.query_types import TermQuery
from number_compiler.sequences.double_reverse.boundary_cycles import (
    CANDIDATE_COMPONENTS,
)
from number_compiler.sequences.double_reverse.temporal_mixed_adic_consumer import (
    MixedAdicState,
    certified_edge_action,
    certified_mixed_adic_packet,
    source_entry,
)
from tests.support.observation_views import view_value


def physical_next(x: int) -> int:
    return 2 * int(str(x)[::-1])


def field_orientations(x: int) -> dict[str, int]:
    high = "".join(str(2 * int(c)) for c in str(x))
    low = "".join(str(2 * int(c)) for c in str(x)[::-1])
    return {
        "high_first_mod90": int(high) % 90,
        "low_first_mod90": int(low) % 90,
        "reverse_characters_of_high_first_mod90": int(high[::-1]) % 90,
        "reverse_characters_of_low_first_mod90": int(low[::-1]) % 90,
    }


def test_nine_edge_closure_is_an_exhaustive_induction() -> None:
    rows = certified_edge_action()
    assert len(rows) == len(CANDIDATE_COMPONENTS[0]) == 9
    assert all(1 <= len(row) <= 2 for row in rows)
    entry = source_entry(196)
    assert entry is not None and entry.generation == 16


def test_four_step_multiplication_is_exact_on_every_semantic_class() -> None:
    for phase in range(4):
        for parity in (0, 1):
            for r99 in range(99):
                state = MixedAdicState(phase, parity, r99)
                actual = state
                for _ in range(4):
                    actual = actual.successor()
                assert state.power(4) == actual
                period = state.primitive_period
                assert period % 4 == 0 and period <= 120
                assert state.power(period) == state
                if r99 == 0:
                    assert period == 4
                assert actual.residue99 == 160 * r99 % 99
                assert actual.width_parity == (None if r99 % 11 == 0 else parity)
                assert actual.phase == phase
                assert state.field.residue == 2 * state.residue1980 % 18
                assert (
                    state.power(72).field.four_field_orientations_mod90
                    == state.field.four_field_orientations_mod90
                )
                assert (
                    state.power(576).field.four_field_orientations_mod90
                    == state.field.four_field_orientations_mod90
                )


def test_all_guarded_fields_have_distinct_mod90_orientations() -> None:
    projections = {
        tuple(
            MixedAdicState(
                phase, 0, residue
            ).field.four_field_orientations_mod90.values()
        )
        for phase in range(4)
        for residue in range(9)
    }
    assert len(projections) == 36


def test_binary_power_composes_without_physical_occurrences() -> None:
    rng = random.Random(169)
    for _ in range(200):
        state = MixedAdicState(rng.randrange(4), rng.randrange(2), rng.randrange(99))
        a, b = rng.randrange(10**20), rng.randrange(10**20)
        assert state.power(a).power(b) == state.power(a + b)
        assert state.power(1) == state.successor()


@pytest.mark.parametrize("seed", [196, 17068, 17442, 17888, 48042, 49068, 49888])
def test_actual_source_orbit_and_both_field_orientations(seed: int) -> None:
    x = seed
    for n in range(230):
        packet = certified_mixed_adic_packet(seed, n)
        if packet["status"] == "available":
            assert packet["physical_residue1980"] == x % 1980, (seed, n)
            candidates = packet["physical_mod9900_candidates"]
            assert is_object_sequence(candidates)
            assert x % 9900 in candidates, (seed, n)
            field = packet["field_mod18_mod90"]
            assert is_string_object_mapping(field)
            assert field["four_field_orientations_mod90"] == field_orientations(x)
            assert packet["physical_post_entry_steps"] == 0
            assert packet["cross_precision_projection_mod9900_to_mod1980"]
        x = physical_next(x)


def test_period_72_576_not_forged_for_the_mixed_prime_quotient() -> None:
    packet = certified_mixed_adic_packet(196, 16)
    assert packet["physical_residue1980"] == 1228
    assert packet["primitive_period_mod1980_and_phase"] == 120
    samples = packet["period_72_576_consumer"]
    assert is_object_sequence(samples)
    for sample in samples:
        assert is_string_object_mapping(sample)
        assert sample["duration"] in (72, 576)
        assert sample["field_mod18_mod90_and_outer_carry_return"]
        assert sample["mixed_mod1980_return"] is False
        assert sample["physical_mod99_return"] is False
        assert sample["physical_full_carry_vector_period_certified"] is False
        for prime, minimum in ((2, 2), (5, 1)):
            valuation = sample[f"return_{prime}_adic"]
            assert is_string_object_mapping(valuation)
            assert valuation["at_least"] == minimum


def test_large_index_returns_with_no_post_entry_source_work() -> None:
    n = 10**100
    packet = certified_mixed_adic_packet(196, n)
    assert packet["physical_post_entry_steps"] == 0
    assert packet["physical_admission_steps"] == 16
    assert packet["full_endpoint_materialized"] is False
    assert packet["nine_edge_induction_checked"] == 9
    entry = source_entry(196)
    assert entry is not None
    state = MixedAdicState(entry.phase, entry.width_parity, entry.residue99)
    assert state.power(n - 16).residue1980 == packet["physical_residue1980"]
    classes = packet["edge_powerset_reachable_class_count"]
    assert isinstance(classes, int) and classes <= 512


def test_source_admission_respects_request_budgets() -> None:
    assert certified_mixed_adic_packet(196, 16, max_steps=15)["status"] == "unavailable"
    assert (
        certified_mixed_adic_packet(196, 16, max_state_bits=8)["status"]
        == "unavailable"
    )
    assert (
        certified_mixed_adic_packet(196, 16, max_steps=16)["physical_admission_steps"]
        == 16
    )


def test_mixed_adic_cli_must_not_project_full_term(
    monkeypatch: pytest.MonkeyPatch, capsys: CaptureFixture[str]
) -> None:
    def forbidden(query: TermQuery) -> ProjectedNumberTerm:
        raise AssertionError(
            "guarded mixed-adic observer touched physical source engine"
        )

    monkeypatch.setattr(NumberCompiler, "project", forbidden)
    assert (
        main(
            [
                "2rev10",
                "--seed",
                "196",
                "--nth-power10",
                "80",
                "--no-value",
                "--info",
                "arithmetic.modular",
                "--arithmetic-modular-kind",
                "mixed-adic",
                "--format",
                "json",
            ],
            shared_cache=False,
        )
        == 0
    )
    obj = json.loads(capsys.readouterr().out)
    data = view_value(obj["info"]["arithmetic.modular"], "mixed-adic")
    assert data["status"] == "available"
    assert data["temporal_powered_without_source_scheduler"] is True
    assert data["full_endpoint_materialized"] is False
    assert obj["value"] is None


def test_mix_does_not_replace_existing_seed_morphism(
    capsys: CaptureFixture[str],
) -> None:
    # A combined request must still build the real source for the explicitly
    # demanded full-word seed morphism; the fast observer cannot authorize it.
    assert (
        main(
            [
                "2rev10",
                "--seed",
                "196",
                "--nth",
                "40",
                "--no-value",
                "--info",
                "arithmetic.modular",
                "--arithmetic-modular-kind",
                "mixed-adic",
                "--info",
                "temporal.closed-form",
                "--temporal-closed-form-kind",
                "source-action",
                "--info",
                "temporal.accumulator",
                "--format",
                "json",
            ],
            shared_cache=False,
        )
        == 0
    )
    obj = json.loads(capsys.readouterr().out)
    data = view_value(obj["info"]["arithmetic.modular"], "mixed-adic")
    assert data["physical_residue1980"] == 508
    assert "target_normalized_mod198" in view_value(
        obj["info"]["temporal.accumulator"], "alternating"
    )


def test_five_digit_field225_survives_two_reverse_cutover(
    monkeypatch: pytest.MonkeyPatch, capsys: CaptureFixture[str]
) -> None:
    def forbidden(query: TermQuery) -> ProjectedNumberTerm:
        raise AssertionError("5rev10 mod225 projected a physical source")

    monkeypatch.setattr(NumberCompiler, "project", forbidden)
    assert (
        main(
            [
                "5rev10",
                "--seed",
                "196",
                "--nth-power10",
                "45",
                "--no-value",
                "--info",
                "arithmetic.modular",
                "--arithmetic-modular-kind",
                "digit-field",
                "--arithmetic-modular-places",
                "2",
                "--format",
                "json",
            ],
            shared_cache=False,
        )
        == 0
    )
    obj = json.loads(capsys.readouterr().out)
    packet = view_value(obj["info"]["arithmetic.modular"], "digit-field")
    assert packet["source_occurrences_materialized"] is False
    assert packet["field_residue"] == 80 * pow(5, 10**45, 225) % 225


def test_exact_756_class_moore_minimization() -> None:
    raw = [MixedAdicState(p, w, r) for p in range(4) for w in (0, 1) for r in range(99)]
    assert len(raw) == 792
    assert len(set(raw)) == 756
    # Equivalence is exactly the 36 pairwise width-parity merges where 11|r.
    for p in range(4):
        for r in range(99):
            a, b = MixedAdicState(p, 0, r), MixedAdicState(p, 1, r)
            assert (a == b) == (r % 11 == 0)
            assert a.residue1980 == b.residue1980
            if r % 11:
                assert a.successor().residue1980 != b.successor().residue1980
            else:
                assert a.power(10**80) == b.power(10**80)
    # Current outputs distinguish distinct residues; the first future output
    # separates all four phases, including the mod-20 collisions 0/3 and 1/2.
    for p in range(4):
        for q in range(p + 1, 4):
            s, t = MixedAdicState(p, 1, 1), MixedAdicState(q, 1, 1)
            assert (s.residue1980, s.successor().residue1980) != (
                t.residue1980,
                t.successor().residue1980,
            )
