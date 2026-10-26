"""Complete-future local Moore refinement and pointed temporal stencils."""

from __future__ import annotations

from dataclasses import replace
from inspect import signature
from itertools import product
from typing import cast

import pytest

from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.query_types import DoubleReverseTermQuery
from number_compiler.api.reverse_payloads import DoubleReverseTermPayload
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.stencil_moore import (
    DIGIT_STENCIL_MOORE,
    StencilOutput,
    minimize_digit_stencil,
    stencil_cell,
    stencil_from_ports,
)
from number_compiler.sequences.double_reverse.temporal_alternating_carry import (
    TwoStepCarryCell,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
    IssuedDoubleReverseSourcePrefix,
    source_prefix_binding,
)


def _literal(seed: int, physical_steps: int) -> int:
    for _ in range(physical_steps):
        seed = 2 * int(str(seed)[::-1])
    return seed


def test_moore_minimum_has_no_false_ltgt_or_f5_merges() -> None:
    expected: dict[StencilOutput, int] = {
        "digit": 10,
        "ltgt": 2,
        "f5": 5,
        "joint": 10,
    }
    for contract, initial in expected.items():
        machine = minimize_digit_stencil(contract)
        assert machine == DIGIT_STENCIL_MOORE[contract]
        assert machine.initial_classes == initial
        assert machine.state_count == 10
        assert machine.refinement_rounds == int(initial != 10)
        assert len(set(machine.classes)) == 10
        for a, b in product(range(10), repeat=2):
            if a == b:
                assert machine.classes[a] == machine.classes[b]
            else:
                assert machine.classes[a] != machine.classes[b]
            if machine.project(a) == machine.project(b) and a != b:
                witness = machine.separating_port(a, b)
                assert witness is not None
                left, right = witness
                assert machine.project(stencil_from_ports(left, a, right)) != (
                    machine.project(stencil_from_ports(left, b, right))
                )


def test_all_cell_and_two_step_transducer_ports_are_identical() -> None:
    for left, center, right in product(range(10), repeat=3):
        expected = (
            4 * center
            + 2 * int(left >= 5)
            + int((2 * right + int(center >= 5)) % 10 >= 5)
        ) % 10
        assert stencil_cell(left, center, right) == expected
        assert stencil_from_ports(int(left >= 5), center, right % 5) == expected
        right_carry = int((2 * (right % 5) + int(center >= 5)) % 10 >= 5)
        assert (
            TwoStepCarryCell.apply(center, int(left >= 5), right_carry).digit
            == expected
        )
    for high, center in product((0, 1), range(10)):
        sentinel_zero = TwoStepCarryCell.apply(center, high, 0).digit
        assert sentinel_zero == stencil_from_ports(high, center, 0)


@pytest.mark.parametrize("seed", (173488, 1768742, 4957342, 174388, 1763388))
@pytest.mark.parametrize("f_steps", (1, 2, 3, 4, 5, 7, 8, 13, 16, 31))
@pytest.mark.validation
def test_every_pointed_digit_matches_literally_powered_endpoint(
    seed: int, f_steps: int
) -> None:
    expected = str(_literal(seed, 2 * f_steps))
    with DoubleReverseTerm(seed, 2 * f_steps, max_steps=128) as term:
        engine = term.temporal_engine
        phase = engine.certify(term.source_root)
        assert phase is not None
        for index, character in enumerate(expected):
            point = engine.pointed_stencil(term.source_root, f_steps, phase, index)
            digit = int(character)
            assert point.width == len(expected)
            assert point.msd_index == index
            assert point.digit == digit
            assert point.ltgt == (digit >= 5)
            assert point.f5 == digit % 5
            assert point.moore_state == DIGIT_STENCIL_MOORE["joint"].classes[digit]
        assert term.published_image is None  # no full endpoint constructed


def test_public_digit_is_pointed_and_does_not_prepare_endpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(173488, 128) as term:

        def forbid_endpoint(_term: DoubleReverseTerm) -> None:
            raise AssertionError("a pointed digit query built the entire endpoint")

        monkeypatch.setattr(DoubleReverseTerm, "prepare_endpoint", forbid_endpoint)
        actual = _literal(173488, 128)
        for pos in (0, 1, 5, 20, len(str(actual)) - 1):
            assert term.digit(pos) == int(str(actual)[-pos - 1])
        assert term.published_image is None
        counters = term.metrics()
        assert counters["double_reverse_pointed_stencil_publications"] == 5
        assert counters.get("double_reverse_temporal_hashlife_publications", 0) == 0
        # The pointed cone and slice cache must pass the same payload audit.
        assert collect_ledger_metrics(term.resource_ledger).resource_audit_complete == 1


@pytest.mark.parametrize(
    ("coordinate", "exception"),
    ((-1, IndexError), (True, TypeError), (1.5, TypeError)),
)
def test_direct_and_projected_digits_reject_invalid_coordinates_before_work(
    coordinate: object,
    exception: type[Exception],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    projected = NumberCompiler(shared_cache=False).project(
        DoubleReverseTermQuery(64, seed=196)
    )
    assert isinstance(projected.payload, DoubleReverseTermPayload)
    term = projected.payload.term

    def forbid_construction(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("invalid digit coordinate triggered source construction")

    monkeypatch.setattr(
        DoubleReverseTerm, "_certified_prefix_entry", forbid_construction
    )
    monkeypatch.setattr(DoubleReverseTerm, "prepare_endpoint", forbid_construction)
    with term:
        for read_digit in (term.digit, projected.digit):
            with pytest.raises(exception):
                read_digit(cast("int", coordinate))
        assert term.published_image is None


def test_pointed_source_rejects_unknown_border_and_invalid_coordinate() -> None:
    with DoubleReverseTerm(0, 64) as term, pytest.raises(ValueError, match="certified"):
        term.pointed_stencil(0)
    with DoubleReverseTerm(173488, 64) as term, pytest.raises(IndexError):
        term.pointed_stencil(10_000)
    with (
        DoubleReverseTerm(173488, 1) as term,
        pytest.raises(ValueError, match="two generations"),
    ):
        term.pointed_stencil(0)
    with DoubleReverseTerm(173488, 63) as term:
        point = term.pointed_stencil(0)
        assert point.prefix_steps == 1
        assert point.digit == _literal(173488, 63) % 10


@pytest.mark.parametrize("seed,entry", ((196, 16), (12, 10), (4721, 9)))
def test_exact_transient_prefix_powers_196_and_other_cylinders(
    seed: int, entry: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    with DoubleReverseTerm(seed, 64) as term:

        def forbid_endpoint(_term: DoubleReverseTerm) -> None:
            raise AssertionError("stencil rebuilt whole endpoint")

        monkeypatch.setattr(DoubleReverseTerm, "prepare_endpoint", forbid_endpoint)
        point = term.pointed_stencil(0)
        # An odd prefix may be extended by one step to leave an even
        # remaining temporal clock; seed 4721 is the representative case.
        assert point.prefix_steps in (entry, entry + 1)
        assert point.digit == _literal(seed, 64) % 10
        assert term.digit(0) == point.digit
        assert term.published_image is None


@pytest.mark.parametrize("horizon", (16, 32, 64, 128))
def test_bounded_pointed_demands_share_prefix_without_endpoint(
    horizon: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    with DoubleReverseTerm(196, horizon, max_steps=128) as term:

        def forbid_endpoint(_term: DoubleReverseTerm) -> None:
            raise AssertionError("bounded stencil demand constructed the endpoint")

        monkeypatch.setattr(DoubleReverseTerm, "prepare_endpoint", forbid_endpoint)
        prefix, _ = term.temporal_border_bank()
        before = term.metrics()["double_reverse_pointed_border_entry_steps"]
        assert prefix == 16
        if horizon >= 32:
            expected = _literal(196, horizon)
            assert term.width() == len(str(expected))
            assert term.digit(0) == expected % 10
            assert term.digit(term.width() - 1) == int(str(expected)[0])
        after = term.metrics()["double_reverse_pointed_border_entry_steps"]
        assert before == after == 16
        assert term.published_image is None


@pytest.mark.validation
def test_seed196_generation64_pointed_and_full_work_counters(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    expected = _literal(196, 64)
    with DoubleReverseTerm(196, 64, max_steps=128) as pointed:

        def forbid_endpoint(_term: DoubleReverseTerm) -> None:
            raise AssertionError("pointed work constructed the complete endpoint")

        with monkeypatch.context() as guard:
            guard.setattr(DoubleReverseTerm, "prepare_endpoint", forbid_endpoint)
            assert pointed.width() == len(str(expected))
            assert pointed.digit(3) == (expected // 1_000) % 10
        pointed_metrics = pointed.metrics()
        assert pointed.published_image is None
        assert pointed_metrics["double_reverse_pointed_border_entry_steps"] == 16
        assert pointed_metrics["double_reverse_binary_shift_primitives"] == 16
        assert pointed_metrics["double_reverse_spatial_transducer_applications"] == 0
        assert pointed_metrics["double_reverse_pointed_stencil_publications"] == 1
        assert pointed_metrics["double_reverse_pointed_stencil_tiles"] > 0

    with DoubleReverseTerm(196, 64, max_steps=128) as materialized:
        assert materialized.materialize(max_bits=4096) == expected
        materialized_metrics = materialized.metrics()
        assert materialized.published_image is not None
        assert materialized_metrics["double_reverse_temporal_hashlife_publications"] > 0
        assert materialized_metrics["double_reverse_hashlife_tile_selections"] > 0


def test_source_prefix_seal_rejects_rewritten_cursor_and_binding() -> None:
    with DoubleReverseTerm(196, 64, max_steps=128) as term:
        term.temporal_border_bank()
        engine = term.temporal_engine
        entry = engine.source_prefix()
        issued = cast(
            IssuedDoubleReverseSourcePrefix | None,
            object.__getattribute__(engine, "_prefix_issued"),
        )
        assert entry is not None and issued is not None
        original_steps = entry.physical_steps
        original_binding = issued.binding
        try:
            object.__setattr__(entry, "physical_steps", original_steps + 1)
            object.__setattr__(issued, "binding", source_prefix_binding(entry))
            with pytest.raises(ValueError, match="stale"):
                engine.source_prefix()
        finally:
            object.__setattr__(entry, "physical_steps", original_steps)
            object.__setattr__(issued, "binding", original_binding)
        assert engine.source_prefix() == entry


def test_source_prefix_has_no_public_raw_integer_issuer() -> None:
    with DoubleReverseTerm(196, 64, max_steps=128) as term:
        term.temporal_border_bank()
        engine = term.temporal_engine
        entry = engine.source_prefix()
        assert entry is not None and entry.certified_phase is not None
        assert not hasattr(engine, "publish_source_prefix")
        assert engine.validate_source_prefix(entry) is entry

        forged_phase = replace(entry, certified_phase=(entry.certified_phase + 1) % 4)
        forged_source = replace(entry, source=entry.target)
        with pytest.raises(ValueError, match="owner-issued"):
            engine.validate_source_prefix(forged_phase)
        with pytest.raises(ValueError, match="owner-issued"):
            engine.validate_source_prefix(forged_source)

        with pytest.raises(TypeError):
            signature(engine.advance_source_prefix).bind(term.source_root)


def test_completed_endpoint_keeps_precedence_over_new_pointed_work() -> None:
    with DoubleReverseTerm(173488, 32) as term:
        term.materialize(max_bits=256)
        assert term.published_image is not None
        before = term.metrics()
        assert term.width() == len(str(_literal(173488, 32)))
        assert term.digit(0) == _literal(173488, 32) % 10
        after = term.metrics()
        assert after.get("double_reverse_pointed_border_entry_steps", 0) == before.get(
            "double_reverse_pointed_border_entry_steps", 0
        )
        assert after.get(
            "double_reverse_pointed_stencil_publications", 0
        ) == before.get("double_reverse_pointed_stencil_publications", 0)
