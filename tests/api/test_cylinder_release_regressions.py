"""Consumer, work-budget and semantic-identity regressions from the CLI audit."""

from __future__ import annotations

import json
from itertools import product
from typing import Never

import pytest

from number_compiler.api.cli import main
from number_compiler.arithmetic.polynomials.arithmetic_tile import (
    ArithmeticTile,
    ArithmeticTileSpec,
)
from number_compiler.arithmetic.polynomials.twisted_observer import (
    first_mirror_obstruction,
)
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.clock_observers import CollatzClockObservers
from number_compiler.sequences.collatz.power import CollatzEventArena


def forbidden(*args: object, **kwargs: object) -> Never:
    raise AssertionError("unrequested arithmetic work")


def test_no_factor_cli_does_not_collect_classical_gcd(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    from devtools.proofs.oracles import special_classical_ceiling as classical_ceiling

    monkeypatch.setattr(classical_ceiling, "_proper_gcd_packet", forbidden)
    assert main(["classify", "mersenne", "11"]) == 3
    assert capsys.readouterr().out == "unknown\n"


def test_factor_budget_prevents_power_and_cache_can_retry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
    from number_compiler.sequences.power_numbers import etale_factor

    compiler = CanonicalSequenceCompiler()
    with monkeypatch.context() as patch:
        patch.setattr(etale_factor, "_quadratic_power_pair", forbidden)
        result = compiler.resolve_special_theorem(
            "mersenne", 131, collect_etale_factor=True, max_factor_products=0
        )
        assert (
            not result.decided and result.factor_query_status == "product-budget-exceeded"
        )
        assert result.etale_ring_multiplications == 0
    result = compiler.resolve_special_theorem(
        "mersenne", 131, collect_etale_factor=True, max_factor_products=261
    )
    assert result.factor_witness == 263 and result.etale_ring_multiplications == 261


def test_large_exponent_gate_is_bounded(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    from number_compiler.sequences.power_numbers import numbers

    monkeypatch.setattr(numbers, "smallest_factor", forbidden)
    p = str((1 << 64) + 13)
    assert (
        main(["classify", "mersenne", p, "--max-candidate-bits", p, "--format", "json"])
        == 3
    )
    assert json.loads(capsys.readouterr().out)["method"] == "exponent-gate-budget"


def test_large_unresolved_candidate_has_no_classical_fallback(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    from devtools.proofs.oracles import classical_ceiling

    monkeypatch.setattr(classical_ceiling, "mersenne_classical_ceiling", forbidden)
    assert (
        main(
            [
                "classify",
                "mersenne",
                "20011",
                "--format",
                "json",
            ]
        )
        == 3
    )
    row = json.loads(capsys.readouterr().out)
    assert row["status"] == "unknown"
    assert "classical_budget_exceeded" not in row


@pytest.mark.parametrize(
    "kind", ["modular", "clock", "twisted", "hasse", "hensel", "tropical", "factor"]
)
def test_source_derived_observer_cli(
    kind: str, capsys: pytest.CaptureFixture[str]
) -> None:
    assert main(["observe", "collatz", "3", "--seed", "27", "--kind", kind]) == 0
    row = json.loads(capsys.readouterr().out)
    assert row["discovered_events"] == 3 and row["discovery_digit_work"] > 0
    if kind == "modular":
        assert row["value"] == {"upper": 27, "offset": 23, "lower": 16}
        assert (27 * 27 + 23) // 16 == 47
    if kind == "clock":
        assert row["value"]["physical_ticks"] == 7


def test_observer_cli_consumes_dispatch(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(CollatzClockObservers, "modular", forbidden)
    with pytest.raises(AssertionError, match="unrequested"):
        main(["observe", "collatz", "3", "--seed", "27", "--kind", "modular"])


def test_mirror_and_supplied_root_cli(capsys: pytest.CaptureFixture[str]) -> None:
    assert main(["observe", "196", "3"]) == 0
    row = json.loads(capsys.readouterr().out)
    assert row["palindrome"] is False and any(row["value"]["coefficients"])
    assert row["work_counters"]["tile_cylinder_node_evaluations"] > 0
    assert row["work_counters"].get("point_response_requests", 0) == 0
    assert row["peak_nodes"] >= row["retained_nodes"] > 0
    assert main(["observe", "mersenne", "11", "--defect", "621"]) == 0
    row = json.loads(capsys.readouterr().out)
    assert row["factor"] == 23 and "supplied" in row["scope"]
    assert main(["observe", "mersenne", "11", "--defect", "391"]) == 2
    capsys.readouterr()


def test_mirror_reads_target_at_most_once() -> None:
    calls = []

    def digit(i: int) -> int:
        calls.append(i)
        return 1

    assert first_mirror_obstruction(1024, digit) is None
    assert sorted(calls) == list(range(1024))


def test_two_tile_views_share_square(monkeypatch: pytest.MonkeyPatch) -> None:
    import number_compiler.arithmetic.polynomials.arithmetic_tile as owner

    tile = ArithmeticTile.from_value(ArithmeticTileSpec.mersenne(11), 621)
    tile.step_with_primary_carry_jet()
    monkeypatch.setattr(owner, "adaptive_square_convolution", forbidden)
    step, projection = tile.step_with_twisted_projection(width=11, sign=1)
    assert step.tile.residue == (621 * 621 - 2) % 2047
    assert projection.width == 11


def test_observer_cache_reuses_overlapping_demands() -> None:
    arena = CollatzEventArena()
    a = arena.from_valuations((1, 2, 1))
    observer = CollatzClockObservers(arena)
    first = observer.modular(a, 257)
    count = observer.node_evaluations
    assert observer.modular(a, 257) is first
    assert observer.node_evaluations == count
    observer.modular(a, 263)
    assert observer.node_evaluations > count


def test_event_association_identity_and_transport() -> None:
    for word in product((1, 2, 3), repeat=5):
        arena = CollatzEventArena()
        left = right = arena.identity
        for k in word:
            left = arena.concat(left, arena.event(k))
        for k in reversed(word):
            right = arena.concat(arena.event(k), right)
        assert left is right is arena.from_valuations(word)
        # Independent polynomial append, not an arena materialization oracle.
        upper, offset, lower = 1, 0, 1
        for k in word:
            upper, offset, lower = 3 * upper, 3 * offset + lower, lower * 2**k
        assert CollatzClockObservers(arena).modular(left, 257).offset == offset % 257


def test_huge_uniform_action_stays_shared() -> None:
    arena = CollatzEventArena()
    root = arena.power(arena.event(2), 10**100)
    assert root.effect.events == 10**100
    assert arena.node_count < 1000
    assert arena.cocycle_materializations == 0


def test_admitted_output_cap_skips_exact_width(monkeypatch: pytest.MonkeyPatch) -> None:
    term = PoweredCollatzTerm(27, 3)
    monkeypatch.setattr(PoweredCollatzTerm, "width", forbidden)
    assert term.materialize(max_bits=term.maximum_width) == 124


def test_tight_output_cap_still_rejects() -> None:
    with pytest.raises(ValueError):
        PoweredCollatzTerm(27, 3).materialize(max_bits=2)


def test_hard_composite_exponent_needs_no_full_factor_search(
    capsys: pytest.CaptureFixture[str],
) -> None:
    p = str(1000003 * 1000033)
    assert (
        main(
            [
                "classify",
                "mersenne",
                p,
                "--max-candidate-bits",
                p,
                "--factor",
                "--format",
                "json",
            ]
        )
        == 0
    )
    row = json.loads(capsys.readouterr().out)
    assert row["status"] == "composite" and row["factor_expression"] is None
    assert row["factor_query_status"] == "no-split"


def test_mirror_sheet_budget_precedes_allocation(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert main(["observe", "196", "3", "--width", "1000000000000"]) == 2
    assert "sheet exceeds digit budget" in capsys.readouterr().err


def test_prefix_does_not_claim_arrival_at_one(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert main(["observe", "collatz", "1", "--seed", "27"]) == 0
    assert json.loads(capsys.readouterr().out)["reached_one"] is False


@pytest.mark.parametrize("mutation", ("ports", "action", "wiring"))
def test_warm_point_rejects_mutated_issued_contract(mutation: str) -> None:
    term = PoweredCollatzTerm(27, 8)
    term.digit(0)
    lazy = term._point_index()._lazy_application
    assert lazy is not None
    application = lazy._open()
    if mutation == "ports":
        original = application.ports
        # bool aliases integer equality; tuple identity must still reject it.
        forged = tuple(bool(value) for value in original)
        object.__setattr__(application, "ports", forged)
        try:
            with pytest.raises((TypeError, ValueError)):
                term.digit(0)
        finally:
            object.__setattr__(application, "ports", original)
    else:
        target = application.action if mutation == "action" else application.wiring
        field = "local_id" if mutation == "action" else "phase"
        previous = getattr(target, field)
        object.__setattr__(target, field, previous + 1)
        try:
            with pytest.raises((TypeError, ValueError)):
                term.digit(0)
        finally:
            object.__setattr__(target, field, previous)
    term.digit(0)


def test_warm_point_and_inventory_reject_same_tile_lease_alias() -> None:
    from number_compiler.hashlife.execution.tile_application_authority import (
        audit_tile_application_registry,
    )

    term = PoweredCollatzTerm(27, 8)
    expected = term.digit(0)
    lazy = term._point_index()._lazy_application
    assert lazy is not None
    application = lazy._open()
    scheduler = application.scheduler
    with scheduler.application(
        application.action, application.source, application.ports, application.wiring
    ) as second:
        original = application._input._id
        object.__setattr__(application._input, "_id", second._input._id)
        try:
            with pytest.raises(ValueError):
                term.digit(0)
            _, invalid = audit_tile_application_registry(
                scheduler._applications, dict(term._ledger.iter_containers())
            )
            assert invalid
        finally:
            object.__setattr__(application._input, "_id", original)
    assert term.digit(0) == expected
