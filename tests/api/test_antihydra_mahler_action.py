"""Independent bounded consumer checks, distinct from a non-halting proof."""

import subprocess
import sys
from fractions import Fraction
from dataclasses import fields

import pytest

from number_compiler.api.antihydra_observation import observe_run
from number_compiler.api.number_api import NumberCompiler
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicAggregateSummary,
)
from number_compiler.sequences.antihydra import runtime
from number_compiler.sequences.antihydra.mahler import tangent
from number_compiler.sequences.antihydra.mahler_action import associated_action
from number_compiler.sequences.antihydra.arithmetic_images import (
    AntihydraArithmeticImageWorkspace,
)
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm, run


@pytest.mark.parametrize("kind", ("clock", "hensel"))
def test_unrequested_mahler_module_is_not_imported(kind: str) -> None:
    code = """
import sys
sys.modules['number_compiler.sequences.antihydra.mahler_action'] = None
from number_compiler.api.cli import main
raise SystemExit(main(sys.argv[1:]))
"""
    result = subprocess.run(
        [sys.executable, "-c", code, "antihydra", "--nth", "2", "--info", kind],
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout == "18\n"


def _rational(value: object) -> Fraction:
    assert isinstance(value, dict)
    numerator, denominator = value["numerator"], value["denominator"]
    assert type(numerator) is int and type(denominator) is int
    return Fraction(numerator, denominator)


def test_arithmetic_mahler_and_hensel_do_not_construct_physical_roof(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = AntihydraArithmeticTerm(64)
    result = term.result()

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("arithmetic Mahler observation requested a physical roof")

    monkeypatch.setattr(runtime, "physical_roof", forbidden)
    hensel = tangent(result, 8)
    action = associated_action(result)
    mahler = dict(hensel)
    mahler["associated_action"] = action

    assert action["source_binding"] == result.source_binding
    assert mahler["timestamp_macro_returns"] == result.returns
    assert hensel["consumed_centered_odd_events"] == result.odd_events
    assert not term.physical_publications
    assert term.ledger.counters.get("physical_roof_evaluations", 0) == 0
    assert term.ledger.counters.get("physical_roof_construction_requests", 0) == 0


def test_mahler_consumes_the_composed_source_image_without_refolding_segments() -> None:
    term = AntihydraArithmeticTerm(1024)
    result = term.result()
    packet = associated_action(result)
    workspace = term.arithmetic_workspace
    assert workspace is not None
    transfer = workspace.summary().transfer
    assert _rational(packet["scale"]) == Fraction(transfer.upper, transfer.lower)
    assert _rational(packet["offset"]) == -3 * Fraction(
        transfer.upper + transfer.offset - transfer.lower, transfer.lower
    )
    assert term.ledger.counters.get("mahler_source_cylinder_compositions", 0) == 0
    assert term.ledger.counters["mahler_source_composed_image_reads"] == 1


def test_antihydra_and_mahler_consume_the_shared_saturated_publication(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = AntihydraArithmeticImageWorkspace.saturated_summary
    published: list[DyadicAggregateSummary] = []

    def counted(workspace: AntihydraArithmeticImageWorkspace) -> DyadicAggregateSummary:
        value = original(workspace)
        published.append(value)
        return value

    monkeypatch.setattr(AntihydraArithmeticImageWorkspace, "saturated_summary", counted)
    term = AntihydraArithmeticTerm(65)
    result = term.result()
    assert published and published[-1].width == 65
    prior = len(published)
    action = associated_action(result)
    assert len(published) > prior
    assert action["extent"] == 65
    assert action["first_failure"] == 2
    assert result.first_failure_index is None
    assert {field.name for field in fields(DyadicAggregateSummary)}.isdisjoint(
        {"support", "children", "history", "branch_word", "valuations"}
    )
    assert term.ledger.counters["source_image_adapter_registrations"] == 1
    assert not term._segments_ready and not term.physical_publications


def test_plain_digits_and_mahler_do_not_materialize_segments(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(
        _workspace: AntihydraArithmeticImageWorkspace,
    ) -> None:
        raise AssertionError("unrequested Antihydra segments were materialized")

    monkeypatch.setattr(AntihydraArithmeticImageWorkspace, "segments", forbidden)
    term = AntihydraArithmeticTerm(64)
    result = term.result()
    assert result.h > 8
    assert NumberCompiler().nth("antihydra", 64) == result.h
    assert associated_action(result)["extent"] == 64
    assert not term._segments and not term._segments_ready
    assert term.metrics()["retained_source_blocks"] == 0
    report = audit_registered_payloads(term.ledger)
    assert report.forbidden_future_payloads == report.unknown_payloads == 0
    assert term.ledger.counters.get("arithmetic_block_applications", 0) == 0


def test_halted_physical_adapter_does_not_relabel_total_arithmetic_extent() -> None:
    term = AntihydraArithmeticTerm(0)
    arithmetic = term.result()
    halted = object.__new__(runtime.Run)
    values = {
        "requested": 0,
        "returns": 0,
        "h": 8,
        "balance": -1,
        "minimum": -1,
        "left": 5,
        "right": 6,
        "halted": True,
        "ledger": term.ledger,
        "_engine": term.engine,
        "_term": term,
        "_source": runtime._SOURCE,
    }
    for name, value in values.items():
        object.__setattr__(halted, name, value)
    publication = runtime._PhysicalPublication(
        halted,
        halted.requested,
        halted.returns,
        halted.h,
        halted.balance,
        halted.minimum,
        halted.left,
        halted.right,
        halted.halted,
    )
    term.ledger.reserve(term.physical_owner, entries=1, nodes=2)
    term.physical_publications.append(publication)
    halted.require_source()

    with pytest.raises(ValueError, match="halted source"):
        tangent(halted, 8)
    with pytest.raises(ValueError, match="halted source"):
        associated_action(halted)
    assert tangent(arithmetic, 8)["timestamp_macro_returns"] == 0


@pytest.mark.parametrize("extent", (0, 1, 2, 3, 7, 8, 15, 16, 63, 64, 65, 128))
def test_mahler_action_matches_independent_finite_source(extent: int) -> None:
    result = run(extent)
    packet = observe_run(result, kind="mahler")["value"]["associated_action"]
    h = 8
    scale, offset = Fraction(1), Fraction(0)
    cap: Fraction | None = None
    first_failure: int | None = None
    for index in range(extent):
        bit = (h - 1) & 1
        scale *= Fraction(3, 2)
        offset = Fraction(3, 2) * offset - Fraction(3 * bit, 2)
        roof = Fraction(3, 4) if bit else Fraction(9, 4)
        cap = (
            roof
            if cap is None
            else min(roof, Fraction(3, 2) * cap - Fraction(3 * bit, 2))
        )
        if first_failure is None and cap <= 0:
            first_failure = index + 1
        h += h // 2
    assert packet["source_binding"] == result.source_binding
    assert packet["extent"] == extent
    assert packet["bit_convention"] == "parity_of_centered_D_equals_a_minus_one"
    assert _rational(packet["scale"]) == scale
    assert _rational(packet["offset"]) == offset
    assert packet["cap"] is None if cap is None else _rational(packet["cap"]) == cap
    assert packet["first_failure"] == first_failure
    assert packet["first_failure_index_unit"] == "one_based_macro_return"
    assert packet["all_time_claim"] is False


def test_mahler_demand_reuses_source_support(monkeypatch: pytest.MonkeyPatch) -> None:
    term = AntihydraArithmeticTerm(64)
    result = term.result()

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("Mahler consumer rediscovered source arithmetic")

    monkeypatch.setattr(term.engine, "arithmetic_cylinder", forbidden)
    first = associated_action(result)
    second = associated_action(result)
    assert first == second
    assert term.ledger.counters["mahler_source_composed_image_reads"] == 1
    assert term.ledger.counters["source_image_projection_hits"] >= 1


def test_mahler_uses_arithmetic_scheduler_without_second_action_arena(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields import consumer_pullback

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("Mahler rebuilt a second action arena")

    monkeypatch.setattr(consumer_pullback.AssociatedActionArena, "__init__", forbidden)
    term = AntihydraArithmeticTerm(64)
    result = term.result()
    assert associated_action(result)["first_failure"] == 2
    assert term.mahler_workspace is not None
    assert term.mahler_workspace.source_workspace is term.arithmetic_workspace


def test_mahler_rejects_tampered_cached_source_projection() -> None:
    from number_compiler.hashlife.execution.source_bound_images import (
        SourceImageDemand,
    )

    term = AntihydraArithmeticTerm(8)
    result = term.result()
    associated_action(result)
    source = term.arithmetic_workspace
    assert source is not None
    projection = source.scheduler.source_projection(
        source, source.root_image, SourceImageDemand("mahler-associated-action")
    )
    object.__setattr__(projection.value, "cap", None)
    with pytest.raises(ValueError, match="projection record was altered"):
        associated_action(result)


def test_mahler_consumer_does_not_transfer_ledger_safety() -> None:
    # The actual source begins with centered bits 11.  Its ledger is +4,
    # whereas the Mahler cap is 3/2 * 3/4 - 3/2 = -3/8.
    result = run(2)
    packet = observe_run(result, kind="mahler")["value"]["associated_action"]
    assert result.balance == 4 and not result.halted
    assert packet["first_failure"] == 2
    assert _rational(packet["cap"]) == Fraction(-3, 8)


def test_mahler_rejected_publication_releases_its_stores() -> None:
    term = AntihydraArithmeticTerm(64)
    result = term.result()
    ledger = result.ledger
    before = ledger.entries, ledger.nodes
    limit = ledger.max_cache_entries
    ledger.max_cache_entries = ledger.entries
    with pytest.raises(BlockContextBudgetExceeded):
        associated_action(result)
    assert (ledger.entries, ledger.nodes) == before
    assert term.mahler_workspace is None
    ledger.max_cache_entries = limit
    assert associated_action(result)["first_failure"] == 2


def test_mahler_rejects_foreign_occurrence_workspace() -> None:
    first, second = run(16), run(16)
    associated_action(first)
    second._term.mahler_workspace = first._term.mahler_workspace
    with pytest.raises(ValueError, match="another source occurrence"):
        associated_action(second)


@pytest.mark.parametrize("returns", (0, 1, 2, 8, 64))
def test_root_shell_is_source_bound_exact_squared_coordinate(returns: int) -> None:
    term = AntihydraArithmeticTerm(returns)
    result = term.result()
    packet = associated_action(result)
    root = packet["root_shell"]
    assert isinstance(root, dict)
    # Independent bounded source trajectory, used only as a test oracle.
    d, scale, offset = 7, Fraction(1), Fraction(0)
    lower, upper = Fraction(0), Fraction(1)
    for _ in range(returns):
        parity = d % 2
        scale *= Fraction(3, 2)
        offset = Fraction(3, 2) * offset - parity
        lower = max(lower, -offset / scale)
        upper = min(upper, (1 - offset) / scale)
        d = (3 * d + parity) // 2
    assert _rational(root["radicand_scale"]) == scale
    assert _rational(root["radicand_offset"]) == offset
    guard = root["guard_squared"]
    assert isinstance(guard, dict)
    if lower >= upper:
        lower = upper = Fraction(0)
    assert _rational(guard["lower"]) == lower
    assert _rational(guard["upper"]) == upper
    assert guard["empty"] == (lower == upper)
    assert guard["lower_closed"] and not guard["upper_closed"]
    assert not term._segments_ready and not term.physical_publications
    assert term.ledger.counters["mahler_root_shell_projections"] == 1
    assert term.ledger.counters["mahler_root_shell_operand_bits"] > 0
