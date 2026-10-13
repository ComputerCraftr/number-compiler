"""Independent bounded consumer checks, distinct from a non-halting proof."""

import subprocess
import sys
from dataclasses import fields
from fractions import Fraction

import pytest

from number_compiler.api.antihydra_observation import observe_run
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.query_types import AntihydraTermQuery
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicAggregateSummary,
)
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.antihydra import runtime
from number_compiler.sequences.antihydra.arithmetic_images import (
    AntihydraArithmeticImageWorkspace,
)
from number_compiler.sequences.antihydra.mahler import tangent
from number_compiler.sequences.antihydra.mahler_action import associated_action
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm, run
from tests.support.report_values import object_record


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


def test_one_return_uses_source_bound_bit_without_aggregate_projection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = AntihydraArithmeticTerm(1, shared_cache=False)
    result = term.result()
    workspace = term.arithmetic_workspace
    assert workspace is not None

    def forbidden_projection(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("one-return Mahler leaf requested aggregate projection")

    monkeypatch.setattr(
        type(workspace.scheduler), "source_projection", forbidden_projection
    )
    packet = associated_action(result)
    assert _rational(packet["scale"]) == Fraction(3, 2)
    assert _rational(packet["offset"]) == Fraction(-3, 2)
    assert _rational(packet["cap"]) == Fraction(3, 4)

    original_seed = workspace.seed
    object.__setattr__(workspace, "seed", original_seed + 1)
    try:
        with pytest.raises(ValueError, match="source image was changed"):
            associated_action(result)
    finally:
        object.__setattr__(workspace, "seed", original_seed)


def test_physical_adapter_authenticates_arithmetic_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    physical = run(2)
    original = runtime.ArithmeticResult.require_source
    validated: list[runtime.ArithmeticResult] = []

    def counted(result: runtime.ArithmeticResult) -> None:
        validated.append(result)
        original(result)

    monkeypatch.setattr(runtime.ArithmeticResult, "require_source", counted)
    arithmetic = runtime.authenticated_arithmetic_result(physical)
    assert validated == [arithmetic]
    assert arithmetic is physical._term._result
    assert runtime.authenticated_arithmetic_result(arithmetic) is arithmetic
    assert validated == [arithmetic, arithmetic]


@pytest.mark.parametrize("forged_owner", ("run", "arithmetic"))
def test_physical_adapter_rejects_forged_source_owner(forged_owner: str) -> None:
    physical = run(2)
    arithmetic = physical._term._result
    assert type(arithmetic) is runtime.ArithmeticResult
    owner = physical if forged_owner == "run" else arithmetic
    token = owner._source
    object.__setattr__(owner, "_source", object())
    try:
        with pytest.raises(ValueError, match="unbound Antihydra"):
            runtime.authenticated_arithmetic_result(physical)
    finally:
        object.__setattr__(owner, "_source", token)


@pytest.mark.parametrize("precision", (1, 2, 8, 65))
@pytest.mark.parametrize("extent", (0, 1024))
def test_tangent_uses_one_precision_limited_clock(
    precision: int, extent: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.sequences.antihydra import mahler
    from number_compiler.sequences.collatz.inverse_three_clock import InverseThreeClock

    result = AntihydraArithmeticTerm(extent).result()
    demanded: list[tuple[int, int]] = []

    class CountedClock(InverseThreeClock):
        @property
        def inverse_unit(self) -> int:
            demanded.append((self.precision, self.phase))
            return super().inverse_unit

    monkeypatch.setattr(mahler, "InverseThreeClock", CountedClock)
    packet = tangent(result, precision)
    modulus = 1 << precision
    inverse = pow(3, -result.returns, modulus)
    normalized = (result.h - 1) * inverse % modulus
    root = -pow(3, -result.returns - 1, modulus) % modulus
    difference = (normalized - root) % modulus
    expected_match = (
        (difference & -difference).bit_length() - 1 if difference else precision
    )
    assert packet["normalized_residue"] == normalized
    assert packet["clock_root"] == root
    assert packet["matched_bits"] == expected_match
    assert packet["resolved"] == bool(difference)
    assert len(demanded) == 1
    assert demanded[0][0] == max(3, precision)
    if not difference:
        assert packet["required_next_precision"] == precision + 6
    assert result.ledger.counters["tangent_inverse_clock_demands"] == 1
    assert result.ledger.counters["tangent_modular_power_exponent_bits"] == (
        demanded[0][1].bit_length()
    )
    assert (
        result.ledger.counters["tangent_clock_input_exponent_bits"]
        == (extent + 1).bit_length()
    )
    assert result.ledger.counters["tangent_modular_operand_bits"] == (
        max(1, (result.h - 1).bit_length())
        + max(1, ((result.h - 1) & (modulus - 1)).bit_length())
        + max(1, inverse.bit_length())
        + 3 * (max(3, precision) + 1)
    )


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
    # Public source validation reads the aggregate twice (result and endpoint).
    # The Mahler projector consumes the authenticated image summary directly.
    assert len(published) == prior + 2
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
    assert NumberCompiler().nth(AntihydraTermQuery(64)) == result.h
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


@pytest.mark.parametrize("extent", (0, 1, 2, 3, 8, 63, 64, 65, 128, 257))
def test_compact_source_image_publishes_exact_arithmetic_and_shared_mahler_carry(
    extent: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.hashlife.execution import dyadic_return_transport

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("production arithmetic constructed a branch itinerary")

    for name in ("residue_macro", "balanced_residue_macro"):
        monkeypatch.setattr(dyadic_return_transport, name, forbidden)
    term = AntihydraArithmeticTerm(extent)
    result = term.result()
    packet = associated_action(result)
    residual = object_record(packet["temporal_run_residual"])
    d, carry, balance, minimum, first_failure = 7, 0, 0, 0, None
    for index in range(extent):
        bit = d & 1
        carry = 3 * carry + (bit << index)
        d = (3 * d + bit) // 2
        balance += 2 if bit else -1
        minimum = min(minimum, balance)
        if balance < 0 and first_failure is None:
            first_failure = index
    assert (result.h, result.balance, result.minimum, result.first_failure_index) == (
        d + 1,
        balance,
        minimum,
        first_failure,
    )
    assert residual["Q"] == extent and residual["C"] == carry
    assert _rational(residual["rho"]) == Fraction(2**extent, 3**extent)
    assert _rational(residual["h"]) == Fraction(4 * carry, 3**extent)
    assert residual["delta"] == balance and residual["minimum"] == minimum
    workspace = term.arithmetic_workspace
    assert workspace is not None
    if extent:
        support_id = workspace.summary().support
        assert support_id is not None
        support = workspace.support_node(support_id)
        assert support.saturated and support.children is None
        assert support.branch_word is None
        if extent <= workspace.MAX_LEAF_STEPS:
            assert term.ledger.counters["antihydra_arithmetic_temporal_run_actions"] > 0
        else:
            assert (
                term.ledger.counters["antihydra_arithmetic_balanced_composite_tails"]
                == 1
            )
    assert term.ledger.counters.get("antihydra_arithmetic_leaf_steps", 0) == 0
    assert not term._segments_ready


@pytest.mark.parametrize("bit,length", ((0, 1000), (1, 1000)))
def test_centered_run_selector_powers_both_antihydra_branches(
    bit: int, length: int
) -> None:
    workspace = AntihydraArithmeticTerm(0)._arithmetic_image()
    d = (1 << length) - 1 if bit else 1 << length
    runs = tuple(workspace._runs(d + 1, length))
    assert len(runs) == 1
    size, selected, endpoint = runs[0]
    assert (size, selected) == (length, bit)
    # Centered zero steps multiply by three, unlike the Collatz zero action.
    assert endpoint == 3**length - bit


@pytest.mark.parametrize("family", ("antihydra", "collatz"))
def test_independent_audit_accepts_run_image_and_demanded_support(family: str) -> None:
    from number_compiler.resources.dyadic_return_payload_audit import (
        audit_dyadic_return_payloads,
    )
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.collatz.physical_images import (
        CollatzPhysicalImageWorkspace,
    )

    ledger = ResourceLedger()
    workspace = (
        AntihydraArithmeticImageWorkspace(ledger, 65)
        if family == "antihydra"
        else CollatzPhysicalImageWorkspace(ledger, 27, 65, retain_chronology=False)
    )
    assert not audit_dyadic_return_payloads(ledger).invalid
    assert ledger.counters["dyadic_payload_audit_branch_steps"] == 65
    assert sum(width for _start, width, _word in workspace.branch_segments()) == 65
    assert not audit_dyadic_return_payloads(ledger).invalid


@pytest.mark.parametrize("family", ("antihydra", "collatz"))
@pytest.mark.parametrize("field", ("offset", "delta", "minimum", "odd_steps", "source"))
@pytest.mark.parametrize("expanded", (False, True))
def test_independent_audit_rejects_resealed_saturated_run_forgery(
    family: str, field: str, expanded: bool
) -> None:
    from number_compiler.resources.dyadic_return_payload_audit import (
        audit_dyadic_return_payloads,
    )
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.collatz.physical_images import (
        CollatzPhysicalImageWorkspace,
    )

    ledger = ResourceLedger()
    workspace = (
        AntihydraArithmeticImageWorkspace(ledger, 65)
        if family == "antihydra"
        else CollatzPhysicalImageWorkspace(ledger, 27, 65, retain_chronology=False)
    )
    if expanded:
        assert sum(width for _start, width, _word in workspace.branch_segments()) == 65
    image = workspace.image_node(workspace.root_payload)
    summary = image.summary
    support_id = summary.support
    assert support_id is not None
    support = workspace.support_node(support_id)
    assert support.saturated
    if field == "source":
        source = workspace.source_node(workspace.root_source)
        object.__setattr__(source, "exact", False)
        raw_snapshot = workspace.source_snapshots[workspace.root_source.local_id]
        assert isinstance(raw_snapshot, tuple)
        snapshot: list[object] = list(raw_snapshot)
        snapshot[7] = False
        workspace.source_snapshots[workspace.root_source.local_id] = tuple(snapshot)
    else:
        raw_support_snapshot = workspace.support_snapshots[support_id.local_id]
        raw_image_snapshot = workspace.image_snapshots[workspace.root_payload.local_id]
        assert isinstance(raw_support_snapshot, tuple)
        assert isinstance(raw_image_snapshot, tuple)
        support_snapshot: list[object] = list(raw_support_snapshot)
        image_snapshot: list[object] = list(raw_image_snapshot)
        if field == "offset":
            replacement = support.transfer.offset + 1
            object.__setattr__(support.transfer, "offset", replacement)
            support_snapshot[3] = image_snapshot[5] = replacement
        else:
            replacement = getattr(support, field) + (-1 if field == "minimum" else 1)
            object.__setattr__(support, field, replacement)
            object.__setattr__(summary, field, replacement)
            support_index, image_index = {
                "delta": (6, 7),
                "minimum": (7, 8),
                "odd_steps": (5, 9),
            }[field]
            support_snapshot[support_index] = image_snapshot[image_index] = replacement
        workspace.support_snapshots[support_id.local_id] = tuple(support_snapshot)
        workspace.image_snapshots[workspace.root_payload.local_id] = tuple(
            image_snapshot
        )
    assert audit_dyadic_return_payloads(ledger).invalid
    if field != "source":
        # Rechecking the retained seal alone would accept these changes.
        # Independent source-law reconstruction must actually run.
        assert ledger.counters["dyadic_payload_audit_branch_steps"] == 65


def test_audit_rejects_negative_demanded_transfer_with_matching_exact_endpoint() -> (
    None
):
    from number_compiler.resources.dyadic_return_payload_audit import (
        audit_dyadic_return_payloads,
    )
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.collatz.physical_images import (
        CollatzPhysicalImageWorkspace,
    )

    ledger = ResourceLedger()
    workspace = CollatzPhysicalImageWorkspace(ledger, 27, 65, retain_chronology=False)
    summary = workspace.summary()
    assert summary.transfer.upper == 0
    assert sum(width for _start, width, _word in workspace.branch_segments()) == 65
    expanded_id = workspace.demanded_support[workspace.root_payload]
    expanded = workspace.support_node(expanded_id)
    transfer = expanded.transfer
    # Forge a decreasing map with the correct value at this one source.
    # Endpoint agreement cannot replace the independently checked branch law.
    object.__setattr__(transfer, "upper", -1)
    offset = summary.transfer.offset * transfer.lower + workspace.seed
    object.__setattr__(transfer, "offset", offset)
    assert transfer.upper * workspace.seed + offset == (
        summary.transfer.offset * transfer.lower
    )
    raw_snapshot = workspace.support_snapshots[expanded_id.local_id]
    assert isinstance(raw_snapshot, tuple)
    snapshot: list[object] = list(raw_snapshot)
    snapshot[2], snapshot[3] = -1, offset
    workspace.support_snapshots[expanded_id.local_id] = tuple(snapshot)
    assert audit_dyadic_return_payloads(ledger).invalid


@pytest.mark.parametrize("returns", (0, 1, 2, 8, 16, 128, 512))
def test_homogeneous_growth_is_demanded_from_admitted_mahler_extent(
    returns: int,
) -> None:
    term = AntihydraArithmeticTerm(returns)
    packet = associated_action(term.result())
    growth = object_record(packet["homogeneous_growth"])
    assert (growth["growths"], growth["halvings"], growth["radix"]) == (
        returns,
        returns,
        10,
    )
    order = growth["homogeneous_radix_order"]
    assert type(order) is int
    scale = Fraction(3, 2) ** returns
    assert Fraction(10) ** order <= scale < Fraction(10) ** (order + 1)
    rational = object_record(packet["scale"])
    numerator, denominator = rational["numerator"], rational["denominator"]
    assert type(numerator) is int and type(denominator) is int
    assert scale == Fraction(numerator, denominator)
    assert not any(
        row.entries or row.nodes
        for row in term.ledger.inventory()
        if row.name.startswith("homogeneous-growth")
    )
