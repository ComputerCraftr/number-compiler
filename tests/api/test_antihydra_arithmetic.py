"""Total Antihydra arithmetic terms share one source-bound cylinder owner."""

from __future__ import annotations

from typing import cast

import pytest

from number_compiler.api.antihydra_observation import observe_run
from number_compiler.api.number_api import AntihydraTermPayload, NumberCompiler
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.antihydra.blocks import (
    admitted_arithmetic_cylinder,
    arithmetic_from_word,
    arithmetic_kernel,
)
from number_compiler.sequences.antihydra.runtime import (
    AntihydraArithmeticTerm,
    ArithmeticResult,
    ArithmeticSegment,
    CylinderEngine,
    run,
)


def _reference(returns: int) -> tuple[int, int, int, int | None]:
    h, balance, minimum = 8, 0, 0
    first_failure: int | None = None
    for index in range(returns):
        balance += -1 if h & 1 else 2
        minimum = min(minimum, balance)
        if balance < 0 and first_failure is None:
            first_failure = index
        h += h // 2
    return h, balance, minimum, first_failure


@pytest.mark.parametrize("width,residue", ((1, 0), (8, 173)))
def test_admitted_constructor_is_the_canonical_bounded_kernel(
    width: int, residue: int
) -> None:
    assert admitted_arithmetic_cylinder(residue, width) == arithmetic_kernel(
        residue, width
    )


@pytest.mark.parametrize("width,residue", ((9, 341), (64, (1 << 63) + 17)))
def test_admitted_constructor_owns_wide_source_parity(width: int, residue: int) -> None:
    admitted = admitted_arithmetic_cylinder(residue, width)
    assert admitted == arithmetic_from_word(residue, width, admitted.parity_word)
    with pytest.raises(ValueError, match="kernel width"):
        arithmetic_kernel(residue, width)


@pytest.mark.parametrize("returns", (0, 1, 7, 64, 65, 257))
def test_total_arithmetic_result_matches_source_recurrence(returns: int) -> None:
    term = AntihydraArithmeticTerm(returns)
    result = term.result()
    assert (result.h, result.balance, result.minimum, result.first_failure_index) == (
        _reference(returns)
    )
    assert result.returns == returns
    assert len(term.segments) <= (returns + 63) // 64
    assert not term.engine.memo
    assert term.ledger.counters.get("physical_roof_evaluations", 0) == 0


def test_number_api_is_lazy_and_reuses_arithmetic_owner_for_info_and_physical(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    compiler = NumberCompiler()
    projected = compiler.project_nth("antihydra", 129)
    assert type(projected.payload) is AntihydraTermPayload
    owner = projected.payload.term
    assert owner._result is None and not owner.segments
    reused = compiler.project_nth("antihydra", 129).payload
    assert type(reused) is AntihydraTermPayload
    assert reused.term is owner

    expected = _reference(129)[0]
    assert projected.materialize(max_bits=4096) == expected
    arithmetic_work = owner.ledger.counters["arithmetic_block_applications"]
    assert projected.payload.info()["h"] == expected
    assert owner.ledger.counters["arithmetic_block_applications"] == arithmetic_work
    assert owner.ledger.counters.get("physical_roof_evaluations", 0) == 0
    reference = run(129)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("physical roof rediscovered arithmetic branches")

    monkeypatch.setattr(
        "number_compiler.sequences.antihydra.blocks.arithmetic_kernel", forbidden
    )
    monkeypatch.setattr(
        "number_compiler.sequences.antihydra.runtime.arithmetic_kernel", forbidden
    )
    physical = projected.payload.physical_run()
    assert (
        physical.h,
        physical.balance,
        physical.minimum,
        physical.left,
        physical.right,
        physical.halted,
    ) == (
        reference.h,
        reference.balance,
        reference.minimum,
        reference.left,
        reference.right,
        reference.halted,
    )
    assert owner.ledger.counters["arithmetic_block_applications"] == arithmetic_work
    assert owner.ledger.counters.get("physical_roof_evaluations", 0) > 0
    assert owner.ledger.counters.get("physical_roof_branch_discovery_steps", 0) == 0


def test_arithmetic_budgets_and_blank_source_are_fail_closed() -> None:
    compiler = NumberCompiler()
    with pytest.raises(ValueError, match="budget"):
        compiler.project_nth("antihydra", 17, max_steps=16)
    with pytest.raises(ValueError, match="budget"):
        compiler.project_nth("antihydra", 17, max_state_bits=16)
    with pytest.raises(ValueError, match="blank-tape"):
        compiler.project_nth("antihydra", 1, seed=8)
    limited = NumberCompiler(max_context_nodes=128, max_cache_entries=64)
    payload = limited.project_nth("antihydra", 1).payload
    assert type(payload) is AntihydraTermPayload
    assert payload.term.engine.capacity == 64


def test_output_budget_refuses_before_arithmetic_execution() -> None:
    compiler = NumberCompiler()
    with pytest.raises(ValueError):
        compiler.nth("antihydra", 1000, max_bits=32)
    payload = compiler.project_nth("antihydra", 1000).payload
    assert type(payload) is AntihydraTermPayload
    assert payload.term._result is None
    assert not payload.term.segments
    assert compiler.nth("antihydra", 0, max_bits=4) == 8


def test_failed_result_publication_rolls_back_retained_support() -> None:
    term = AntihydraArithmeticTerm(8)
    term.max_state_bits = 4
    with pytest.raises(ValueError, match="state exceeds"):
        term.result()
    assert term._result is None and not term.segments
    row = next(
        item
        for item in term.ledger.inventory()
        if item.role == "arithmetic_cylinder_support"
    )
    assert row.entries == row.nodes == 0
    assert term.ledger.counters["arithmetic_publication_rollbacks"] == 1


def test_arithmetic_support_is_charged_and_auditable() -> None:
    term = AntihydraArithmeticTerm(130)
    term.result()
    report = audit_registered_payloads(term.ledger)
    assert report.forbidden_future_payloads == 0
    assert report.unknown_payloads == 0
    row = next(
        item
        for item in term.ledger.inventory()
        if item.role == "arithmetic_cylinder_support"
    )
    assert row.entries == row.nodes == len(term.segments) == 3

    result = term.result()
    object.__setattr__(result, "h", result.h + 1)
    with pytest.raises(ValueError, match="result was changed"):
        term.result()
    assert audit_registered_payloads(term.ledger).forbidden_future_payloads > 0


@pytest.mark.parametrize(
    "field,replacement",
    (
        ("requested", 8),
        ("returns", 8),
        ("h", 999),
        ("balance", 999),
        ("minimum", 999),
        ("left", 999),
        ("right", 999),
        ("halted", True),
    ),
)
def test_cached_physical_result_rejects_scalar_forgery(
    field: str, replacement: object
) -> None:
    term = AntihydraArithmeticTerm(7)
    result = term.physical_run()
    object.__setattr__(result, field, replacement)
    with pytest.raises(ValueError, match="physical result was changed"):
        term.physical_run()
    assert audit_registered_payloads(term.ledger).forbidden_future_payloads > 0


def test_total_h7_arithmetic_continues_past_guarded_first_failure() -> None:
    # 7,10,15,22 has chronological parity word 0101 (low bit first).
    block = arithmetic_from_word(7, 4, 0b0101)
    assert block.advance(7, 0) == (33, 2)
    assert block.minimum == -1

    term = AntihydraArithmeticTerm(0)
    h, balance, _left, _right, completed, halted = term._physical_block(
        block, 7, 0, 0, 0, 0
    )
    assert (h, balance, completed, halted) == (7, -1, 1, True)


def test_repeated_engine_execution_has_distinct_charged_publications() -> None:
    engine = CylinderEngine()
    first = engine.execute(64)
    second = engine.execute(64)
    first.require_source()
    second.require_source()
    assert first is not second
    rows = [row for row in engine.ledger.inventory() if row.role == "physical_result"]
    assert len(rows) == 2
    assert all(row.entries == 1 and row.nodes == 2 for row in rows)
    audit = audit_registered_payloads(engine.ledger)
    assert (
        audit.forbidden_future_payloads,
        audit.unbounded_future_integers,
        audit.unknown_payloads,
    ) == (0, 0, 0)


@pytest.mark.parametrize(
    "field,offset",
    (
        ("width", -1),
        ("residue", 1),
        ("output", 1),
        ("delta", 1),
        ("minimum", 1),
        ("parity_word", 1),
    ),
)
def test_retained_arithmetic_fields_are_bound_to_the_source_trajectory(
    field: str,
    offset: int,
) -> None:
    term = AntihydraArithmeticTerm(64)
    arithmetic = term.result()
    physical = term.physical_run()
    block = term.segments[0].cylinder
    replacement = getattr(block, field) + offset
    object.__setattr__(block, field, replacement)

    with pytest.raises(ValueError, match="arithmetic support was changed"):
        arithmetic.require_source()
    with pytest.raises(ValueError, match="arithmetic support was changed"):
        physical.require_source()
    with pytest.raises(ValueError, match="arithmetic support was changed"):
        term.physical_run()


def test_consistent_but_foreign_arithmetic_word_is_not_source_admissible() -> None:
    term = AntihydraArithmeticTerm(64)
    result = term.result()
    original = term.segments[0]
    block = original.cylinder
    foreign = arithmetic_from_word(block.residue, block.width, block.parity_word ^ 1)
    term.segments[0] = ArithmeticSegment(original.start, foreign)

    with pytest.raises(ValueError, match="arithmetic support was changed"):
        result.require_source()


def test_boolean_segment_coordinate_is_rejected_by_runtime_and_audit() -> None:
    term = AntihydraArithmeticTerm(64)
    result = term.result()
    physical = term.physical_run()
    object.__setattr__(term.segments[0], "start", False)
    with pytest.raises(ValueError, match="arithmetic support was changed"):
        result.require_source()
    with pytest.raises(ValueError, match="arithmetic support was changed"):
        physical.require_source()
    audit = audit_registered_payloads(term.ledger)
    assert audit.forbidden_future_payloads + audit.unknown_payloads > 0


@pytest.mark.parametrize(
    "kind",
    (
        "clock",
        "modular",
        "tape",
        "twisted",
        "spacetime",
        "hasse",
        "hensel",
        "mahler",
        "tropical",
        "factor",
    ),
)
def test_every_direct_observer_rejects_mutated_retained_support(kind: str) -> None:
    result = run(64)
    block = result._term.segments[0].cylinder
    object.__setattr__(block, "parity_word", block.parity_word ^ 1)

    with pytest.raises(ValueError, match="arithmetic support was changed"):
        observe_run(result, kind=kind, modulus=3, width=2, sign=1, precision=8)


def test_retained_support_rejects_forged_segment_and_cylinder_types() -> None:
    for field in ("segment", "cylinder"):
        term = AntihydraArithmeticTerm(64)
        result = term.result()
        if field == "segment":
            term.segments[0] = cast(ArithmeticSegment, object())
        else:
            object.__setattr__(term.segments[0], "cylinder", object())
        with pytest.raises(ValueError, match="arithmetic support was changed"):
            result.require_source()


def test_run_rejects_forged_arithmetic_publication_type() -> None:
    result = run(8)

    class ForgedArithmeticResult:
        def require_source(self) -> None:
            return None

    result._term._result = cast(ArithmeticResult, ForgedArithmeticResult())
    with pytest.raises(ValueError, match="unbound Antihydra arithmetic result"):
        result.require_source()
