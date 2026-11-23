"""Cold action lookups must reuse checked parent nodes before arithmetic work."""

from __future__ import annotations

from collections.abc import Callable, MutableMapping
from typing import NoReturn, cast

import pytest

from number_compiler.arithmetic.fields.consumer_pullback import PrefixSafety
from number_compiler.sequences.comma import action_arena as action_arena_module
from number_compiler.sequences.comma.action_arena import (
    CommaActionID,
    CommaActionRecord,
)
from number_compiler.sequences.comma.boundary_quotient import (
    AffineWeight,
    BoundaryState,
)
from number_compiler.sequences.comma.power import CommaTerm


def _action_keys(term: CommaTerm) -> MutableMapping[tuple[object, ...], CommaActionID]:
    return cast(
        MutableMapping[tuple[object, ...], CommaActionID],
        object.__getattribute__(term.arena, "_keys"),
    )


def test_warm_phase_prefix_skips_transfer_and_displacement(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with CommaTerm(1, shared_cache=False) as term:
        arena = term.arena
        first = arena.phase_prefix(1, 7, 3)
        transfer_count = term.ledger.counters["comma_transfer_constructions"]
        assert transfer_count > 0

        def forbidden(*_args: object, **_kwargs: object) -> NoReturn:
            pytest.fail("warm phase prefix rebuilt its arithmetic payload")

        monkeypatch.setattr(arena, "transfer", forbidden)
        monkeypatch.setattr(action_arena_module, "phase_prefix_displacement", forbidden)
        original_node = arena.node
        node_calls = 0

        def counted_node(identifier: CommaActionID) -> CommaActionRecord:
            nonlocal node_calls
            node_calls += 1
            return original_node(identifier)

        monkeypatch.setattr(arena, "node", counted_node)
        for _ in range(20):
            assert arena.phase_prefix(1, 7, 3) == first
        assert node_calls == 20
        assert term.ledger.counters["comma_transfer_constructions"] == transfer_count
        assert arena.node(first).steps == 3


def test_phase_prefix_checks_key_binding_and_invalid_inputs_before_reuse() -> None:
    with CommaTerm(1, shared_cache=False) as term:
        arena = term.arena
        first = arena.phase_prefix(2, 0, 1)
        other_phase = arena.phase_prefix(2, 2, 1)
        assert first != other_phase
        assert arena.node(first).displacement != arena.node(other_phase).displacement
        _action_keys(term)[("phase-prefix", 2, 0, 1)] = other_phase
        with pytest.raises(ValueError, match="aliases a different action"):
            arena.phase_prefix(2, 0, 1)

    with CommaTerm(1, shared_cache=False) as term:
        for leading, digit, steps in (
            (True, 7, 3),
            (1, True, 3),
            (1, 7, True),
            (1, 7, 10),
        ):
            with pytest.raises(ValueError):
                term.arena.phase_prefix(leading, digit, steps)


def test_public_interner_cannot_issue_a_forged_phase_prefix() -> None:
    with CommaTerm(1, shared_cache=False) as term:
        arena = term.arena
        forged = CommaActionRecord(
            "phase-prefix",
            1,
            leading=1,
            entering_digit=7,
            displacement=999,
            maximum_guard=1000,
        )
        with pytest.raises(ValueError, match="aliases a different effect"):
            arena.intern_record(("phase-prefix", 1, 7, 1), forged)

        issued = arena.phase_prefix(1, 7, 1)
        assert arena.node(issued).displacement == 71


@pytest.mark.parametrize("leading,digit", [(1, 7), (2, 0), (5, 2), (9, 7)])
def test_cycle_composition_reuses_a_checked_parent_before_prefix_safety(
    monkeypatch: pytest.MonkeyPatch, leading: int, digit: int
) -> None:
    with CommaTerm(1, shared_cache=False) as term:
        arena = term.arena
        one = arena.cycles(leading, digit, 1)
        three = arena.cycles(leading, digit, 3)
        two = arena.cycles(leading, digit, 2)
        original = arena.node(three)
        original_node = arena.node
        node_calls: list[CommaActionID] = []

        def counted_node(identifier: CommaActionID) -> CommaActionRecord:
            node_calls.append(identifier)
            return original_node(identifier)

        monkeypatch.setattr(arena, "node", counted_node)

        def forbidden(_self: PrefixSafety, _later: PrefixSafety) -> NoReturn:
            pytest.fail("warm cycle composition recomputed its prefix guard")

        monkeypatch.setattr(PrefixSafety, "then", forbidden)
        assert arena.compose(one, two) == three
        assert node_calls == [one, two, three]
        node_calls.clear()
        assert arena.compose(two, one) == three
        assert node_calls == [two, one, three]
        assert arena.node(three) == original


def test_cycle_parent_key_rejects_forged_effect_and_incompatible_phase() -> None:
    with CommaTerm(1, shared_cache=False) as term:
        arena = term.arena
        one = arena.cycles(1, 7, 1)
        arena.cycles(1, 7, 2)
        wrong_parent = arena.cycles(1, 7, 4)
        _action_keys(term)[("cycle", 1, 0, 2)] = wrong_parent
        with pytest.raises(ValueError, match="aliases a different effect"):
            arena.compose(one, one)

    with CommaTerm(1, shared_cache=False) as term:
        before = term.arena.cycles(2, 0, 1)
        after = term.arena.cycles(2, 1, 1)
        combined = term.arena.compose(before, after)
        assert term.arena.node(combined).kind == "sequence"


def test_cycle_request_rejects_local_key_alias_before_warm_reuse() -> None:
    with CommaTerm(1, shared_cache=False) as term:
        arena = term.arena
        correct = arena.cycles(1, 7, 1)
        wrong = arena.cycles(1, 7, 2)
        _action_keys(term)[("cycle", 1, 0, 1)] = wrong

        with pytest.raises(ValueError, match="aliases a different effect"):
            arena.cycle_request(1, 7, 1)

        _action_keys(term)[("cycle", 1, 0, 1)] = correct
        assert arena.cycle_request(1, 7, 1) == (correct, True)


@pytest.mark.parametrize("available_work", [1, 2])
def test_warm_cycle_join_budget_refuses_before_unreserved_arithmetic(
    available_work: int,
) -> None:
    with CommaTerm(1, shared_cache=False) as term:
        arena = term.arena
        one = arena.cycles(1, 7, 1)
        two = arena.cycles(1, 7, 2)
        arena.cycles(1, 7, 3)
        used = term.ledger.counters["comma_work"] + term.ledger.counters.get(
            "comma_certificate_work", 0
        )
        requests = term.ledger.counters["comma_action_requests"]
        publications = term.ledger.counters["comma_action_publications"]
        arena.max_work = used + available_work

        with pytest.raises(ValueError, match="exceeds --max-comma-work"):
            arena.compose(one, two)

        assert term.ledger.counters["comma_work"] == used + available_work
        assert term.ledger.counters["comma_action_requests"] == requests
        assert term.ledger.counters["comma_action_publications"] == publications


def _record_weight_evaluations(
    monkeypatch: pytest.MonkeyPatch,
) -> list[int]:
    calls: list[int] = []
    original = AffineWeight.evaluate

    def counted(
        self: AffineWeight,
        exponent: int,
        *,
        charge_bits: Callable[[int], None] | None = None,
    ) -> int:
        calls.append(exponent)
        return original(self, exponent, charge_bits=charge_bits)

    monkeypatch.setattr(AffineWeight, "evaluate", counted)
    return calls


def test_boundary_weight_is_reused_only_within_one_receipt_transaction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with CommaTerm(1, shared_cache=False) as term:
        template = term.arena.boundary_template(BoundaryState("N", 2, 10))
        calls = _record_weight_evaluations(monkeypatch)
        with term.boundary_receipt_transaction():
            first = term.checked_boundary_prefix_steps(template, 10)
            for _ in range(20):
                assert term.checked_boundary_prefix_steps(template, 10) == first
            assert calls == [10]
            with pytest.raises(ValueError, match="source phase"):
                term.checked_boundary_prefix_steps(template, 11)
        with term.boundary_receipt_transaction():
            assert term.checked_boundary_prefix_steps(template, 10) == first
        assert calls == [10, 10]


def test_boundary_weight_transaction_rollback_discards_cached_scalar(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with CommaTerm(1, shared_cache=False) as term:
        template = term.arena.boundary_template(BoundaryState("N", 2, 10))
        calls = _record_weight_evaluations(monkeypatch)
        with pytest.raises(RuntimeError, match="abort"):
            with term.boundary_receipt_transaction():
                term.checked_boundary_prefix_steps(template, 10)
                raise RuntimeError("abort")
        with term.boundary_receipt_transaction():
            term.checked_boundary_prefix_steps(template, 10)
        assert calls == [10, 10]
