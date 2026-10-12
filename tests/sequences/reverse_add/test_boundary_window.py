from __future__ import annotations

from typing import Literal

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.reverse_add.boundary_window import (
    BoundaryRelationStore,
    FiniteBoundaryWindow,
    ReverseBoundaryWindowObservation,
    ReverseBoundaryWindowObserver,
    WindowRelationBudgetExceeded,
    WindowTile,
)
from number_compiler.sequences.reverse_add.boundary_window_store import (
    BoundaryOperation,
)
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def _engine(
    ledger: ResourceLedger,
    *,
    digits: int = 2,
    operation: Literal["reverse-add", "double-reverse"] = "reverse-add",
    maximum_entries: int = 8192,
    maximum_states: int = 4096,
) -> FiniteBoundaryWindow:
    store = BoundaryRelationStore(
        ledger,
        max_entries=maximum_entries,
        max_states=32_768,
    )
    return FiniteBoundaryWindow(
        digits,
        operation=operation,
        relation_store=store,
        max_states=maximum_states,
    )


def _window(value: int, digits: int) -> tuple[int, int]:
    source_digits = tuple(reversed(digits_lsd(value, 10)))
    return (
        int("".join(map(str, source_digits[:digits]))),
        int("".join(map(str, source_digits[-digits:]))),
    )


def _assert_literal_projection(
    outcomes: frozenset[WindowTile], *, expected: int, source: int
) -> None:
    prefix, suffix = _window(expected, 2)
    growth = len(str(expected)) - len(str(source))
    assert WindowTile(prefix, suffix, growth) in outcomes


@pytest.mark.parametrize("seed", (12_345, 19_999, 123_456_789))
@pytest.mark.parametrize("steps", range(1, 7))
def test_window_relation_contains_literal_reverse_add_successor(
    seed: int, steps: int
) -> None:
    ledger = ResourceLedger()
    engine = _engine(ledger)
    original_digits = digits_lsd(seed, 10)
    initial = engine.source_tile(original_digits)
    carry = engine.source_inner_carry(original_digits)
    outcomes = engine.advance(
        frozenset({initial}),
        steps,
        initial_inner=carry,
        max_operations=50_000,
    )

    current = seed
    for _ in range(steps):
        current += int(str(current)[::-1])
    _assert_literal_projection(outcomes, expected=current, source=seed)
    assert ledger.snapshot().peak_nodes > 0


def test_term_boundary_observation_reports_only_unanimous_edges() -> None:
    term = ReverseAddPoweredTerm(12_345, 1)
    observation = term.observe_boundary_macro()

    assert type(observation) is ReverseBoundaryWindowObservation
    assert observation.status == "available"
    assert observation.steps == 1
    assert observation.target_width == 5
    assert observation.window_digits == 2
    assert observation.prefix == "66"
    assert observation.suffix == "66"
    assert observation.full_integer_powered is False
    assert term._ledger.counters["reverse_boundary_window_queries"] > 0
    assert term._ledger.snapshot().nodes > 0


def test_term_boundary_observer_reuses_authenticated_source_carry_ports() -> None:
    term = ReverseAddPoweredTerm(12_345, 3)
    term.observe_boundary_macro()

    observer = term._boundary_observer
    workspace = term._workspace
    assert isinstance(observer, ReverseBoundaryWindowObserver)
    assert workspace is not None
    assert observer.source_workspace is workspace
    assert (
        term._ledger.counters.get("reverse_boundary_window_source_inner_scan_reads", 0)
        == 0
    )
    assert (
        term._ledger.counters.get("reverse_source_ports_layer_1_carry_queries", 0) > 0
    )


def test_boundary_observation_is_lazy_and_reuses_term_owned_relations() -> None:
    term = ReverseAddPoweredTerm(19_999, 6)
    first = term.observe_boundary_macro()
    before_reads = term._ledger.counters.get(
        "reverse_boundary_window_source_digit_reads", 0
    )
    second = term.observe_boundary_macro()

    assert first == second
    assert (
        term._ledger.counters.get("reverse_boundary_window_source_digit_reads", 0)
        == before_reads
    )
    assert (
        term._ledger.counters.get("reverse_boundary_window_observation_cache_hits", 0)
        == 1
    )
    assert any(
        row.role == "reverse_boundary_window_relation"
        for row in term._ledger.inventory()
    )
    audit = collect_ledger_metrics(term._ledger)
    assert audit.resource_audit_complete == 1, (
        "boundary observer payload audit failed: "
        f"unknown={audit.resource_audit_unknown_payloads}, "
        f"forbidden={audit.forbidden_future_payloads}, "
        f"unbounded={audit.retained_unbounded_future_integers}, "
        f"unregistered={audit.resource_unregistered_containers}/"
        f"{audit.resource_unregistered_payload_resolvers}, "
        f"mismatch={audit.resource_accounting_mismatch}, "
        f"inventory={audit.resource_inventory}"
    )
    assert audit.resource_audit_unknown_payloads == 0
    assert audit.forbidden_future_payloads == 0
    assert audit.resource_accounting_mismatch == 0


def test_boundary_observation_fails_closed_when_edges_disagree() -> None:
    term = ReverseAddPoweredTerm(19_999, 50)
    result = term.observe_boundary_macro(max_states=512, max_compositions=5000)
    assert result.status == "unavailable"
    assert result.full_integer_powered is False
    if result.status == "unavailable":
        assert result.target_width is None
        assert result.prefix == result.suffix == ""
        assert result.reason


def test_observation_rejects_changed_term_binding_and_nondecimal_base() -> None:
    changed = ReverseAddPoweredTerm(12_345, 1)
    changed.seed = 12_346
    with pytest.raises(ValueError, match="binding changed"):
        changed.observe_boundary_macro()

    binary = ReverseAddPoweredTerm(12_345, 1, base=2)
    with pytest.raises(ValueError, match="decimal-only"):
        binary.observe_boundary_macro()


def test_ledger_budget_refusal_is_not_converted_to_mathematical_unavailable() -> None:
    term = ReverseAddPoweredTerm(12_345, 2, max_cache_entries=0)
    with pytest.raises(BlockContextBudgetExceeded):
        term.observe_boundary_macro()


def test_boundary_relation_work_and_retention_limits_refuse_explicitly() -> None:
    ledger = ResourceLedger()
    engine = _engine(ledger, maximum_entries=1)
    initial = engine.source_tile(digits_lsd(12_345, 10))
    carry = engine.source_inner_carry(digits_lsd(12_345, 10))
    with pytest.raises(WindowRelationBudgetExceeded):
        engine.advance(frozenset({initial}), 8, initial_inner=carry, max_operations=0)


def test_boundary_frontier_append_failure_after_mutation_rolls_back(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    store = BoundaryRelationStore(ledger, max_entries=16, max_states=32)
    operation: BoundaryOperation = "reverse-add"
    frame: tuple[tuple[int, BoundaryOperation, int, int, int], bool] = (
        (2, operation, 12, 34, 1),
        False,
    )
    original = LedgerList.append

    def fail_after_append(self: LedgerList[object], value: object) -> None:
        original(self, value)
        if self is store.worklist:
            raise MemoryError("frontier append failed after mutation")

    with monkeypatch.context() as patch:
        patch.setattr(LedgerList, "append", fail_after_append)
        with (
            pytest.raises(MemoryError, match="after mutation"),
            store.charged_frontier() as frontier,
        ):
            frontier.push(frame)

    assert not store.worklist
    account = ledger.inventory_owner(store._workspace_owner)
    assert account.entries == account.nodes == account.observed_entries == 0

    with store.charged_frontier() as frontier:
        frontier.push(frame)
        assert frontier.pop() == frame
    assert ledger.entries == ledger.nodes == 0


@pytest.mark.parametrize("seed", (12_345, 12_347, 98_765, 19_871))
def test_double_reverse_parameter_engine_contains_literal_successor(seed: int) -> None:
    ledger = ResourceLedger()
    engine = _engine(ledger, operation="double-reverse")
    source_digits = digits_lsd(seed, 10)
    initial = engine.source_tile(source_digits)
    carry = engine.source_inner_carry(source_digits)
    outcomes = engine.advance(
        frozenset({initial}), 1, initial_inner=carry, max_operations=20
    )
    expected = 2 * int(str(seed)[::-1])
    _assert_literal_projection(outcomes, expected=expected, source=seed)


def test_double_reverse_refuses_zero_tail_and_symmetric_carry_views() -> None:
    ledger = ResourceLedger()
    engine = _engine(ledger, operation="double-reverse")
    source = engine.source_tile(digits_lsd(12_340, 10))
    with pytest.raises(WindowRelationBudgetExceeded, match="zero tail"):
        engine.next_tiles(source.prefix, source.suffix)
    with pytest.raises(ValueError, match="reverse/add"):
        engine.edge_carry_interface(source)


def test_reverse_add_boundary_carry_views_use_shared_three_state_monoid() -> None:
    engine = _engine(ResourceLedger())
    tile = engine.source_tile(digits_lsd(19_999, 10))

    low, high = engine.edge_carry_interface(tile)
    assert low in (0, 1)
    assert high in ((0, 0), (0, 1), (1, 1))
    nested = engine.nested_carry_interfaces(tile)
    assert nested[-1][0] == 2
    assert nested[-1][1] == low


def test_boundary_carry_interfaces_preserve_forward_and_reflected_order() -> None:
    engine = _engine(ResourceLedger(), digits=2)
    tile = WindowTile(prefix=48, suffix=24)

    assert engine.boundary_pair_word(tile) == (8, 10)
    assert engine.edge_carry_interface(tile) == (1, (0, 0))
    assert engine.nested_carry_interfaces(tile) == (
        (1, 0, (0, 0)),
        (2, 1, (0, 0)),
    )


def test_same_boundary_source_carry_can_diverge_on_next_inner_carry() -> None:
    engine = _engine(ResourceLedger(), digits=2)
    sources = (1_100_022, 1_100_522)
    digits = tuple(digits_lsd(source, 10) for source in sources)
    starts = tuple(engine.source_tile(word) for word in digits)
    initial_carries = tuple(engine.source_inner_carry(word) for word in digits)

    assert starts == (WindowTile(11, 22), WindowTile(11, 22))
    assert initial_carries == (0, 0)
    first_edges = tuple(
        engine.advance(
            frozenset({start}),
            1,
            initial_inner=carry,
            max_operations=100,
        )
        for start, carry in zip(starts, initial_carries, strict=True)
    )
    assert first_edges[0] == first_edges[1] == frozenset({WindowTile(33, 33)})

    possible_next_edges = engine.advance(first_edges[0], 1, max_operations=100)
    assert {tile.prefix for tile in possible_next_edges} == {66, 67}
    for source, first_edge in zip(sources, first_edges, strict=True):
        first_value = source + int(str(source)[::-1])
        next_value = first_value + int(str(first_value)[::-1])
        first_prefix, first_suffix = _window(first_value, 2)
        next_prefix, next_suffix = _window(next_value, 2)
        assert first_edge == frozenset({WindowTile(first_prefix, first_suffix, 0)})
        assert WindowTile(next_prefix, next_suffix, 0) in possible_next_edges


def test_observer_does_not_reuse_action_or_occurrence_identity_across_terms() -> None:
    left = ReverseAddPoweredTerm(19_999, 4)
    right = ReverseAddPoweredTerm(19_999, 5)
    left_observer = left.observe_boundary_macro()
    right_observer = right.observe_boundary_macro()

    assert left_observer.steps == 4
    assert right_observer.steps == 5
    assert left._boundary_observer is not right._boundary_observer


def test_same_binding_observer_from_another_term_ledger_is_rejected() -> None:
    owner = ReverseAddPoweredTerm(19_999, 6)
    foreign = ReverseAddPoweredTerm(19_999, 6)
    owner.observe_boundary_macro()
    foreign._boundary_observer = owner._boundary_observer
    foreign._boundary_observer_identity = owner._boundary_observer_identity

    with pytest.raises(ValueError, match="binding or budget changed"):
        foreign.observe_boundary_macro()


def test_mutated_cached_window_result_is_rejected() -> None:
    term = ReverseAddPoweredTerm(19_999, 6)
    observation = term.observe_boundary_macro()
    object.__setattr__(observation, "prefix", "00")

    with pytest.raises(ValueError, match="observation cache was changed"):
        term.observe_boundary_macro()
