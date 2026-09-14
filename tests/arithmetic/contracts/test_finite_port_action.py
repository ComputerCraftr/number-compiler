from __future__ import annotations

from itertools import product
from typing import Literal, Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    TransferSummaryID,
)
from number_compiler.arithmetic.functions.finite_port_action import (
    FinitePortActionArena,
    PortVariable,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics


def test_reset_identity_functions_are_extensional_aliases_and_compose() -> None:
    arena = FinitePortActionArena()
    port = PortVariable(0, 0, "carry", 0)
    functions = [
        arena.unary(port, low, high)
        for low, high in ((False, False), (False, True), (True, True))
    ]
    assert functions[0] == arena.constant(False)
    assert functions[1] == arena.variable(port)
    assert functions[2] == arena.constant(True)
    for before, after, value in product(functions, functions, (False, True)):
        combined = arena.compose(before, after, port)
        expected = arena.apply(after, {port: arena.apply(before, {port: value})})
        assert arena.apply(combined, {port: value}) == expected
    assert arena.node_count == 3


@pytest.mark.parametrize("warm", (False, True))
def test_finite_port_rejects_subclass_and_scalar_aliases_before_work(
    warm: bool,
) -> None:
    arena = FinitePortActionArena()
    port = PortVariable(0, 0, "carry", 0)
    function = arena.variable(port)
    if warm:
        assert arena.apply(function, {port: False}) is False
    before = arena.ledger.snapshot()

    class TransferAlias(TransferSummaryID):
        pass

    alias = TransferAlias(function.owner, function.kind, function.local_id)
    with pytest.raises(ValueError, match="transfer handle"):
        arena.apply(alias, {port: False})
    for value in (0, 1, 0.0, 1.0):
        with pytest.raises(TypeError, match="Boolean"):
            arena.constant(cast("bool", value))
        with pytest.raises(TypeError, match="Booleans"):
            arena.unary(port, cast("bool", value), False)
        with pytest.raises(TypeError, match="Boolean values"):
            arena.apply(function, {port: cast(bool, value)})
    assert arena.ledger.snapshot() == before


def test_shannon_reduction_and_simultaneous_substitution_are_canonical() -> None:
    arena = FinitePortActionArena()
    xvar, yvar = PortVariable(0, 0, "carry", 0), PortVariable(1, 0, "carry", 0)
    x, y = arena.variable(xvar), arena.variable(yvar)
    zero = arena.constant(False)
    xy = arena.choose(x, y, zero)
    assert xy == arena.choose(y, x, zero)
    assert arena.choose(x, y, y) == y
    assert arena.negate(arena.negate(xy)) == xy
    swapped = arena.substitute(xy, {xvar: arena.negate(y), yvar: x})
    for a, b in product((False, True), repeat=2):
        assert arena.apply(swapped, {xvar: a, yvar: b}) == (a and not b)
    reflection = {xvar: yvar, yvar: xvar}
    assert arena.permute(arena.permute(swapped, reflection), reflection) == swapped
    with pytest.raises(ValueError, match="bijection"):
        arena.permute(swapped, {xvar: yvar})


def test_twenty_row_cut_stays_factored_and_never_enumerates_joint_states() -> None:
    arena = FinitePortActionArena()
    ports = [
        PortVariable(time, side, "carry", 0) for time in range(20) for side in (0, 1)
    ]
    identity = arena.cut({port: arena.variable(port) for port in reversed(ports)})
    resets = arena.cut({port: arena.constant(bool(port.time & 1)) for port in ports})
    combined = arena.compose_cut(identity, resets)
    assert combined == resets
    assert len(combined.components) == 40
    assert arena.node_count == 42
    for component in combined.components:
        assert arena.apply(component.function, {}) == bool(component.variable.time & 1)
    metrics = collect_ledger_metrics(arena.ledger)
    assert metrics.resource_audit_complete == 1
    assert metrics.resource_accounting_mismatch == 0
    assert metrics.forbidden_future_payloads == 0


def test_query_eviction_preserves_canonical_handles_and_live_inventory() -> None:
    arena = FinitePortActionArena()
    xvar, yvar = PortVariable(0, 0, "carry", 0), PortVariable(1, 0, "carry", 0)
    x, y = arena.variable(xvar), arena.variable(yvar)
    first = arena.choose(x, y, arena.constant(False))
    assert len(arena._ite) > 0
    count = arena.node_count
    arena.ledger.evict_query_memos()
    assert len(arena._ite) == 0
    assert arena.node_count == count
    assert arena.choose(y, x, arena.constant(False)) == first
    assert collect_ledger_metrics(arena.ledger).resource_accounting_mismatch == 0


def test_every_external_reference_is_validated_before_shortcuts_or_cache_hits() -> None:
    a, b = FinitePortActionArena(), FinitePortActionArena()
    port = PortVariable(0, 0, "carry", 0)
    local = a.variable(port)
    foreign = b.variable(port)
    a.choose(local, a.constant(True), a.constant(False))
    invalid = [
        foreign,
        ArenaHandle(a.owner, "finite-port-function", local.local_id),
        ActionProgramID(a.owner, "finite-port-function", local.local_id),
    ]
    for handle in invalid:
        with pytest.raises(ValueError):
            a.apply(cast("TransferSummaryID", handle), {port: False})
        with pytest.raises(ValueError):
            a.choose(a.constant(False), cast("TransferSummaryID", handle), local)
        with pytest.raises(ValueError):
            a.substitute(a.constant(False), {port: cast(TransferSummaryID, handle)})
    ledger = ResourceLedger(max_cache_entries=0)
    with pytest.raises(BlockContextBudgetExceeded):
        FinitePortActionArena(ledger)
    assert ledger.entries == ledger.nodes == 0


def test_composition_metrics_count_requests_and_evaluations_in_the_same_units() -> None:
    from number_compiler.arithmetic.functions.finite_port_action import (
        FinitePortActionArena,
        PortVariable,
    )

    arena = FinitePortActionArena()
    port = PortVariable(0, 0, "carry", 0)
    identity = arena.variable(port)
    for _ in range(3):
        arena.compose(identity, arena.constant(False), port)
        arena.choose(identity, arena.constant(True), arena.constant(False))
    counters = arena.ledger.counters
    assert (
        counters["composition_requests"]
        == counters.get("composition_cache_hits", 0)
        + counters["composition_evaluations"]
    )


def test_constant_substitution_prunes_unreachable_function_before_visiting(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = FinitePortActionArena()
    port = PortVariable(0, 0, "selector", 0)
    selected = arena.variable(port)
    unneeded = arena.variable(PortVariable(1, 0, "large-unneeded-interface", 0))
    root = arena.choose(selected, unneeded, arena.constant(False))

    def forbidden(*args: object) -> Never:
        raise AssertionError("constant cofactor must not compose the rejected branch")

    monkeypatch.setattr(arena, "choose", forbidden)
    before = arena.ledger.snapshot()
    assert arena.substitute(root, {port: arena.constant(False)}) == arena.constant(
        False
    )
    counters = arena.ledger.counters
    assert (
        counters["finite_port_substitution_visits"]
        - before.counters.get("finite_port_substitution_visits", 0)
        == 1
    )
    assert counters["finite_port_substitution_constant_prunes"] == 1
    assert arena.ledger.entries == before.entries
    other = FinitePortActionArena()
    frozen = arena.ledger.snapshot()
    with pytest.raises(ValueError):
        arena.substitute(
            root,
            {
                port: arena.constant(False),
                PortVariable(2, 0, "unused", 0): other.constant(False),
            },
        )
    assert arena.ledger.snapshot() == frozen


def test_decision_interner_metrics_separate_existing_keys_identity_and_publication() -> (
    None
):
    arena = FinitePortActionArena()
    port = PortVariable(0, 0, "carry", 0)
    identity = arena.variable(port)
    before = arena.ledger.snapshot()
    assert arena.variable(port) == identity
    assert (
        arena._intern(port, identity.local_id, identity.local_id) == identity.local_id
    )
    after = arena.ledger.snapshot()
    assert (
        after.counters["finite_decision_interner_requests"]
        == before.counters["finite_decision_interner_requests"] + 2
    )
    assert (
        after.counters["finite_decision_interner_hits"]
        == before.counters.get("finite_decision_interner_hits", 0) + 1
    )
    assert (
        after.counters["finite_decision_identity_reductions"]
        == before.counters.get("finite_decision_identity_reductions", 0) + 1
    )
    assert (
        after.counters["finite_decision_interner_evaluations"]
        == before.counters["finite_decision_interner_evaluations"]
    )
    assert (
        after.counters["finite_decision_published_nodes"]
        == before.counters["finite_decision_published_nodes"]
    )
    frozen = arena.ledger.snapshot()
    with pytest.raises(ValueError):
        arena._intern(PortVariable(0, 0, "carry", 1), -1, 0)
    assert arena.ledger.snapshot() == frozen


def test_private_node_interner_probes_integer_ids_without_handle_allocation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = FinitePortActionArena()
    port = PortVariable(0, 0, "carry", 0)
    identity = arena.variable(port)
    before = arena.ledger.snapshot()

    def forbidden(*_args: object) -> Never:
        raise AssertionError("private canonical lookup allocated a scoped handle")

    monkeypatch.setattr(arena, "_handle", forbidden)
    assert arena._intern(port, 0, 1) == identity.local_id
    for invalid in (False, 0.0):
        with pytest.raises(ValueError):
            arena._intern(port, cast("int", invalid), 1)
    after = arena.ledger.snapshot()
    assert (after.nodes, after.entries) == (before.nodes, before.entries)


@pytest.mark.parametrize(
    ("field", "value"), (("time", True), ("side", 0.0), ("bit", False), ("role", ""))
)
def test_private_node_interner_revalidates_forged_port_coordinates(
    field: Literal["bit", "role", "side", "time"],
    value: Literal[""] | bool | float,
) -> None:
    arena = FinitePortActionArena()
    port = PortVariable(0, 0, "validated-port", 0)
    object.__setattr__(port, field, value)
    before = arena.ledger.snapshot()
    with pytest.raises(ValueError):
        arena._intern(port, 0, 1)
    assert arena.ledger.snapshot() == before


def test_choice_subproblems_use_only_private_integer_identities(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.functions.finite_port_action import _ChoiceIndexKey

    arena = FinitePortActionArena()
    ports = tuple(PortVariable(0, 0, "choice-private", bit) for bit in range(3))
    first, second, third = (arena.variable(port) for port in ports)
    original = arena._handle
    calls = 0

    def counted(
        index: int,
    ) -> TransferSummaryID:
        nonlocal calls
        calls += 1
        return original(index)

    monkeypatch.setattr(arena, "_handle", counted)
    arena.choose(first, arena.choose(second, third, first), third)
    assert calls == 2  # one public handle for each choose result, never subproblems
    assert all(
        type(key) is _ChoiceIndexKey
        and all(
            type(index) is int
            for index in (
                key.condition,
                key.yes,
                key.no,
                result,
            )
        )
        for key, result in arena._ite.items()
    )


def test_private_choice_cache_numeric_alias_corruption_is_audited() -> None:
    arena = FinitePortActionArena()
    port = PortVariable(0, 0, "choice-corruption", 0)
    value = arena.variable(port)
    arena.choose(value, arena.constant(False), arena.constant(True))
    key = next(iter(arena._ite))
    arena._ite._data[key] = True
    arena.ledger.note_store_mutation()
    assert collect_ledger_metrics(arena.ledger).forbidden_future_payloads > 0


@pytest.mark.parametrize("corruption", ("wrong-node", "boolean-index", "mutated-key"))
def test_private_integer_interner_is_independently_linked_to_semantic_nodes(
    corruption: str,
) -> None:
    arena = FinitePortActionArena()
    first = arena.variable(PortVariable(0, 0, "carry", 0))
    second = arena.variable(PortVariable(0, 0, "carry", 1))
    assert collect_ledger_metrics(arena.ledger).forbidden_future_payloads == 0
    key = next(key for key, index in arena._keys.items() if index == first.local_id)
    if corruption == "mutated-key":
        object.__setattr__(key, "low", 1)
    else:
        arena._keys[key] = second.local_id if corruption == "wrong-node" else True
    arena.ledger.note_store_mutation()
    assert collect_ledger_metrics(arena.ledger).forbidden_future_payloads > 0


@pytest.mark.parametrize("corruption", ("redundant", "unordered", "terminal-payload"))
def test_integer_interner_audit_checks_reduction_order_and_terminals(
    corruption: str,
) -> None:
    arena = FinitePortActionArena()
    first = arena.variable(PortVariable(0, 0, "carry", 0))
    second = arena.variable(PortVariable(1, 0, "carry", 0))
    assert collect_ledger_metrics(arena.ledger).forbidden_future_payloads == 0
    key = next(key for key, index in arena._keys.items() if index == second.local_id)
    node = arena._nodes[second.local_id]
    if corruption == "terminal-payload":
        object.__setattr__(arena._nodes[0], "low", 1 << 255)
    else:
        low = 1 if corruption == "redundant" else first.local_id
        object.__setattr__(key, "low", low)
        object.__setattr__(node, "low", low)
    arena.ledger.note_store_mutation()
    assert collect_ledger_metrics(arena.ledger).forbidden_future_payloads > 0
