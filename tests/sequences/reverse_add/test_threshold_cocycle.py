"""Extensional nonlinear consumers and genuinely substituted temporal powers."""

from collections.abc import MutableMapping
from dataclasses import replace
from itertools import product
from typing import Never, cast

import pytest

from devtools.experiments.reverse_add.cocycle_temporal import (
    CocycleAction,
    CocycleTemporalArena,
)
from devtools.experiments.reverse_add.threshold_cocycle import (
    ResidueMorphism,
    ThresholdCocycleArena,
    ThresholdCocycleResidualID,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.active_output import DIGIT, F5


def test_primitive_cocycle_and_swapped_affine_arguments_are_extensional() -> None:
    k = ThresholdCocycleArena(BitFunctionArena(ResourceLedger()))
    x, y = (k.bits.variable(k.ports, p, DIGIT) for p in k.ports)
    a, b = k.from_representative(x), k.from_representative(y)
    forward = k.precompose(k.primitive, a, b)
    backward = k.precompose(k.primitive, b, a)
    assert forward == backward == k.primitive
    domain = k.domain(k.add(a, b), forward)
    for first, second in product(range(10), repeat=2):
        binding = dict(zip((p.variable for p in k.ports), (first, second), strict=True))
        assert k.bits.evaluate(k.resolve(forward), binding) == int(first + second >= 10)
        assert k.bits.evaluate(domain, binding) == (
            2 if first + second >= 10 else int(first + second == 9)
        )


def test_equal_kappa_does_not_erase_eq_and_restriction_is_part_of_identity() -> None:
    k = ThresholdCocycleArena(BitFunctionArena(ResourceLedger()))
    zero, nine, eight = k.constant(0, 0), k.constant(4, 1), k.constant(3, 0)
    a = k.precompose(k.primitive, zero, nine)
    b = k.precompose(k.primitive, zero, eight)
    assert a == b
    assert k.domain(k.add(zero, nine), a) != k.domain(k.add(zero, eight), b)
    one = k.bits.constant(FunctionSignature((), BOOL), 1)
    assert k.bits.evaluate(k.domain(nine, k.intern(one)), {}) is None
    x = k.bits.variable(k.ports, k.ports[0], DIGIT)
    even = k.bits.map_atoms(x, BOOL, tuple(int(v % 2 == 0) for v in range(10)))
    restricted = k.restrict(k.primitive, even)
    assert restricted != k.primitive
    with pytest.raises(ValueError, match="every"):
        k.compose_temporal(k.primitive, {}, restricted)
    identity = {p.variable: k.bits.variable(k.ports, p, DIGIT) for p in k.ports}
    assert k.compose_temporal(k.primitive, identity, restricted) == restricted
    shifted = k.representative(k.add(k.from_representative(x), k.constant(1, 1)))
    pulled = k.compose_temporal(
        restricted, {**identity, k.ports[0].variable: shifted}, k.primitive
    )
    for value in range(10):
        binding = {k.ports[0].variable: value, k.ports[1].variable: 9}
        result = k.bits.evaluate(k.resolve(pulled), binding)
        assert (result is not None) == bool(value % 2)


def test_affine_cocycle_squares_to_1024_with_primitive_and_evaluation_poisoned(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    bits = BitFunctionArena(ResourceLedger(max_nodes=20000, max_cache_entries=100000))
    k, t, ports, action = _additive_action(bits, "additive-cocycle-context")
    first = action
    powers = {1: action}

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError(
            "temporal composition performed primitive replay or point evaluation"
        )

    with monkeypatch.context() as patch:
        patch.setattr(t, "primitive", forbidden)
        patch.setattr(bits, "evaluate", forbidden)
        patch.setattr(bits, "substitute", forbidden)
        patch.setattr(bits, "restrict", forbidden)
        for _ in range(10):
            action = t.compose(action, action)
            powers[action.events] = action
    assert t.primitive_successors == 1
    assert t.temporal_compositions == 10
    assert powers[16] == powers[256]
    assert t.saturated(powers[16]) == t.saturated(powers[256])
    doubled, retained = bits.compose_complete_transform(
        t.saturated(first),
        t.saturated(first),
        retained=tuple(k.resolve(residual) for residual in first.cocycles),
    )
    assert doubled == t.saturated(powers[2])
    assert retained == tuple(k.resolve(residual) for residual in powers[2].cocycles)
    for count, power in powers.items():
        for x, y in product(range(10), repeat=2):
            bind = dict(
                zip(
                    (p.variable for p in ports),
                    (x % 5, x % 2, y % 5, y % 2, 0),
                    strict=True,
                )
            )
            assert bits.evaluate(power.outputs[0], bind) == (x + count * y) % 5
            assert bits.evaluate(power.outputs[1], bind) == (x + count * y) % 2
            assert bits.evaluate(power.outputs[-1], bind) == int(
                (x + (count - 1) * y) % 10 + y >= 10
            )
    with pytest.raises(ValueError, match="metadata"):
        t.compose(replace(first, events=True), first)
    with pytest.raises(ValueError, match="definedness"):
        t.compose(
            replace(first, admissible=bits.constant(FunctionSignature(ports, BOOL), 0)),
            first,
        )


def test_uninterned_cocycle_cannot_bypass_root_accounting() -> None:
    k = ThresholdCocycleArena(BitFunctionArena(ResourceLedger()))
    function = k.bits.constant(FunctionSignature((), BOOL), 0)
    forged = ThresholdCocycleResidualID(function)
    with pytest.raises(ValueError, match="not interned"):
        k.resolve(forged)
    count = k.residual_count
    assert k.resolve(k.intern(function)) == function
    assert k.residual_count == count + 1
    assert k.intern(function) == forged
    assert k.residual_count == count + 1


def test_temporal_composition_cache_is_complete_and_event_sensitive() -> None:
    bits = BitFunctionArena(ResourceLedger())
    _unused_k_binding, t, ports, action = _additive_action(bits, "cache-context")

    initial_requests = bits.ledger.counters.get("temporal_composition_requests", 0)
    initial_validations = bits.ledger.counters.get(
        "temporal_composition_validation_attempts", 0
    )
    first = t.compose(action, action)
    assert bits.ledger.counters["temporal_composition_requests"] == initial_requests + 1
    assert (
        bits.ledger.counters["temporal_composition_validation_attempts"]
        == initial_validations + 2
    )
    second = t.compose(action, action)
    assert second == first
    assert t.temporal_composition_cache_hits == 1
    assert t.temporal_compositions == 1
    assert bits.ledger.counters["temporal_composition_requests"] == initial_requests + 2
    assert (
        bits.ledger.counters["temporal_composition_validation_attempts"]
        == initial_validations + 5
    )

    cache_key = next(iter(t._composition_cache))
    cache_data = cast(MutableMapping[object, object], t._composition_cache._data)
    original_entry = cache_data[cache_key]
    cache_data[cache_key] = object()
    try:
        with pytest.raises(ValueError, match="cache payload"):
            t.compose(action, action)
    finally:
        cache_data[cache_key] = original_entry

    cached_entry = next(iter(t._composition_cache.values()))
    original_entry_id = cached_entry.entry_id
    object.__setattr__(cached_entry, "entry_id", False)
    try:
        with pytest.raises(ValueError, match="cache entry"):
            t.compose(action, action)
    finally:
        object.__setattr__(cached_entry, "entry_id", original_entry_id)

    original_key = cached_entry.key
    object.__setattr__(
        cached_entry,
        "key",
        replace(original_key, before_events=True),
    )
    try:
        with pytest.raises(ValueError, match="cache key"):
            t.compose(action, action)
    finally:
        object.__setattr__(cached_entry, "key", original_key)

    output_handle = cached_entry.result.outputs[0]
    original_local_id = output_handle.local_id
    replacement = bits.constant(FunctionSignature(ports, F5), 0)
    object.__setattr__(output_handle, "local_id", replacement.local_id)
    try:
        with pytest.raises(ValueError, match="cache seal"):
            t.compose(action, action)
    finally:
        object.__setattr__(output_handle, "local_id", original_local_id)

    event_shifted = replace(action, events=2)
    t.compose(event_shifted, action)
    assert t.temporal_composition_cache_hits == 1
    assert t.temporal_compositions == 2

    cached_entry = next(iter(t._composition_cache.values()))
    original_events = cached_entry.result.events
    object.__setattr__(cached_entry.result, "events", original_events + 1)
    try:
        with pytest.raises(ValueError, match="cache seal"):
            t.compose(action, action)
    finally:
        object.__setattr__(cached_entry.result, "events", original_events)


def _additive_action(
    bits: BitFunctionArena,
    role: str,
) -> tuple[
    ThresholdCocycleArena, CocycleTemporalArena, tuple[FinitePort, ...], CocycleAction
]:
    k = ThresholdCocycleArena(bits)
    t = CocycleTemporalArena(k)
    sorts = (F5, BOOL, F5, BOOL, BOOL)
    ports = tuple(
        FinitePort(PortVariable(0, i, role, 0), sort.cardinality)
        for i, sort in enumerate(sorts)
    )
    a, e, b, f, _last = (
        bits.variable(ports, port, sort)
        for port, sort in zip(ports, sorts, strict=True)
    )
    left, right = ResidueMorphism(a, e), ResidueMorphism(b, f)
    value = k.add(left, right)
    residual = k.precompose(k.primitive, left, right)
    action = t.primitive(
        ports,
        (value.alpha, value.epsilon, b, f, k.resolve(residual)),
        (residual,),
        bits.constant(FunctionSignature(ports, BOOL), 1),
    )
    return k, t, ports, action
