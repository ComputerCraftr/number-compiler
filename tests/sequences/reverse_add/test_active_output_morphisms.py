"""Local morphism laws; these do not assert whole-state future closure."""

from itertools import product

import pytest

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    compose_carry_fn,
    scan_carry_automaton,
)
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.formula.decimal_pair_coordinates import decimal_q95
from number_compiler.arithmetic.polynomials.centered_f5 import CenteredF5Transport
from number_compiler.hashlife.actions.field_actions import CoordinateOutputMorphismID
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.hashlife.tiles.tiles import TileArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.active_output import (
    CARRY_ACTION,
    F5,
    PAIR,
    Q95,
    ReverseActiveOutputArena,
)


def _arena() -> ReverseActiveOutputArena:
    return ReverseActiveOutputArena(BitFunctionArena(ResourceLedger()))


def test_q95_has_fixed_leaf_semantics_and_derived_three_state_carry() -> None:
    arena = _arena()
    bits = arena.bits
    port = FinitePort(PortVariable(0, 0, "q95", 0), 95)
    value = bits.variable((port,), port, Q95)
    output, forcing = arena.q95_output(value), arena.q95_forcing(value)
    assert arena.q95(output, forcing) == value
    domain = arena.q95_carry(value)
    assert bits.resolve(domain).signature.output == CARRY_ACTION
    for q in range(95):
        binding = {port.variable: q}
        symbol, residue = divmod(q, 5)
        assert bits.evaluate(arena.resolve(output), binding) == symbol
        assert bits.evaluate(forcing, binding) == residue
        assert bits.evaluate(domain, binding) == (
            0 if symbol < 9 else 1 if symbol == 9 else 2
        )
    assert bits.evaluate(domain, {port.variable: 95}) is None
    with pytest.raises(ValueError, match="encoded width"):
        bits.evaluate(domain, {port.variable: -1})


def test_q95_carry_projection_needs_no_intermediate_output_publication(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = _arena()
    bits = arena.bits
    port = FinitePort(PortVariable(0, 0, "q95", 0), 95)
    carrier = bits.variable((port,), port, Q95)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("carry projection constructed another output state")

    monkeypatch.setattr(arena, "q95_output", forbidden)
    monkeypatch.setattr(arena, "intern", forbidden)
    derived = arena.q95_carry(carrier)
    assert arena.ledger.counters.get("reverse_active_output_publications", 0) == 0
    for q in range(95):
        expected = 0 if q // 5 < 9 else 1 if q // 5 == 9 else 2
        assert bits.evaluate(derived, {port.variable: q}) == expected


def test_equal_q95_leaf_is_not_a_future_source_occurrence() -> None:
    """A local quotient match cannot authorize a whole temporal cache hit."""
    # Both width-three sources have the same outer pair 7 and the same
    # incoming carry, so their outer Q95 leaf at zero forcing is 35.
    outer_196 = 6 + 1
    outer_106 = 6 + 1
    assert outer_196 == outer_106 == 7
    assert decimal_q95(outer_196, 0) == decimal_q95(outer_106, 0) == 35

    # The differing center changes the next outer pair. This only refutes
    # source substitution based on a single leaf; it does not refute a full
    # source-bound saturated regional transformer.
    next_196 = 196 + 691
    next_106 = 106 + 601
    assert next_196 == 887 and next_106 == 707
    assert next_196 % 10 + next_196 // 100 == 15
    assert next_106 % 10 + next_106 // 100 == 14


def test_q95_region_summary_composes_without_primitive_port_expansion(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Spatial range closure, deliberately not a temporal successor theorem."""
    _poison_tiles(monkeypatch)
    arena = _arena()
    bits = arena.bits
    ports = (
        FinitePort(PortVariable(0, 0, "q95", 0), 95),
        FinitePort(PortVariable(0, 1, "carry-region", 0), 3),
    )
    leaf = bits.variable(ports, ports[0], Q95)
    prefix = bits.variable(ports, ports[1], CARRY_ACTION)
    allowed = bits.constant(FunctionSignature(ports, BOOL), 1)
    scan, _ = bits.complete_transform(
        ports, (leaf, arena.carry_then(prefix, arena.q95_carry(leaf))), allowed
    )
    with monkeypatch.context() as patch:

        def forbidden(*_args: object) -> int:
            raise AssertionError("range composition evaluated a symbol")

        patch.setattr(bits, "evaluate", forbidden)
        square, _ = bits.compose_complete_transform(scan, scan)
        fourth, _ = bits.compose_complete_transform(square, square)
    # Repeated equal-domain spatial ranges are idempotent, including EQ.
    assert scan == square == fourth
    assert tuple(port.cardinality for port in fourth.ports) == (95, 3)
    monoid = (CarryFn.CONST0, CarryFn.ID, CarryFn.CONST1)
    for q, incoming in product(range(95), range(3)):
        symbol = q // 5
        leaf_domain = 0 if symbol < 9 else 1 if symbol == 9 else 2
        expected = monoid.index(compose_carry_fn(monoid[leaf_domain], monoid[incoming]))
        values = {ports[0].variable: q, ports[1].variable: incoming}
        assert bits.evaluate(fourth.outputs[1], values) == expected


def _poison_tiles(monkeypatch: pytest.MonkeyPatch) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("local morphisms must not construct exact output tiles")

    monkeypatch.setattr(TileArena, "leaf", forbidden)
    monkeypatch.setattr(TileArena, "join", forbidden)
    monkeypatch.setattr(TileScheduler, "complete", forbidden)
    monkeypatch.setattr(TileScheduler, "_complete_direct", forbidden)


def test_complete_local_law_and_output_control_reconstruction() -> None:
    arena = _arena()
    bits = arena.bits
    ports = tuple(
        FinitePort(PortVariable(0, i, "coordinate", 0), cardinality)
        for i, cardinality in enumerate((19, 2, 19, 2))
    )
    functions = tuple(
        bits.variable(ports, p, PAIR if p.cardinality == 19 else BOOL) for p in ports
    )
    output = arena.pair(*functions)
    alpha, beta, nu = arena.coordinates(output)
    assert arena.from_coordinates(alpha, beta, nu) == output
    left_alpha = arena.coordinates(arena.intern(functions[0]))[0]
    right_alpha = arena.coordinates(arena.intern(functions[2]))[0]
    birth = arena.add_alpha(
        bits.map_atoms(functions[1], F5, (0, 1)),
        bits.map_atoms(functions[3], F5, (0, 1)),
    )
    assert arena.add_alpha(arena.add_alpha(left_alpha, right_alpha), birth) == alpha
    repeated = arena.pair(functions[0], functions[1], functions[0], functions[3])
    assert (
        arena.transported_alpha(CenteredF5Transport(1, 0), lambda _x: left_alpha, birth)
        == arena.coordinates(repeated)[0]
    )
    carry = arena.carry_action(output)
    for left, c, right, d in product(range(19), range(2), range(19), range(2)):
        values = dict(
            zip((p.variable for p in ports), (left, c, right, d), strict=True)
        )
        expected = (left + c) % 10 + (right + d) % 10
        assert bits.evaluate(arena.resolve(output), values) == expected
        assert bits.evaluate(alpha, values) == expected % 5
        assert bits.evaluate(beta, values) == expected % 10 // 5
        assert bits.evaluate(nu, values) == expected // 10
        assert bits.evaluate(carry, values) == (
            0 if expected < 9 else 1 if expected == 9 else 2
        )
    invalid = {p.variable: 0 for p in ports}
    invalid[ports[0].variable] = 19
    assert bits.evaluate(arena.resolve(output), invalid) is None


def test_transport_birth_cancellation_before_output_interning() -> None:
    arena = _arena()
    bits = arena.bits
    port = FinitePort(PortVariable(0, 0, "alpha-at-x", 0), 5)
    source = bits.variable((port,), port, F5)
    negative = bits.map_atoms(source, F5, (0, 4, 3, 2, 1))
    zero = bits.constant(FunctionSignature((port,), F5), 0)
    bit_zero = bits.constant(FunctionSignature((port,), BOOL), 0)
    combined = arena.transported_alpha(
        CenteredF5Transport(), lambda _x: source, negative
    )
    assert combined == zero
    assert arena.from_coordinates(
        combined, bit_zero, bit_zero
    ) == arena.from_coordinates(zero, bit_zero, bit_zero)
    # Same F5 channel alone must never identify different next carry actions.
    four, nine = arena.constant(4), arena.constant(9)
    assert arena.coordinates(four)[0] == arena.coordinates(nine)[0]
    assert four != nine
    assert arena.carry_action(four) != arena.carry_action(nine)
    with pytest.raises(BlockContextBudgetExceeded):
        arena.transported_alpha(
            CenteredF5Transport(0, 5**12 - 1),
            lambda _x: pytest.fail("dense transport called source before budget check"),
            zero,
            max_terms=4,
        )


@pytest.mark.parametrize(
    "first,second",
    [
        ((10, 0, 0, 10), (10, 9, 9, 10)),
        ((0, 9, 9, 10, 10, 9, 9, 0), (0, 14, 14, 0, 0, 14, 14, 0)),
    ],
)
def test_cold_cancellation_witness_local_coordinates(
    first: tuple[int, ...],
    second: tuple[int, ...],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _poison_tiles(monkeypatch)
    arena = _arena()
    bits = arena.bits
    carry_bits = tuple(bits.constant(FunctionSignature((), BOOL), c) for c in (0, 1))
    one = bits.constant(FunctionSignature((), PAIR), 1)
    outputs: list[tuple[CoordinateOutputMorphismID, ...]] = []
    for source in (first, second):
        boundaries = scan_carry_automaton(source).boundaries
        digits = tuple(
            arena.normalized(
                arena.resolve(arena.constant(s)),
                carry_bits[boundaries[i]],
            )
            for i, s in enumerate(source)
        )
        if boundaries[-1]:
            # One leading digit in the same least-to-most-significant frame.
            digits += (arena.normalized(one, carry_bits[0]),)
        ids = tuple(
            arena.intern(bits.add(a, b, PAIR))
            for a, b in zip(digits, digits[::-1], strict=True)
        )
        expected, _growth = pair_step(source, 10)
        assert tuple(bits.evaluate(arena.resolve(o), {}) for o in ids) == expected
        outputs.append(ids)
    assert first != second and outputs[0] == outputs[1]
    # IDs are coordinate functions, not a new exact-row or future-class handle.
    assert len(set(outputs[0] + outputs[1])) < len(outputs[0] + outputs[1])


def test_symbolic_successor_substitution_and_spatial_carry_composition(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _poison_tiles(monkeypatch)
    arena = _arena()
    bits = arena.bits
    p = FinitePort(PortVariable(0, 0, "local-symbol", 0), 19)
    source = bits.variable((p,), p, PAIR)
    zero = bits.constant(FunctionSignature((), BOOL), 0)
    step = arena.pair(source, zero, source, zero)
    squared = arena.substitute(step, {p.variable: arena.resolve(step)})
    assert squared == arena.pair(arena.resolve(step), zero, arena.resolve(step), zero)
    for s in range(19):
        assert bits.evaluate(arena.resolve(squared), {p.variable: s}) == 2 * (
            (2 * (s % 10)) % 10
        )
    actions = tuple(
        bits.constant(FunctionSignature((), CARRY_ACTION), i) for i in range(3)
    )
    monoid = (CarryFn.CONST0, CarryFn.ID, CarryFn.CONST1)
    for before, after in product(range(3), repeat=2):
        composed = arena.carry_then(actions[before], actions[after])
        assert bits.evaluate(composed, {}) == monoid.index(
            compose_carry_fn(monoid[after], monoid[before])
        )
        for c in (0, 1):
            incoming = bits.constant(FunctionSignature((), BOOL), c)
            assert arena.carry_apply(composed, incoming) == arena.carry_apply(
                actions[after], arena.carry_apply(actions[before], incoming)
            )


def test_scoped_ids_partial_channels_and_atomic_output_budget() -> None:
    arena = _arena()
    bits = arena.bits
    with pytest.raises(ValueError):
        arena.resolve(_arena().constant(0))
    alpha = bits.constant(FunctionSignature((), F5), 4)
    one = bits.constant(FunctionSignature((), BOOL), 1)
    invalid = arena.from_coordinates(alpha, one, one)
    assert bits.evaluate(arena.resolve(invalid), {}) is None
    assert invalid != arena.constant(0)
    function = bits.constant(FunctionSignature((), PAIR), 2)
    arena.ledger.max_cache_entries = arena.ledger.entries
    snapshot = arena.ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        arena.intern(function)
    assert arena.ledger.entries == snapshot.entries
    assert arena.ledger.nodes == snapshot.nodes
    assert all(i.accounting_delta in (None, 0) for i in arena.ledger.inventory())


def test_symbolic_forward_carry_geometry_and_growth_against_pair_oracle(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """All symmetric width-three blocks, with carry/growth left symbolic."""
    _poison_tiles(monkeypatch)
    arena = _arena()
    bits = arena.bits
    ports = tuple(
        FinitePort(PortVariable(0, i, "pair-coordinate", 0), 19) for i in range(2)
    )
    outer, inner = (bits.variable(ports, p, PAIR) for p in ports)
    outer_action, inner_action = (
        arena.carry_action(arena.intern(f)) for f in (outer, inner)
    )
    zero = bits.constant(FunctionSignature((), BOOL), 0)
    c1 = arena.carry_apply(outer_action, zero)
    c2 = arena.carry_apply(arena.carry_then(outer_action, inner_action), zero)
    final_action = arena.carry_then(
        arena.carry_then(outer_action, inner_action), outer_action
    )
    regrouped = arena.carry_then(
        outer_action, arena.carry_then(inner_action, outer_action)
    )
    assert regrouped == final_action
    growth = arena.carry_apply(final_action, zero)
    digit0 = arena.normalized(outer, zero)
    digit1 = arena.normalized(inner, c1)
    digit2 = arena.normalized(outer, c2)
    one = arena.normalized(arena.resolve(arena.constant(1)), zero)
    # Reflect already normalized digits; there is no reverse causal scan.
    edge = arena.intern(
        bits.select(growth, bits.add(digit0, one, PAIR), bits.add(digit0, digit2, PAIR))
    )
    middle = arena.intern(
        bits.select(
            growth, bits.add(digit1, digit2, PAIR), bits.add(digit1, digit1, PAIR)
        )
    )
    next_edge_action = arena.carry_action(edge)
    for a, b in product(range(19), repeat=2):
        values = {ports[0].variable: a, ports[1].variable: b}
        expected, grew = pair_step((a, b, a), 10)
        assert bits.evaluate(growth, values) == grew
        assert bits.evaluate(arena.resolve(edge), values) == expected[0]
        assert bits.evaluate(arena.resolve(middle), values) == expected[1]
        assert bits.evaluate(arena.carry_apply(next_edge_action, zero), values) == int(
            expected[0] >= 10
        )
