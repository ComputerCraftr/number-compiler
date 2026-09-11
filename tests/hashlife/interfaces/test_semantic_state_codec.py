"""An arbitrary primitive continuation is encoded by independent formal ports."""

from __future__ import annotations

from dataclasses import replace
from itertools import product
from typing import TYPE_CHECKING, Literal

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
    PhysicalCollatzFourBlockEffect,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.hashlife.interfaces.semantic_state_codec import StateCodecArena
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructureID,
)
from tests.support.diamond_continuation_reduction import machine
from tests.support.semantic_state_codec import tiny

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.interfaces.semantic_state_codec import StateCodecArena


def codec_arena(
    runtime: DiamondRuntime,
) -> StateCodecArena:
    structures = StructureArena(BitFunctionArena(runtime.ledger))
    return StateCodecArena(runtime, structures)


@pytest.mark.parametrize("side", [0, 1])
def test_every_small_arbitrary_continuation_and_anchor_are_preserved(side: int) -> None:
    runtime, action = tiny()
    arena = codec_arena(runtime)
    paired = runtime.actions.compose(action, action)
    codec = arena.compile(paired, side)
    anchor = arena.anchor(codec)
    assert codec.argument_port is not None
    target = AtomSort("argument", codec.argument_port.cardinality)
    assert codec.argument_port is not None
    selected = tuple(
        arena.evaluate_continuation(
            codec, arena.structures.bits.constant(FunctionSignature((), target), q)
        )
        for q in range(codec.argument_port.cardinality)
    )
    observed = set()
    assert codec.continuation_cardinality is not None
    for initial in range(codec.anchor_cardinality):
        for values in product(
            range(codec.continuation_cardinality), repeat=len(codec.component_ports)
        ):
            inputs = {codec.anchor_port.variable: initial}
            inputs.update(
                (port.variable, value)
                for port, value in zip(codec.component_ports, values)
            )
            actual = (
                arena.structures.evaluate_atom(anchor, inputs),
                tuple(
                    arena.structures.evaluate_atom(item, inputs) for item in selected
                ),
            )
            assert actual == (initial, values)
            observed.add(actual)
    assert len(
        observed
    ) == codec.anchor_cardinality * codec.continuation_cardinality ** len(
        codec.component_ports
    )
    # No compiled action, source cell, or expression carries a realized future value.
    assert len(arena.records) == 1
    assert all(row.accounting_delta == 0 for row in runtime.ledger.inventory())


def test_unused_storage_codes_decode_to_zero_without_changing_kernel_domains() -> None:
    runtime, action = tiny()
    arena = codec_arena(runtime)
    codec = arena.compile(runtime.actions.compose(action, action), 1)
    argument = arena.structures.bits.constant(
        FunctionSignature((), AtomSort("argument", 2)), 0
    )
    selected = arena.evaluate_continuation(codec, argument)
    values = {port.variable: 0 for port in codec.ports}
    values[codec.component_ports[1].variable] = 3
    assert arena.structures.evaluate_atom(arena.anchor(codec), values) == 0
    assert arena.structures.evaluate_atom(selected, values) == 0
    values[codec.component_ports[0].variable] = 3
    values[codec.anchor_port.variable] = 3
    assert arena.structures.evaluate_atom(arena.anchor(codec), values) == 0
    assert arena.structures.evaluate_atom(selected, values) == 0
    # Kernel-domain input admission retains cardinality3 and rejects code3.
    from number_compiler.arithmetic.functions.finite_function_types import FinitePort

    original = FinitePort(PortVariable(0, 0, "original-kernel", 0), 3)
    variable = arena.structures.bits.variable(
        (original,), original, AtomSort("kernel-state", 3)
    )
    assert arena.structures.bits.evaluate(variable, {original.variable: 3}) is None


def test_primitive_codec_is_one_numeric_anchor_port() -> None:
    runtime, action = tiny()
    arena = codec_arena(runtime)
    codec = arena.compile(action, 1)
    assert codec.component_ports == () and codec.argument_port is None
    assert arena.anchor(codec) == codec.structure
    for q in range(4):
        assert arena.structures.evaluate_atom(
            codec.structure, {codec.anchor_port.variable: q}
        ) == (q if q < 3 else 0)


def test_warm_codec_never_constructs_new_semantic_nodes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, action = tiny()
    arena = codec_arena(runtime)
    paired = runtime.actions.compose(action, action)
    codec = arena.compile(paired, 0)

    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("warm codec rebuilt its selector circuit")

    monkeypatch.setattr(
        "number_compiler.hashlife.interfaces.semantic_state_codec._Builder", forbidden
    )
    assert arena.compile(paired, 0) is codec
    assert runtime.ledger.counters["semantic_state_codec_hits"] == 1


@pytest.mark.parametrize(
    "field,value",
    [
        ("local_id", True),
        ("local_id", -1),
        ("local_id", 0.0),
        ("owner", ArenaToken()),
        ("kind", "other"),
    ],
)
def test_foreign_forged_actions_reject_before_warm_mutation(
    field: Literal["kind"] | Literal["local_id"] | Literal["owner"],
    value: ArenaToken | Literal["other"] | bool | float | int,
) -> None:
    runtime, action = tiny()
    arena = codec_arena(runtime)
    arena.compile(action, 0)
    forged = object.__new__(ActionProgramID)
    for name in ("owner", "kind", "local_id"):
        object.__setattr__(
            forged, name, value if name == field else getattr(action, name)
        )
    before = runtime.ledger.snapshot()
    with pytest.raises((TypeError, ValueError)):
        arena.compile(forged, 0)
    assert runtime.ledger.snapshot() == before


def test_higher_domain_and_forged_metadata_reject_before_allocation() -> None:
    runtime, action = tiny()
    arena = codec_arena(runtime)
    paired = runtime.actions.compose(action, action)
    higher = runtime.actions.compose(paired, paired)
    codec = arena.compile(paired, 0)
    before = runtime.ledger.snapshot()
    with pytest.raises(ValueError, match="composed function domain"):
        arena.compile(higher, 0)
    with pytest.raises(ValueError, match="not issued"):
        arena.anchor(replace(codec))
    with pytest.raises(ValueError):
        arena.compile(action, True)
    assert runtime.ledger.snapshot() == before


def test_parent_metadata_and_all_semantic_nodes_publish_atomically() -> None:
    runtime, action = tiny()
    arena = codec_arena(runtime)
    paired = runtime.actions.compose(action, action)
    before = runtime.ledger.snapshot()
    # One slot permits metadata alone but cannot permit its semantic graph.
    runtime.ledger.tighten_limits(None, before.entries + 1)
    with pytest.raises(BlockContextBudgetExceeded):
        arena.compile(paired, 1)
    after = runtime.ledger.snapshot()
    assert (
        after.entries,
        after.nodes,
        after.peak_entries,
        after.peak_nodes,
        after.inventory,
    ) == (
        before.entries,
        before.nodes,
        before.peak_entries,
        before.peak_nodes,
        before.inventory,
    )
    assert (
        not arena.records
        and not arena.structures.nodes
        and not arena.structures.bits.nodes
    )
    assert not arena.structures.functions.nodes


@pytest.mark.parametrize("side,expected", [(0, 546), (1, 357)])
def test_verified_c4_pair_codec_uses_fixed_primitive_component_bits(
    side: int, expected: int
) -> None:
    runtime, action = machine(PhysicalCollatzFourBlockEffect())
    arena = codec_arena(runtime)
    codec = arena.compile(
        runtime.actions.compose(action, action), side, PortVariable(0, 0, "c4-pair", 0)
    )
    assert codec.encoded_bits == expected
    assert len(codec.component_ports) == (90 if side == 0 else 50)
    assert len(arena.structures.nodes) == 4
    assert len(arena.structures.bits.nodes) == 2
    assert len(arena.structures.functions.nodes) < 100_000
    assert len(arena.records) == 1


def test_unused_storage_codes_have_identical_reduced_decoded_function_ids() -> None:
    runtime, action = tiny()
    arena = codec_arena(runtime)
    codec = arena.compile(runtime.actions.compose(action, action), 1)

    def decoded(code: int) -> StructureID:
        replacements = {
            port.variable: arena.structures.bits.constant(
                FunctionSignature((), AtomSort("storage-code", port.cardinality)), code
            )
            for port in codec.ports
        }
        return arena.structures.substitute(codec.structure, replacements)

    # Every anchor/entry has original cardinality3 but storage cardinality4.
    assert decoded(3) == decoded(0)
    assert decoded(1) != decoded(0)


def test_descriptor_admits_without_registering_stores_or_spending_budget() -> None:
    from number_compiler.hashlife.interfaces.semantic_state_codec import describe_state

    runtime, action = tiny()
    paired = runtime.actions.compose(action, action)
    before = runtime.ledger.snapshot()
    runtime.ledger.tighten_limits(before.nodes, before.entries)
    spec = describe_state(runtime, paired, 1)
    assert spec.anchor_cardinality == 3
    assert tuple(port.cardinality for port in spec.ports) == (4, 4, 4)
    assert runtime.ledger.snapshot() == before
