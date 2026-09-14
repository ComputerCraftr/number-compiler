"""Actual retained stores reject builtin and seal-removal bypasses."""

from array import array
from collections.abc import Callable
from functools import partial
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
)
from number_compiler.hashlife.actions.lazy_compiler import (
    LazyCompiler,
    ProgramComposition,
)
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect


def test_builtin_mutation_descriptors_cannot_bypass_zero_reservations_or_recycle_ids() -> (
    None
):
    ledger = ResourceLedger(max_nodes=0, max_cache_entries=0)
    sequence: LedgerList[object]
    sequence = ledger.make_list(ledger.register("nodes", "action_program"))
    mapping: LedgerDict[object, object]
    mapping = ledger.make_dict(ledger.register("keys", "action_interner"))
    before = ledger.snapshot()
    operations: tuple[Callable[[], object], ...] = (
        lambda: list.append(cast("list[int]", sequence), 42),
        lambda: list.clear(cast("list[int]", sequence)),
        lambda: list.__init__(cast("list[int]", sequence), [42]),
        lambda: dict.__setitem__(cast("dict[int, int]", mapping), 0, 42),
        lambda: dict.update(cast("dict[int, int]", mapping), {0: 42}),
        lambda: dict.__init__(cast("dict[int, int]", mapping), {0: 42}),
    )
    for operation in operations:
        with pytest.raises(TypeError):
            operation()
        assert not sequence and not mapping
        assert ledger.snapshot() == before


def test_canonical_wrappers_preserve_ids_and_ownership_after_failed_mutation() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("nodes", "action_program")
    nodes: LedgerList[object]
    nodes = ledger.make_list(owner)
    ledger.reserve(owner, entries=2, nodes=2)
    nodes.extend(("first", "second"))
    before = ledger.snapshot()
    operations: tuple[Callable[[], object], ...] = (
        lambda: nodes.clear(),
        lambda: nodes.pop(),
        lambda: nodes.reverse(),
        lambda: nodes.__setitem__(0, "replacement"),
        lambda: list.__setitem__(cast("list[str]", nodes), 0, "replacement"),
        lambda: LedgerList.__init__(nodes, ledger, owner, 1, True),
        lambda: delattr(nodes, "_sealed"),
        lambda: setattr(nodes, "append_only", False),
    )
    for operation in operations:
        with pytest.raises((TypeError, AttributeError)):
            operation()
        assert tuple(nodes) == ("first", "second")
        assert ledger.snapshot() == before
    ledger.reserve(owner, entries=1, nodes=1)
    nodes.append("third")
    assert nodes[0] == "first" and nodes[2] == "third"


def test_direct_store_construction_cannot_spend_another_containers_reservation() -> (
    None
):
    ledger = ResourceLedger()
    owner = ledger.register("actual", "action_program")
    actual: LedgerList[object]
    actual = ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    counterfeit: LedgerList[object]
    counterfeit = LedgerList(ledger, owner, 1, True)
    with pytest.raises(RuntimeError, match="factory"):
        counterfeit.append(42)
    assert not actual and not counterfeit
    other = ledger.register("mapping", "query_memo")
    ledger.reserve(other, entries=1)
    fake_mapping: LedgerDict[object, object]
    fake_mapping = LedgerDict(ledger, other, 0)
    with pytest.raises(RuntimeError, match="factory"):
        fake_mapping[0] = 42


def test_public_iterators_cannot_expose_the_canonical_backing_container() -> None:
    ledger = ResourceLedger(max_nodes=1, max_cache_entries=2)
    owner = ledger.register("nodes", "action_program")
    nodes: LedgerList[object]
    nodes = ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    nodes.append("original")
    iterator = iter(nodes)
    with pytest.raises(TypeError):
        iterator.__reduce__()
    assert next(iterator) == "original"
    with pytest.raises(TypeError):
        iterator.__reduce__()
    assert tuple(nodes) == ("original",)

    mapping_owner = ledger.register("keys", "query_memo")
    mapping: LedgerDict[object, object]
    mapping = ledger.make_dict(mapping_owner)
    ledger.reserve(mapping_owner, entries=1)
    mapping["key"] = "value"
    # CPython's dictionary iterator reduction returns a key-list copy, not the
    # backing dictionary. Mutating that public copy cannot alter the store.
    copied_keys = cast("tuple[object, tuple[list[str]]]", iter(mapping).__reduce__())[
        1
    ][0]
    copied_keys.append("injected")
    assert tuple(mapping.items()) == (("key", "value"),)


@pytest.mark.parametrize("populated", (False, True))
def test_public_serialization_hooks_never_expose_live_store_backing(
    populated: bool,
) -> None:
    ledger = ResourceLedger(max_nodes=1, max_cache_entries=2)
    node_owner = ledger.register("nodes", "action_program")
    key_owner = ledger.register("keys", "query_memo")
    nodes: LedgerList[object]
    keys: LedgerDict[object, object]
    nodes, keys = ledger.make_list(node_owner), ledger.make_dict(key_owner)
    if populated:
        ledger.reserve_many(((node_owner, 1, 1), (key_owner, 1, 0)))
        nodes.append("original")
        keys[0] = "original"
    before = ledger.snapshot()
    for store in (nodes, keys):
        serializers: tuple[Callable[[], object], ...] = (
            store.__reduce__,
            partial(store.__reduce_ex__, 4),
            store.__getstate__,
            partial(object.__reduce_ex__, store, 4),
        )
        for serialize in serializers:
            with pytest.raises(TypeError, match="not serializable"):
                serialize()
        assert ledger.snapshot() == before


def test_frozen_kernel_and_program_seals_cannot_be_deleted_and_states_have_no_dict() -> (
    None
):
    atom = BaseBlockEffect(2)
    compiler = LazyCompiler(ResourceLedger())
    program = compiler.compose(atom, atom)
    finite = FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=1,
        right_count=1,
        alphabet_size=4,
        initial_left=0,
        initial_right=0,
        left_transitions=array("H", [0] * 4),
        right_transitions=array("H", [0] * 4),
        outputs=bytes(range(4)),
        kernel_name="identity",
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
    )
    assert isinstance(program, ProgramComposition)
    definitions: tuple[
        BaseBlockEffect
        | DigitNormalizeBlockEffect
        | CollatzPhysicalBlockEffect
        | FiniteBlockEffect
        | ProgramComposition,
        ...,
    ] = (
        atom,
        DigitNormalizeBlockEffect(2),
        CollatzPhysicalBlockEffect(),
        finite,
        program,
    )
    for definition in definitions:
        before = definition.canonical_key
        with pytest.raises(AttributeError):
            delattr(definition, "_sealed")
        with pytest.raises(AttributeError):
            definition.base = 17
        assert definition.canonical_key == before
        assert not hasattr(definition, "__dict__")
    assert not hasattr(atom.initial(BoundarySide.LEFT), "__dict__")
    assert not hasattr(atom.initial(BoundarySide.RIGHT), "__dict__")
