"""Negative controls for immutable semantics and the actual allocation boundary."""

from __future__ import annotations

from array import array
from collections.abc import Callable, MutableMapping
from typing import cast

import pytest

from number_compiler.arithmetic.contracts import semantic_identity
from number_compiler.arithmetic.contracts.block_effect import BoundarySide, _effect_key
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
)
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.hashlife.actions.lazy_compiler import (
    LazyCompiler,
    ProgramComposition,
)
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect


def _finite(*, flip: bool = False) -> FiniteBlockEffect:
    return FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=1,
        right_count=1,
        alphabet_size=4,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", [0] * 4),
        right_transitions=array("I", [0] * 4),
        outputs=bytes((1, 0, 2, 3) if flip else range(4)),
        kernel_name="same-name",
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
    )


@pytest.mark.parametrize(
    "atom",
    (BaseBlockEffect(10), DigitNormalizeBlockEffect(10), CollatzPhysicalBlockEffect()),
)
def test_primitive_semantics_are_deeply_cacheless_and_cannot_be_warmed_or_mutated(
    atom: BaseBlockEffect | CollatzPhysicalBlockEffect | DigitNormalizeBlockEffect,
) -> None:
    before = {name: getattr(atom, name) for name in atom.__slots__}
    left, right = atom.initial(BoundarySide.LEFT), atom.initial(BoundarySide.RIGHT)
    for symbol in (0, 1, atom.blank):
        atom.emit(left, symbol, right)
        atom.advance(BoundarySide.LEFT, left, symbol)
        atom.advance(BoundarySide.RIGHT, right, symbol)
    assert {name: getattr(atom, name) for name in atom.__slots__} == before
    assert not any(isinstance(value, (dict, list, set)) for value in before.values())
    assert atom.runtime_stats()["leaf_effect_cache_entries"] == 0
    with pytest.raises(AttributeError):
        atom.base = 7
    with pytest.raises(AttributeError):
        atom._new_cache = {}


def test_forced_digest_collision_does_not_alias_finite_or_composed_actions(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        semantic_identity,
        "_tuple_digest",
        lambda _value, _children: b"same digest for every tuple",
    )
    one, two, equal = _finite(), _finite(flip=True), _finite()
    one_identity = one.canonical_key[1]
    two_identity = two.canonical_key[1]
    assert isinstance(one_identity, SemanticIdentity)
    assert isinstance(two_identity, SemanticIdentity)
    assert one_identity.digest == two_identity.digest
    assert one_identity.behavior != two_identity.behavior
    assert one.canonical_key != two.canonical_key
    assert one.canonical_key == equal.canonical_key
    compiler = LazyCompiler(ResourceLedger())
    first, second = compiler.atom(one), compiler.atom(two)
    assert first is not second
    assert compiler.atom(equal) is first
    a, b = compiler.compose(first, first), compiler.compose(second, second)
    assert isinstance(a, ProgramComposition) and isinstance(b, ProgramComposition)
    assert a is not b and a.canonical_key != b.canonical_key


@pytest.mark.parametrize("bad", ([1, 2], {1: 2}, bytearray(b"future"), lambda: 0))
def test_semantic_keys_cannot_hide_mutable_or_executable_behavior(bad: object) -> None:
    with pytest.raises(TypeError, match="mutable or executable"):
        SemanticIdentity("digest", (bad,))


def test_factory_checks_capacity_at_every_retained_insertion() -> None:
    ledger = ResourceLedger(max_cache_entries=2)
    owner = ledger.register("memo", "query_memo")
    cache: LedgerDict[object, object]
    cache = ledger.make_dict(owner)
    writes: tuple[Callable[[], object], ...] = (
        lambda: cache.__setitem__(0, 1),
        lambda: cache.setdefault(0, 1),
        lambda: cache.update({0: 1}),
        lambda: cache.__ior__({0: 1}),
    )
    for write in writes:
        before = ledger.snapshot()
        with pytest.raises(RuntimeError, match="prior ledger reservation"):
            write()
        assert cache == {} and ledger.snapshot() == before
    ledger.reserve(owner, entries=1)
    cache[0] = 1
    before = ledger.snapshot()
    with pytest.raises(RuntimeError, match="prior ledger reservation"):
        cache.update({0: 2, 1: 3})
    assert cache == {0: 1} and ledger.snapshot() == before
    with pytest.raises(AttributeError):
        cache.owner = 3
    with pytest.raises(AttributeError):
        cache.hidden_payload = [1, 2, 3]


def test_canonical_factory_sequence_and_public_compiler_view_cannot_recycle_ids() -> (
    None
):
    ledger = ResourceLedger()
    owner = ledger.register("program", "action_program")
    nodes: LedgerList[object]
    nodes = ledger.make_list(owner)
    with pytest.raises(RuntimeError, match="prior ledger reservation"):
        nodes.append("first")
    ledger.reserve(owner, entries=2, nodes=2)
    nodes.extend(("first", "second"))
    mutations: tuple[Callable[[], object], ...] = (
        lambda: nodes.clear(),
        lambda: nodes.pop(),
        lambda: nodes.remove("first"),
        lambda: nodes.__setitem__(0, "second"),
        lambda: nodes.reverse(),
        lambda: nodes.sort(),
        lambda: nodes.__imul__(0),
        lambda: type(nodes).__init__(nodes, ledger, owner, 1, True),
    )
    for mutate in mutations:
        with pytest.raises(TypeError):
            mutate()
        assert nodes == ["first", "second"]
    compiler = LazyCompiler(ResourceLedger())
    atom = compiler.atom(BaseBlockEffect(10))
    action = compiler.compose(atom, atom)
    assert isinstance(compiler.nodes, tuple)
    with pytest.raises(TypeError):
        cast(MutableMapping[object, int], compiler.ids)[_effect_key(atom)] = (
            action.node_id
        )
    compiler.ledger.evict_query_memos()
    assert compiler.atom(action) is action


def test_memo_eviction_releases_factory_storage_and_retains_no_old_values() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("memo", "query_memo")
    memo: OwnedMemo[int, str] = OwnedMemo(ledger, owner, evictable=True)
    memo[0] = "first"
    assert ledger.entries == 1
    ledger.evict_query_memos()
    assert ledger.entries == 0 and not memo
    memo[1] = "second"
    assert tuple(memo) == (1,)
    assert ledger.inventory()[owner].accounting_delta == 0
