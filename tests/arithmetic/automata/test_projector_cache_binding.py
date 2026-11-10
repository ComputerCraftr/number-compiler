from __future__ import annotations

import gc
from collections.abc import Callable
from copy import copy, deepcopy
from pickle import dumps
from weakref import ref

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import (
    BimachineSLPProjector,
    SLPArena,
    SLPNode,
)
from number_compiler.arithmetic.automata.transducer import (
    DFA,
    LazyBimachine,
    build_pair_step_bimachine,
    encode_pair_half,
    end_tag,
    parity_tag,
)
from number_compiler.arithmetic.functions.residual import minimize_bimachine
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList

ProjectorCacheStores = tuple[
    OwnedMemo[tuple[int, int], int | None],
    OwnedMemo[tuple[int, int], int | None],
    OwnedMemo[tuple[int, int, int], int],
    OwnedMemo[tuple[int, int, int], int | None],
    OwnedMemo[tuple[int, int, int], int | None],
]


def _new_binding() -> tuple[
    ResourceLedger,
    LedgerSLPArena,
    BimachineSLPProjector,
    ProjectorCacheStores,
]:
    ledger = ResourceLedger()
    arena = LedgerSLPArena(ledger, "projector-test", "test")
    machine = minimize_bimachine(
        build_pair_step_bimachine(10), cache_outputs=False
    ).machine
    stores: ProjectorCacheStores = (
        OwnedMemo(ledger, ledger.register("projector-forward", "test_cache")),
        OwnedMemo(ledger, ledger.register("projector-reverse", "test_cache")),
        OwnedMemo(ledger, ledger.register("projector-block", "test_cache")),
        OwnedMemo(ledger, ledger.register("projector-forward-power", "test_cache")),
        OwnedMemo(ledger, ledger.register("projector-reverse-power", "test_cache")),
    )
    return ledger, arena, BimachineSLPProjector(machine, arena), stores


def _bind(
    projector: BimachineSLPProjector,
    stores: ProjectorCacheStores,
) -> None:
    forward, reverse, block, forward_power, reverse_power = stores
    projector.bind_cache_stores(
        forward=forward,
        reverse=reverse,
        block=block,
        forward_power=forward_power,
        reverse_power=reverse_power,
    )


def _dispose(arena: LedgerSLPArena, stores: ProjectorCacheStores) -> None:
    for store in stores:
        store.dispose()
    arena.dispose()
    assert arena.ledger.entries == 0
    assert arena.ledger.nodes == 0


def _assert_unbound(
    projector: BimachineSLPProjector,
    stores: ProjectorCacheStores,
) -> None:
    forward, reverse, block, forward_power, reverse_power = stores
    assert not projector.has_exact_owned_cache_binding(
        forward=forward,
        reverse=reverse,
        block=block,
        forward_power=forward_power,
        reverse_power=reverse_power,
    )


def _fail_node_rollback_after_delete_once(
    arena: LedgerSLPArena,
    monkeypatch: pytest.MonkeyPatch,
    message: str,
) -> None:
    node_store = arena.audit_snapshot().node_store
    original_rollback: Callable[[LedgerList[SLPNode], int], None] = LedgerList[
        SLPNode
    ].rollback_unpublished
    failed = False

    def fail_after_delete(self: LedgerList[SLPNode], size: int) -> None:
        nonlocal failed
        original_rollback(self, size)
        if self is not node_store:
            return
        if not failed:
            failed = True
            raise RuntimeError(message)

    monkeypatch.setattr(LedgerList, "rollback_unpublished", fail_after_delete)


def _symbol_state_machine() -> LazyBimachine:
    alphabet = (1, 2, 3)
    left = DFA(
        alphabet,
        0,
        {(0, 1): 1, (0, 2): 2, (0, 3): 3},
        (0, 1, 2, 3),
    )
    right = DFA(
        alphabet,
        0,
        {(0, symbol): 0 for symbol in alphabet},
        (0,),
        right=True,
    )
    return LazyBimachine(
        10,
        alphabet,
        left,
        right,
        lambda _left_state, symbol, _right_state: (symbol,),
        cache_enabled=False,
    )


def test_projector_cache_binding_rejects_populated_private_cache() -> None:
    _, arena, projector, stores = _new_binding()
    try:
        root = arena.word(encode_pair_half(0, (1, 2, 3), 10))
        projector.forward(root, projector.machine.left.start)

        with pytest.raises(ValueError, match="already in use"):
            _bind(projector, stores)
    finally:
        _dispose(arena, stores)


def test_projector_claims_empty_stores_exclusively_and_survives_clear() -> None:
    _, arena, first, stores = _new_binding()
    second = BimachineSLPProjector(first.machine, arena)
    third = BimachineSLPProjector(first.machine, arena)
    try:
        _bind(first, stores)
        first_claim = first.audit_cache_binding_identity
        assert first_claim is not None
        views = first.audit_cache_stores
        assert all(
            view.owner_snapshot is not None
            and view.owner_snapshot.consumer_claimed
            and view.owner_snapshot.consumer_claim_committed
            and view.owner_snapshot.consumer_claim_identity is first_claim
            for view in views
        )

        with pytest.raises(ValueError, match="owner audit"):
            _bind(third, stores)
        assert all(len(store) == 0 for store in stores)

        root = arena.word(encode_pair_half(0, (1, 2, 3), 10))
        first.forward(root, first.machine.left.start)
        assert any(len(store) > 0 for store in stores)
        first.clear_caches()
        assert all(len(store) == 0 for store in stores)

        # A failed shared-store bind leaves the second projector standalone.
        second.forward(root, second.machine.left.start)
        assert all(len(store) == 0 for store in stores)

        for view in first.audit_cache_stores:
            assert view.owner_snapshot is not None
            assert view.owner_snapshot.consumer_claim_committed
            assert view.owner_snapshot.consumer_claim_identity is first_claim
        with pytest.raises(ValueError, match="owner audit"):
            _bind(third, stores)
    finally:
        _dispose(arena, stores)


def test_projector_claim_rolls_back_late_store_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, arena, projector, stores = _new_binding()
    claims = 0

    def fail_third_claim(
        self: OwnedMemo[object, object], name: str, value: object
    ) -> None:
        nonlocal claims
        if name == "_consumer_claim":
            claims += 1
            if claims == 3:
                raise RuntimeError("injected late memo claim failure")
        object.__setattr__(self, name, value)

    try:
        monkeypatch.setattr(OwnedMemo, "__setattr__", fail_third_claim)
        with pytest.raises(RuntimeError, match="late memo claim"):
            _bind(projector, stores)
        monkeypatch.undo()

        assert projector.audit_cache_binding_identity is None
        assert all(
            not store.audit_snapshot().consumer_claimed
            and not store.audit_snapshot().consumer_claim_committed
            and store.audit_snapshot().consumer_claim_identity is None
            for store in stores
        )

        _bind(projector, stores)
        claim = projector.audit_cache_binding_identity
        assert claim is not None
        assert all(
            store.audit_snapshot().consumer_claim_identity is claim
            and store.audit_snapshot().consumer_claim_committed
            for store in stores
        )
    finally:
        _dispose(arena, stores)


def test_committed_projector_claim_is_not_released_by_memo_disposal() -> None:
    _, arena, projector, stores = _new_binding()
    second = BimachineSLPProjector(projector.machine, arena)
    try:
        _bind(projector, stores)
        claim = projector.audit_cache_binding_identity
        assert claim is not None

        for store in stores:
            store.dispose()
        assert all(
            store.audit_snapshot().consumer_claimed
            and store.audit_snapshot().consumer_claim_committed
            and store.audit_snapshot().consumer_claim_identity is claim
            for store in stores
        )
        with pytest.raises(RuntimeError, match="disposed"):
            _bind(second, stores)
    finally:
        _dispose(arena, stores)


def test_projector_claim_cannot_be_copied_to_another_consumer() -> None:
    _, arena, first, stores = _new_binding()
    foreign = BimachineSLPProjector(first.machine, arena)
    try:
        _bind(first, stores)
        for name, store in zip(
            ("_fwd", "_rev", "_block", "_fwd_power", "_rev_power"),
            stores,
            strict=True,
        ):
            object.__setattr__(foreign, name, store)
        object.__setattr__(
            foreign, "_cache_consumer_claim", first.audit_cache_binding_identity
        )
        object.__setattr__(foreign, "_cache_stores_bound", True)

        assert not foreign.has_exact_owned_cache_binding(
            forward=stores[0],
            reverse=stores[1],
            block=stores[2],
            forward_power=stores[3],
            reverse_power=stores[4],
        )
    finally:
        _dispose(arena, stores)


def test_projector_claim_does_not_keep_consumer_alive() -> None:
    _, arena, projector, stores = _new_binding()
    try:
        _bind(projector, stores)
        projector_reference = ref(projector)
        del projector
        gc.collect()

        assert projector_reference() is None
        assert all(store.audit_snapshot().consumer is None for store in stores)
        assert all(store.audit_snapshot().consumer_claim_committed for store in stores)
    finally:
        _dispose(arena, stores)


def test_projector_binding_rejects_foreign_memos_and_disposed_arena() -> None:
    _, arena, projector, stores = _new_binding()
    _, foreign_arena, _, foreign_stores = _new_binding()
    try:
        with pytest.raises(ValueError, match="another ledger"):
            _bind(projector, foreign_stores)

        arena.dispose()
        with pytest.raises(ValueError, match="disposed"):
            _bind(projector, stores)
    finally:
        _dispose(arena, stores)
        _dispose(foreign_arena, foreign_stores)


def _bind_test_word(
    arena: LedgerSLPArena,
    projector: BimachineSLPProjector,
    stores: ProjectorCacheStores,
) -> int:
    _bind(projector, stores)
    return arena.word(encode_pair_half(0, (1, 2, 3), 10))


def test_projector_rejects_machine_retarget_after_warm_cache() -> None:
    _, arena, projector, stores = _new_binding()
    try:
        root = _bind_test_word(arena, projector, stores)
        state = projector.machine.left.start
        projector.forward(root, state)
        assert len(stores[0]) > 0

        replacement = minimize_bimachine(
            build_pair_step_bimachine(10), cache_outputs=False
        ).machine
        assert replacement is not projector.machine
        projector.machine = replacement

        _assert_unbound(projector, stores)
        with pytest.raises(RuntimeError, match="authority changed"):
            projector.forward(root, state)

        projector.clear_caches()
        assert all(len(store) == 0 for store in stores)
        with pytest.raises(RuntimeError, match="authority changed"):
            projector.forward(root, state)
    finally:
        _dispose(arena, stores)


def test_projector_rejects_arena_retarget_after_warm_block_cache() -> None:
    ledger, arena, projector, stores = _new_binding()
    foreign_arena = LedgerSLPArena(ledger, "projector-foreign", "test")
    try:
        root = _bind_test_word(arena, projector, stores)
        left = projector.machine.left.start
        right = projector.machine.right.start
        projector.block(root, left, right)
        assert len(stores[2]) > 0

        projector.arena = foreign_arena

        _assert_unbound(projector, stores)
        with pytest.raises(RuntimeError, match="authority changed"):
            projector.block(root, left, right)

        projector.clear_caches()
        assert all(len(store) == 0 for store in stores)
        with pytest.raises(RuntimeError, match="authority changed"):
            projector.block(root, left, right)
    finally:
        foreign_arena.dispose()
        _dispose(arena, stores)


def test_unbound_projector_requires_clear_after_ledgered_id_reuse() -> None:
    ledger = ResourceLedger()
    arena = LedgerSLPArena(ledger, "standalone-projector", "test")
    projector = BimachineSLPProjector(_symbol_state_machine(), arena)
    try:
        original_root = arena.terminal(1)
        assert original_root == 1
        assert projector.forward(original_root, 0) == 1
        original_generation = arena.node_id_generation

        arena.rollback_unpublished_suffix(original_root)
        assert arena.node_id_generation > original_generation
        reused_root = arena.terminal(3)
        assert reused_root == original_root
        with pytest.raises(RuntimeError, match="node IDs changed"):
            projector.forward(reused_root, 0)

        projector.clear_caches()
        assert projector.forward(reused_root, 0) == 3
    finally:
        arena.dispose()
    assert ledger.entries == 0
    assert ledger.nodes == 0


def test_projector_rejects_cached_hit_after_standalone_arena_clear() -> None:
    arena = SLPArena()
    projector = BimachineSLPProjector(_symbol_state_machine(), arena)
    root = arena.terminal(1)
    assert projector.forward(root, 0) == 1
    original_generation = arena.node_id_generation

    arena.clear()
    assert arena.node_id_generation > original_generation
    with pytest.raises(RuntimeError, match="node IDs changed"):
        projector.forward(root, 0)


def test_projector_rejects_same_id_standalone_node_replacement() -> None:
    arena = SLPArena()
    projector = BimachineSLPProjector(_symbol_state_machine(), arena)
    root = arena.terminal(1)
    assert projector.forward(root, 0) == 1
    generation = arena.node_id_generation

    arena.nodes[1] = SLPNode(1, "TERM", 1, symbol=3)
    assert arena.node_id_generation > generation
    assert arena.node_storage_poisoned
    projector.clear_caches()
    with pytest.raises(RuntimeError, match="node IDs changed"):
        projector.forward(root, 0)
    with pytest.raises(RuntimeError, match="stale interners"):
        BimachineSLPProjector(_symbol_state_machine(), arena)
    with pytest.raises(RuntimeError, match="canonical interners are stale"):
        arena.terminal(3)
    with pytest.raises(AttributeError, match="storage identity is immutable"):
        arena.nodes = []


def test_projector_pins_exact_node_storage_against_forced_replacement() -> None:
    arena = SLPArena()
    projector = BimachineSLPProjector(_symbol_state_machine(), arena)
    root = arena.word((1, 2))
    projector.forward(root, 0)
    generation = arena.node_id_generation

    object.__setattr__(arena, "nodes", list(arena.nodes))

    assert arena.node_id_generation == generation
    with pytest.raises(RuntimeError, match="authority changed"):
        projector.forward(root, 0)
    with pytest.raises(RuntimeError, match="canonical interners are stale"):
        arena.terminal(3)
    with pytest.raises(RuntimeError, match="stale interners"):
        BimachineSLPProjector(_symbol_state_machine(), arena)
    projector.clear_caches()
    with pytest.raises(RuntimeError, match="authority changed"):
        projector.forward(root, 0)


def test_ledgered_projector_requires_clear_after_rollback_reuses_node_ids() -> None:
    _, arena, projector, stores = _new_binding()
    try:
        _bind(projector, stores)
        original_root = arena.terminal(10)
        assert original_root == 1
        state = projector.machine.left.start
        projector.forward(original_root, state)
        original_generation = arena.node_id_generation

        arena.rollback_unpublished_suffix(original_root)
        assert arena.node_id_generation > original_generation
        reused_root = arena.terminal(11)
        assert reused_root == original_root
        with pytest.raises(RuntimeError, match="node IDs changed"):
            projector.forward(reused_root, state)

        assert not projector.has_exact_owned_cache_binding(
            forward=stores[0],
            reverse=stores[1],
            block=stores[2],
            forward_power=stores[3],
            reverse_power=stores[4],
        )
        projector.clear_caches()
        assert projector.forward(reused_root, state) == projector.machine.left.step(
            state, 11
        )
        assert projector.has_exact_owned_cache_binding(
            forward=stores[0],
            reverse=stores[1],
            block=stores[2],
            forward_power=stores[3],
            reverse_power=stores[4],
        )
    finally:
        _dispose(arena, stores)


def test_ledgered_arena_generation_invalidates_partial_but_not_noop_rollback() -> None:
    ledger = ResourceLedger()
    arena = LedgerSLPArena(ledger, "rollback-generation", "test")
    projector = BimachineSLPProjector(_symbol_state_machine(), arena)
    try:
        root = arena.terminal(1)
        assert projector.forward(root, 0) == 1
        generation = arena.node_id_generation

        arena.rollback_unpublished_suffix(len(arena.nodes))
        assert arena.node_id_generation == generation

        def fail_before_remove(_node_id: int) -> None:
            raise RuntimeError("injected rollback callback failure")

        with pytest.raises(RuntimeError, match="rollback callback failure"):
            arena.rollback_unpublished_suffix(root, before_remove=fail_before_remove)
        assert len(arena.nodes) == root + 1
        assert arena.node_id_generation > generation
        with pytest.raises(RuntimeError, match="node IDs changed"):
            projector.forward(root, 0)

        projector.clear_caches()
        assert projector.forward(root, 0) == 1
        generation = arena.node_id_generation
        arena.dispose()
        assert arena.node_id_generation > generation
        with pytest.raises(ValueError, match="disposed"):
            projector.forward(root, 0)
    finally:
        arena.dispose()
    assert ledger.entries == 0
    assert ledger.nodes == 0


def test_suffix_rollback_reconciles_a_post_delete_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    arena = LedgerSLPArena(ledger, "suffix-delete-retry", "test")
    retained_error: RuntimeError | None = None

    try:
        arena.word((1, 2))
        _fail_node_rollback_after_delete_once(
            arena, monkeypatch, "injected post-delete rollback failure"
        )
        try:
            arena.rollback_unpublished_suffix(1)
        except RuntimeError as error:
            retained_error = error
        assert retained_error is not None
        assert retained_error.__traceback__ is not None
        assert len(arena.nodes) == 3
        assert ledger.account_usage(arena.owners[0]) == (3, 3)

        monkeypatch.undo()
        arena.rollback_unpublished_suffix(1)
        assert len(arena.nodes) == 1
        assert ledger.account_usage(arena.owners[0]) == (1, 1)
    finally:
        monkeypatch.undo()
        arena.dispose()
    assert ledger.entries == 0
    assert ledger.nodes == 0


def test_arena_dispose_reconciles_a_post_delete_failure_and_retries(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    arena = LedgerSLPArena(ledger, "dispose-delete-retry", "test")
    retained_error: RuntimeError | None = None

    try:
        arena.word((1, 2))
        _fail_node_rollback_after_delete_once(
            arena, monkeypatch, "injected dispose post-delete failure"
        )
        try:
            arena.dispose()
        except RuntimeError as error:
            retained_error = error
        assert retained_error is not None
        assert retained_error.__traceback__ is not None
        assert len(arena.nodes) == 0
        assert ledger.account_usage(arena.owners[0]) == (0, 0)
        assert not ledger.account_status(arena.owners[0]).disposed

        monkeypatch.undo()
        arena.dispose()
        assert ledger.account_status(arena.owners[0]).disposed
    finally:
        monkeypatch.undo()
        arena.dispose()
    assert ledger.entries == 0
    assert ledger.nodes == 0


def test_failed_unappended_node_release_is_reconciled_on_retry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    arena = LedgerSLPArena(ledger, "unappended-node-retry", "test")
    failed_append = False
    retained_error: RuntimeError | None = None

    try:
        node_store = arena.audit_snapshot().node_store
        original_append: Callable[[LedgerList[SLPNode], SLPNode], None] = LedgerList[
            SLPNode
        ].append
        original_release = ledger.release

        def fail_append(self: LedgerList[SLPNode], value: SLPNode) -> None:
            nonlocal failed_append
            if self is node_store:
                failed_append = True
                raise RuntimeError("injected node append failure")
            original_append(self, value)

        def fail_release(
            owner: int,
            *,
            entries: int = 0,
            nodes: int = 0,
        ) -> None:
            if owner == arena.owners[0] and entries == 1 and nodes == 1:
                raise RuntimeError("injected reserved-node release failure")
            original_release(owner, entries=entries, nodes=nodes)

        monkeypatch.setattr(LedgerList, "append", fail_append)
        monkeypatch.setattr(ledger, "release", fail_release)
        try:
            arena.terminal(7)
        except RuntimeError as error:
            retained_error = error
        assert failed_append
        assert retained_error is not None
        assert retained_error.__traceback__ is not None
        assert len(arena.nodes) == 1
        assert ledger.account_usage(arena.owners[0]) == (2, 2)

        monkeypatch.undo()
        arena.rollback_unpublished_suffix(1)
        assert ledger.account_usage(arena.owners[0]) == (1, 1)
        assert arena.terminal(7) == 1

        release_failed_after_commit = False

        def fail_after_reserved_release(
            owner: int,
            *,
            entries: int = 0,
            nodes: int = 0,
        ) -> None:
            nonlocal release_failed_after_commit
            original_release(owner, entries=entries, nodes=nodes)
            if (
                owner == arena.owners[0]
                and entries == 1
                and nodes == 1
                and not release_failed_after_commit
            ):
                release_failed_after_commit = True
                raise RuntimeError("injected post-release failure")

        monkeypatch.setattr(LedgerList, "append", fail_append)
        monkeypatch.setattr(ledger, "release", fail_after_reserved_release)
        retained_error = None
        try:
            arena.terminal(8)
        except RuntimeError as error:
            retained_error = error
        assert release_failed_after_commit
        assert retained_error is not None
        assert retained_error.__traceback__ is not None
        assert ledger.account_usage(arena.owners[0]) == (2, 2)

        monkeypatch.undo()
        arena.rollback_unpublished_suffix(len(arena.nodes))
        assert ledger.account_usage(arena.owners[0]) == (2, 2)
        assert arena.terminal(8) == 2
    finally:
        monkeypatch.undo()
        arena.dispose()
    assert ledger.entries == 0
    assert ledger.nodes == 0


def test_disposed_arena_clear_does_not_refresh_projector_generation() -> None:
    _, arena, projector, stores = _new_binding()
    try:
        _bind(projector, stores)
        root = arena.terminal(10)
        projector.forward(root, projector.machine.left.start)
        arena.dispose()

        projector.clear_caches()
        assert all(len(store) == 0 for store in stores)
        assert not projector.has_exact_owned_cache_binding(
            forward=stores[0],
            reverse=stores[1],
            block=stores[2],
            forward_power=stores[3],
            reverse_power=stores[4],
        )
        with pytest.raises(ValueError, match="disposed"):
            projector.forward(root, projector.machine.left.start)

        for store in stores:
            store.dispose()
        assert projector.has_exact_owned_cache_binding(
            forward=stores[0],
            reverse=stores[1],
            block=stores[2],
            forward_power=stores[3],
            reverse_power=stores[4],
        )
    finally:
        _dispose(arena, stores)


def test_projector_clear_quarantine_remains_after_full_disposal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, arena, projector, stores = _new_binding()
    try:
        _bind(projector, stores)
        root = arena.terminal(10)
        projector.forward(root, projector.machine.left.start)

        def fail_clear() -> None:
            raise RuntimeError("injected disposed-owner clear failure")

        monkeypatch.setattr(stores[0], "clear", fail_clear)
        with pytest.raises(RuntimeError, match="disposed-owner clear failure"):
            projector.clear_caches()
        monkeypatch.undo()

        for store in stores:
            store.dispose()
        arena.dispose()
        assert projector.has_exact_owned_cache_binding(
            forward=stores[0],
            reverse=stores[1],
            block=stores[2],
            forward_power=stores[3],
            reverse_power=stores[4],
        )
        with pytest.raises(RuntimeError, match="retry clearing"):
            projector.forward(root, projector.machine.left.start)
    finally:
        monkeypatch.undo()
        _dispose(arena, stores)


def test_failed_cache_clear_quarantines_then_retry_reconciles_ledger(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, arena, projector, stores = _new_binding()
    repeated = arena.repeat(arena.word((10, 11)), 5)
    source = arena.concat_many(
        (
            arena.terminal(parity_tag(0, 10)),
            repeated,
            arena.terminal(end_tag(10)),
        )
    )
    try:
        _bind(projector, stores)
        publication_checkpoint = len(arena.nodes)
        expected = projector.apply(source)
        expected_symbols = arena.materialize(expected)
        assert all(len(store) > 0 for store in stores)
        arena.rollback_unpublished_suffix(publication_checkpoint)
        assert not projector.has_exact_owned_cache_binding(
            forward=stores[0],
            reverse=stores[1],
            block=stores[2],
            forward_power=stores[3],
            reverse_power=stores[4],
        )

        first_clear = stores[0].clear
        failed = False

        def fail_first_clear() -> None:
            nonlocal failed
            if not failed:
                failed = True
                raise RuntimeError("injected first cache-clear failure")
            first_clear()

        monkeypatch.setattr(stores[0], "clear", fail_first_clear)
        with pytest.raises(RuntimeError, match="first cache-clear failure"):
            projector.clear_caches()
        monkeypatch.undo()

        assert len(stores[0]) > 0
        assert stores[0].ledger.account_usage(stores[0].owner) == (
            len(stores[0]),
            0,
        )
        assert all(len(store) == 0 for store in stores[1:])
        assert all(
            store.ledger.account_usage(store.owner) == (len(store), 0)
            for store in stores[1:]
        )
        assert not projector.has_exact_owned_cache_binding(
            forward=stores[0],
            reverse=stores[1],
            block=stores[2],
            forward_power=stores[3],
            reverse_power=stores[4],
        )
        with pytest.raises(RuntimeError, match="retry clearing"):
            projector.apply(source)

        projector.clear_caches()
        assert all(len(store) == 0 for store in stores)
        assert all(
            store.ledger.account_usage(store.owner) == (0, 0) for store in stores
        )
        actual = projector.apply(source)
        assert arena.materialize(actual) == expected_symbols
        assert all(
            store.ledger.account_usage(store.owner) == (len(store), 0)
            for store in stores
        )
    finally:
        _dispose(arena, stores)


def test_failed_interner_publication_releases_node_before_id_reuse(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    arena = LedgerSLPArena(ledger, "interner-publication-retry", "test")
    left = arena.terminal(1)
    right = arena.terminal(2)
    checkpoint = len(arena.nodes)
    snapshot = arena.audit_snapshot()
    memo = snapshot.concat_memo
    store = memo.audit_snapshot().container
    publication_error = RuntimeError("injected interner failure after insert")
    first_release_error = RuntimeError("injected interner release failure")
    original_setitem: Callable[[LedgerDict[object, object], object, object], None] = (
        LedgerDict[object, object].__setitem__
    )
    original_note = ledger.note_store_mutation
    original_release = ledger.release
    note_armed = False
    release_failures = [first_release_error]

    def fail_rollback_note() -> None:
        nonlocal note_armed
        if note_armed:
            note_armed = False
            raise RuntimeError("injected interner delete callback failure")
        original_note()

    def insert_then_fail(
        mapping: LedgerDict[object, object], key: object, value: object
    ) -> None:
        nonlocal note_armed
        original_setitem(mapping, key, value)
        if mapping is store and key == (left, right):
            note_armed = True
            raise publication_error

    def fail_release(owner_id: int, *, entries: int = 0, nodes: int = 0) -> None:
        if owner_id == memo.owner and entries == 1 and nodes == 0 and release_failures:
            raise release_failures.pop(0)
        original_release(owner_id, entries=entries, nodes=nodes)

    monkeypatch.setattr(ledger, "note_store_mutation", fail_rollback_note)
    monkeypatch.setattr(LedgerDict, "__setitem__", insert_then_fail)
    monkeypatch.setattr(ledger, "release", fail_release)
    try:
        with pytest.raises(RuntimeError, match="failure after insert") as captured:
            arena.concat(left, right)

        assert captured.value is publication_error
        assert captured.value.__cause__ is first_release_error
        assert len(arena.nodes) == checkpoint
        assert memo.get((left, right)) is None
        assert ledger.account_usage(memo.owner) == (1, 0)

        monkeypatch.undo()
        repeated = arena.concat(left, right)
        assert repeated == checkpoint
        assert arena.concat(left, right) == repeated
        assert arena.materialize(repeated) == (1, 2)
        memo.clear()
        assert ledger.account_usage(memo.owner) == (0, 0)
    finally:
        monkeypatch.undo()
        arena.dispose()
    assert ledger.entries == 0
    assert ledger.nodes == 0


def test_interner_keeps_node_if_exact_failed_store_rollback_refuses(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    arena = LedgerSLPArena(ledger, "interner-publication-quarantine", "test")
    left = arena.terminal(3)
    right = arena.terminal(4)
    checkpoint = len(arena.nodes)
    memo = arena.audit_snapshot().concat_memo
    store = memo.audit_snapshot().container
    publication_error = RuntimeError("injected publication interruption")
    cleanup_error = RuntimeError("injected exact rollback refusal")
    original_setitem: Callable[[LedgerDict[object, object], object, object], None] = (
        LedgerDict[object, object].__setitem__
    )
    original_rollback = LedgerDict[object, object].rollback_inserted_value

    def insert_then_fail(
        mapping: LedgerDict[object, object], key: object, value: object
    ) -> None:
        original_setitem(mapping, key, value)
        if mapping is store and key == (left, right):
            raise publication_error

    def refuse_rollback(
        mapping: LedgerDict[object, object], key: object, value: object
    ) -> bool:
        if mapping is store and key == (left, right):
            raise cleanup_error
        return original_rollback(mapping, key, value)

    monkeypatch.setattr(LedgerDict, "__setitem__", insert_then_fail)
    monkeypatch.setattr(LedgerDict, "rollback_inserted_value", refuse_rollback)
    try:
        with pytest.raises(RuntimeError, match="publication interruption") as captured:
            arena.concat(left, right)

        assert captured.value is publication_error
        assert captured.value.__cause__ is cleanup_error
        assert len(arena.nodes) == checkpoint + 1
        assert memo.get((left, right)) == checkpoint
        assert arena.concat(left, right) == checkpoint
        assert arena.nodes[checkpoint].kind == "CONCAT"
    finally:
        monkeypatch.undo()
        arena.dispose()
    assert ledger.entries == 0
    assert ledger.nodes == 0


@pytest.mark.parametrize("clone", (copy, deepcopy, dumps))
def test_slp_arena_cannot_clone_mutation_authority(
    clone: Callable[[SLPArena], object],
) -> None:
    arena = SLPArena()
    root = arena.terminal(1)
    projector = BimachineSLPProjector(_symbol_state_machine(), arena)
    assert projector.forward(root, 0) == 1
    generation = arena.node_id_generation
    with pytest.raises(TypeError, match="cannot be copied or serialized"):
        clone(arena)
    assert arena.node_id_generation == generation
    assert projector.forward(root, 0) == 1
