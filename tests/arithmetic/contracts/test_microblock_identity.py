from __future__ import annotations

from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.projection.microblock_cache import (
    ExactMicroblock,
    MicroblockCache,
    MicroblockKey,
)
from number_compiler.resources.ledger import LedgerSnapshot, ResourceLedger
from tests.support.assertions import assert_rejected_atomically


def _fixture() -> tuple[
    ResourceLedger, LazyCompiler, MicroblockCache, ActionProgramID, MicroblockKey
]:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    effect = compiler.atom(BaseBlockEffect(10))
    program = compiler.reference(effect)
    cache = MicroblockCache(ledger, compiler.token, compiler.resolve)
    key = MicroblockKey(program, 10, 0, 0, "output")
    cache.put(key, ExactMicroblock(7, 4))
    return ledger, compiler, cache, program, key


@pytest.mark.parametrize("operation", ("get", "put", "discard"))
@pytest.mark.parametrize("kind", ("foreign", "stale", "wrong-kind", "bool", "float"))
def test_microblock_rejects_invalid_program_before_warm_probe_or_mutation(
    operation: str,
    kind: str,
) -> None:
    ledger, compiler, cache, program, _warm = _fixture()
    if kind == "foreign":
        invalid = ActionProgramID(ArenaToken("foreign"), program.kind, program.local_id)
    elif kind == "stale":
        invalid = ActionProgramID(program.owner, program.kind, program.local_id + 100)
    elif kind == "wrong-kind":
        invalid = ActionProgramID(program.owner, "wrong-kind", program.local_id)
    else:
        invalid = ActionProgramID(program.owner, program.kind, program.local_id)
        object.__setattr__(invalid, "local_id", True if kind == "bool" else 0.0)
    key = MicroblockKey.__new__(MicroblockKey)
    object.__setattr__(key, "program", invalid)
    object.__setattr__(key, "radix", 10)
    object.__setattr__(key, "stage", 0)
    object.__setattr__(key, "block", 0)
    object.__setattr__(key, "kind", "output")
    before = ledger.snapshot()
    with pytest.raises((TypeError, ValueError)):
        _invoke_key_operation(cache, key, operation)
    assert ledger.snapshot() == before
    assert cache.get(_warm) == ExactMicroblock(7, 4)
    assert compiler.resolve(program) is not None


@pytest.mark.parametrize("program", (True, 0, 1.0))
def test_microblock_key_rejects_raw_integer_aliases(program: object) -> None:
    with pytest.raises(ValueError, match="invalid exact microblock key"):
        MicroblockKey(cast(ActionProgramID, program), 10, 0, 0, "output")


@pytest.mark.parametrize("source_scope", (True, 1.0))
def test_microblock_key_rejects_numeric_source_scope_aliases(
    source_scope: object,
) -> None:
    _ledger, _compiler, _cache, program, _key = _fixture()
    with pytest.raises(ValueError, match="invalid exact microblock key"):
        MicroblockKey(
            program,
            10,
            0,
            0,
            "output",
            source_scope=cast(ArenaToken | None, source_scope),
        )


def test_microblock_payload_counter_tracks_replacement_and_discard() -> None:
    ledger, _compiler, cache, _program, key = _fixture()
    assert ledger.counters["microblock_payload_bytes"] == 1
    cache.put(key, ExactMicroblock(0xFFFF, 16))
    assert cache.payload_bytes == ledger.counters["microblock_payload_bytes"] == 2
    assert ledger.counters["microblock_payload_high_water_bytes"] == 2
    cache.discard(key)
    assert cache.payload_bytes == ledger.counters["microblock_payload_bytes"] == 0
    assert ledger.counters["microblock_payload_high_water_bytes"] == 2


def test_denied_microblock_reservation_preserves_cache_and_ledger() -> None:
    ledger, _compiler, cache, program, key = _fixture()
    denied = MicroblockKey(program, 10, 0, 1, "output")
    ledger.max_cache_entries = ledger.entries
    before = ledger.snapshot()
    contents = dict(cache.blocks.items())
    with pytest.raises(Exception, match="cache budget exceeded"):
        cache.put(denied, ExactMicroblock(3, 2))
    _assert_cache_retained(cache, ledger, key, contents, before)


def test_capacity_eviction_reuses_reserved_slot_atomically(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _compiler, cache, program, first = _fixture()
    monkeypatch.setattr(cache, "MAX_ENTRIES", 1)
    ledger.max_cache_entries = ledger.entries
    second = MicroblockKey(program, 10, 0, 1, "output")
    before_entries = ledger.entries
    cache.put(second, ExactMicroblock(2, 2))
    assert cache.get(first) is None
    assert cache.get(second) == ExactMicroblock(2, 2)
    assert ledger.entries == before_entries
    assert ledger.counters["microblock_evictions"] == 1


def test_failed_publication_restores_selected_eviction_victim(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _compiler, cache, program, first = _fixture()
    monkeypatch.setattr(cache, "MAX_ENTRIES", 1)
    second = MicroblockKey(program, 10, 0, 1, "output")
    contents = dict(cache.blocks.items())
    before = ledger.snapshot()
    original_check = ledger.check_store_capacity
    calls = 0

    def fail_second_check(owner: int, entries: int, nodes: int) -> None:
        nonlocal calls
        calls += 1
        if calls == 2:
            raise RuntimeError("injected publication failure")
        original_check(owner, entries, nodes)

    monkeypatch.setattr(ledger, "check_store_capacity", fail_second_check)
    with pytest.raises(RuntimeError, match="injected publication failure"):
        cache.put(second, ExactMicroblock(2, 2))
    _assert_cache_retained(cache, ledger, first, contents, before)


@pytest.mark.parametrize("field,value", (("encoded", 4), ("bit_count", 1000)))
def test_published_payload_has_no_caller_or_returned_mutation_alias(
    field: str,
    value: int,
) -> None:
    ledger, _compiler, cache, _program, key = _fixture()
    supplied = ExactMicroblock(5, 3)
    cache.put(key, supplied)
    object.__setattr__(supplied, field, value)
    returned = cache.get(key)
    assert returned == ExactMicroblock(5, 3)
    assert returned is not supplied
    assert returned is not None
    object.__setattr__(returned, field, value)
    assert cache.get(key) == ExactMicroblock(5, 3)
    assert cache.payload_bytes == ledger.counters["microblock_payload_bytes"] == 1
    cache.discard(key)
    assert cache.payload_bytes == 0


def test_publication_snapshots_key_and_scoped_program_aliases() -> None:
    _ledger, _compiler, cache, program, _key = _fixture()
    supplied_program = ActionProgramID(program.owner, program.kind, program.local_id)
    supplied = MicroblockKey(supplied_program, 10, 0, 1, "output")
    cache.put(supplied, ExactMicroblock(0, 1))
    object.__setattr__(supplied, "block", 2)
    object.__setattr__(supplied_program, "local_id", 100)
    canonical = MicroblockKey(program, 10, 0, 1, "output")
    assert cache.get(canonical) == ExactMicroblock(0, 1)
    cache.discard(canonical)
    assert len(cache) == 1


@pytest.mark.parametrize("field,value", (("encoded", True), ("bit_count", 1000)))
def test_corrupt_stored_payload_rejected_before_hit_or_replacement(
    field: str,
    value: int,
) -> None:
    ledger, _compiler, cache, _program, key = _fixture()
    object.__setattr__(cache.blocks[key], field, value)
    before = assert_rejected_atomically(
        ledger, lambda: cache.get(key), (TypeError, ValueError)
    )
    with pytest.raises((TypeError, ValueError)):
        cache.put(key, ExactMicroblock(3, 2))
    assert ledger.snapshot() == before


def test_payload_subclass_cannot_override_admission() -> None:
    class Unbounded(ExactMicroblock):
        def __post_init__(self) -> None:
            pass

    ledger, _compiler, cache, _program, key = _fixture()
    assert_rejected_atomically(
        ledger,
        lambda: cache.put(key, Unbounded(7, 1000)),
        TypeError,
        match="exact bounded payload",
    )
    assert cache.get(key) == ExactMicroblock(7, 4)


@pytest.mark.parametrize("operation", ("get", "put", "discard"))
def test_key_subclass_cannot_override_coordinate_admission(operation: str) -> None:
    class UncheckedKey(MicroblockKey):
        def __post_init__(self) -> None:
            pass

    ledger, _compiler, cache, program, key = _fixture()
    invalid = UncheckedKey(program, 10, False, 0, "output")
    before = ledger.snapshot()
    with pytest.raises(TypeError, match="exact key"):
        _invoke_key_operation(cache, invalid, operation)
    assert ledger.snapshot() == before
    assert cache.get(key) == ExactMicroblock(7, 4)


def _invoke_key_operation(
    cache: MicroblockCache, key: MicroblockKey, operation: str
) -> None:
    if operation == "get":
        cache.get(key)
    elif operation == "put":
        cache.put(key, ExactMicroblock(3, 2))
    else:
        cache.discard(key)


def _assert_cache_retained(
    cache: MicroblockCache,
    ledger: ResourceLedger,
    key: MicroblockKey,
    contents: dict[MicroblockKey, ExactMicroblock],
    before: LedgerSnapshot,
) -> None:
    assert dict(cache.blocks.items()) == contents
    assert ledger.snapshot() == before
    assert cache.get(key) == ExactMicroblock(7, 4)
