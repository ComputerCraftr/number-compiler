"""Strictly capped exact future microblocks for scalar/radix leaf acceleration.

This is not a semantic arena and cannot construct a future DyadicTile.  It owns
only small encoded observations after the canonical source/program identity is
known.  Every retained payload is at most 64 bits; all views/radices on one
term share the same 1,024-entry / 8-KiB payload budget.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import Literal

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.resources.ledger import ResourceLedger, ResourceScope
from number_compiler.resources.metric_keys import projection as _projection_keys
from number_compiler.resources.stores import LedgerDict

MicroblockKind = Literal["binary", "remainder", "output"]


@dataclass(frozen=True, slots=True)
class MicroblockKey:
    program: ActionProgramID
    radix: int
    stage: int
    block: int
    kind: MicroblockKind
    source_scope: ArenaToken | None = None

    def __post_init__(self) -> None:
        source_scope = getattr(self, "source_scope", None)
        if (
            type(self.program) is not ActionProgramID
            or self.program.kind != "action-program"
            or type(self.radix) is not int
            or not 2 <= self.radix <= 1 << 63
            or type(self.stage) is not int
            or self.stage < 0
            or type(self.block) is not int
            or self.block < 0
            or self.kind not in ("binary", "remainder", "output")
            or source_scope is not None
            and type(source_scope) is not ArenaToken
        ):
            raise ValueError("invalid exact microblock key")


@dataclass(frozen=True, slots=True)
class ExactMicroblock:
    encoded: int
    bit_count: int

    def __post_init__(self) -> None:
        if (
            type(self.encoded) is not int
            or self.encoded < 0
            or type(self.bit_count) is not int
            or not 1 <= self.bit_count <= 64
            or self.encoded.bit_length() > self.bit_count
        ):
            raise ValueError("exact microblocks contain at most 64 encoded bits")

    @property
    def payload_bytes(self) -> int:
        return (self.bit_count + 7) // 8


@dataclass(frozen=True, slots=True)
class MicroblockCacheAuditSnapshot:
    """Detached read-only view of exact bounded cache payloads."""

    ledger: ResourceLedger
    owner: int
    blocks: Mapping[MicroblockKey, ExactMicroblock]
    payload_bytes: int


class MicroblockCache:
    """One index-owned, evictable, non-semantic exact observation cache."""

    MAX_ENTRIES = 1_024
    MAX_PAYLOAD_BYTES = 8 * 1_024
    MAX_TRANSIENT_BYTES = 256

    @classmethod
    def shared(
        cls,
        ledger: ResourceLedger,
        program_owner: ArenaToken | None = None,
        validate_program: Callable[[ActionProgramID], object] | None = None,
    ) -> MicroblockCache:
        """Return the one live cache owned by this execution ledger."""
        for root in ledger.iter_execution_roots():
            if type(root) is cls and root.ledger is ledger:
                if program_owner is not None and validate_program is not None:
                    root.bind(program_owner, validate_program)
                return root
        if program_owner is None or validate_program is None:
            raise ValueError("a new microblock cache requires an owning program arena")
        return cls(ledger, program_owner, validate_program)

    def __init__(
        self,
        ledger: ResourceLedger,
        program_owner: ArenaToken,
        validate_program: Callable[[ActionProgramID], object],
    ) -> None:
        if (
            type(ledger) is not ResourceLedger
            or type(program_owner) is not ArenaToken
            or not callable(validate_program)
        ):
            raise TypeError(
                "microblock cache requires an index ledger and program validator"
            )
        self.ledger = ledger
        self._authority_owner = ledger.register(
            "exact-microblock-program-authorities",
            "action_authority",
            ResourceScope.INDEX_OWNED,
        )
        self._validators: LedgerDict[
            ArenaToken, Callable[[ActionProgramID], object]
        ] = ledger.make_dict(self._authority_owner)
        ledger.register_container(
            self._authority_owner,
            self._validators,
            payloads=lambda: self._validators.keys(),
        )
        self.bind(program_owner, validate_program)
        self.owner = ledger.register(
            "exact-microblocks", "exact_microblock", ResourceScope.INDEX_OWNED
        )
        self.blocks: LedgerDict[MicroblockKey, ExactMicroblock] = ledger.make_dict(
            self.owner
        )
        self.payload_bytes = 0
        ledger.register_execution_root(self)
        # make_dict already registered the container; attach eviction through a
        # distinct owner would duplicate ownership, so the cache performs its
        # own pre-publication eviction in put().

    def bind(
        self,
        program_owner: ArenaToken,
        validate_program: Callable[[ActionProgramID], object],
    ) -> None:
        """Admit one scoped program arena before any key from it is probed."""
        if type(program_owner) is not ArenaToken or not callable(validate_program):
            raise TypeError("microblock program authority must be a scoped validator")
        found = self._validators.get(program_owner)
        if found is not None and found != validate_program:
            raise ValueError("microblock program arena already has another validator")
        if found is None:
            self.ledger.reserve(self._authority_owner, entries=1)
        self._validators[program_owner] = validate_program

    def _validate_key(self, key: MicroblockKey) -> None:
        if type(key) is not MicroblockKey:
            raise TypeError("microblock requests require an exact key")
        key.__post_init__()
        validator = self._validators.get(key.program.owner)
        if validator is None:
            raise ValueError("microblock program belongs to an unbound arena")
        validator(key.program)

    @staticmethod
    def _validate_payload(value: ExactMicroblock) -> ExactMicroblock:
        if type(value) is not ExactMicroblock:
            raise TypeError("microblock cache requires an exact bounded payload")
        value.__post_init__()
        return value

    @staticmethod
    def _payload(value: ExactMicroblock) -> ExactMicroblock:
        if type(value) is not ExactMicroblock:
            raise TypeError("microblock cache requires an exact bounded payload")
        # Ordinary frozen-record assignment is already forbidden. Snapshots also
        # isolate explicit object.__setattr__ corruption of caller-held records.
        # Only two scalar fields are copied; retained entry/payload charges stay
        # unchanged, and the copied integer payload remains at most 64 bits.
        return ExactMicroblock(value.encoded, value.bit_count)

    @staticmethod
    def _key_snapshot(key: MicroblockKey) -> MicroblockKey:
        program = key.program
        return MicroblockKey(
            ActionProgramID(program.owner, program.kind, program.local_id),
            key.radix,
            key.stage,
            key.block,
            key.kind,
            key.source_scope,
        )

    def get(self, key: MicroblockKey) -> ExactMicroblock | None:
        self._validate_key(key)
        found = self.blocks.get(key)
        value = None if found is None else self._payload(found)
        self.ledger.bump(_projection_keys.MICROBLOCK_REQUESTS)
        if value is not None:
            self.ledger.bump(_projection_keys.MICROBLOCK_HITS)
        return value

    def _drop(self, key: MicroblockKey) -> None:
        value = self._validate_payload(self.blocks[key])
        del self.blocks[key]
        self.ledger.release(self.owner, entries=1)
        self.payload_bytes -= value.payload_bytes
        self.ledger.counters[_projection_keys.MICROBLOCK_PAYLOAD_BYTES] = (
            self.payload_bytes
        )
        self.ledger.bump(_projection_keys.MICROBLOCK_EVICTIONS)

    def discard(self, key: MicroblockKey) -> None:
        self._validate_key(key)
        if key in self.blocks:
            self._drop(key)

    def put(self, key: MicroblockKey, value: ExactMicroblock) -> None:
        self._validate_key(key)
        value = self._payload(value)
        key = self._key_snapshot(key)
        old = self.blocks.get(key)
        if old is not None:
            old = self._validate_payload(old)
            next_bytes = self.payload_bytes - old.payload_bytes + value.payload_bytes
            if next_bytes > self.MAX_PAYLOAD_BYTES:
                raise RuntimeError(
                    "microblock replacement exceeds the fixed payload cap"
                )
            self.blocks[key] = value
            self.payload_bytes = next_bytes
            self.ledger.counters[_projection_keys.MICROBLOCK_PAYLOAD_BYTES] = (
                self.payload_bytes
            )
            self.ledger.counters[
                _projection_keys.MICROBLOCK_PAYLOAD_HIGH_WATER_BYTES
            ] = max(
                self.ledger.counters.get(
                    _projection_keys.MICROBLOCK_PAYLOAD_HIGH_WATER_BYTES, 0
                ),
                self.payload_bytes,
            )
            return
        victims: list[tuple[MicroblockKey, ExactMicroblock]] = []
        removed_bytes = 0
        for victim in self.blocks:
            if (
                len(self.blocks) - len(victims) < self.MAX_ENTRIES
                and self.payload_bytes - removed_bytes + value.payload_bytes
                <= self.MAX_PAYLOAD_BYTES
            ):
                break
            victim_value = self._validate_payload(self.blocks[victim])
            victims.append((victim, victim_value))
            removed_bytes += victim_value.payload_bytes
        if (
            len(self.blocks) - len(victims) >= self.MAX_ENTRIES
            or self.payload_bytes - removed_bytes + value.payload_bytes
            > self.MAX_PAYLOAD_BYTES
        ):
            raise RuntimeError("microblock payload cannot fit its fixed cache")

        # A victim's already-reserved slot is transferred to the new block.
        # When no victim is required, admission must succeed before any cache
        # mutation.  This prevents a denied global reservation from destroying
        # a locally evicted exact observation.
        reserved = not victims
        if reserved:
            self.ledger.reserve(self.owner, entries=1)
        removed = 0
        try:
            for victim, _victim_value in victims:
                del self.blocks[victim]
                removed += 1
            self.blocks[key] = value
        except BaseException:
            for victim, victim_value in victims[:removed]:
                self.blocks[victim] = victim_value
            if reserved:
                self.ledger.release(self.owner, entries=1)
            raise
        unused_slots = len(victims) - 1
        if unused_slots > 0:
            self.ledger.release(self.owner, entries=unused_slots)
        self.payload_bytes = self.payload_bytes - removed_bytes + value.payload_bytes
        if victims:
            self.ledger.bump(_projection_keys.MICROBLOCK_EVICTIONS, len(victims))
        self.ledger.bump(_projection_keys.MICROBLOCK_PUBLICATIONS)
        self.ledger.counters[_projection_keys.MICROBLOCK_PAYLOAD_BYTES] = (
            self.payload_bytes
        )
        self.ledger.counters[_projection_keys.MICROBLOCK_PAYLOAD_HIGH_WATER_BYTES] = (
            max(
                self.ledger.counters.get(
                    _projection_keys.MICROBLOCK_PAYLOAD_HIGH_WATER_BYTES, 0
                ),
                self.payload_bytes,
            )
        )
        self.ledger.counters[_projection_keys.MICROBLOCK_ENTRY_HIGH_WATER] = max(
            self.ledger.counters.get(_projection_keys.MICROBLOCK_ENTRY_HIGH_WATER, 0),
            len(self.blocks),
        )

    def clear(self) -> None:
        for key in tuple(self.blocks):
            self._drop(key)
        self.payload_bytes = 0
        self.ledger.counters[_projection_keys.MICROBLOCK_PAYLOAD_BYTES] = 0

    def audit_snapshot(self) -> MicroblockCacheAuditSnapshot:
        """Copy bounded payloads so forensic reads cannot mutate this cache."""
        detached = {
            self._key_snapshot(key): self._payload(value)
            for key, value in self.blocks.items()
        }
        return MicroblockCacheAuditSnapshot(
            self.ledger,
            self.owner,
            MappingProxyType(detached),
            self.payload_bytes,
        )

    def __len__(self) -> int:
        return len(self.blocks)


__all__ = [
    "ExactMicroblock",
    "MicroblockCache",
    "MicroblockCacheAuditSnapshot",
    "MicroblockKey",
]
