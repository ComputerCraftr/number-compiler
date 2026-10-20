"""Index-owned symbolic programs for production Collatz field actions.

The generic :class:`ProgramComposition` tree is deliberately not used here.
These nodes are typed components of a Collatz field action and contain only
scoped child references plus exact exponent metadata.  They are construction
syntax for the source-bound provider; no proof-machine state, parity itinerary,
future suffix, or affine integer is retained.
"""

from __future__ import annotations

from collections.abc import Mapping, MutableMapping, MutableSequence
from dataclasses import dataclass
from types import MappingProxyType
from typing import Final, TypeGuard

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
    is_object_tuple,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.arithmetic.contracts.semantic_identity import (
    SemanticIdentity,
    SemanticIdentityDomain,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
    PayloadAuditStoreBinding,
    register_payload_audit_contract,
)
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.collatz.field_action import ProgramRole

_ROLES: tuple[ProgramRole, ...] = (
    "root",
    "affine",
    "output",
    "physical-tick",
    "valuation",
    "frame",
)
_EXPONENT_LIMB_BITS = 64
COLLATZ_RUNTIME_PROGRAM_TAG: Final[str] = "collatz-runtime-program-v2-binary-exponent"
EXACT_EXPONENT_LIMBS_TAG: Final[str] = "exact-exponent-u64-v1"


def _exponent_limbs(exponent: int) -> tuple[int, ...]:
    """Encode one exact nonnegative exponent as canonical bounded limbs.

    SemanticIdentity intentionally rejects unbounded integer payloads. This
    descriptor preserves exact time while avoiding decimal conversion, whose
    cost is larger and can fail at Python's integer-string digit limit.
    """
    bit_length = exponent.bit_length()
    if bit_length == 0:
        return ()
    byte_length = (bit_length + 7) // 8
    encoded = exponent.to_bytes(byte_length, "little")
    return tuple(
        int.from_bytes(encoded[offset : offset + 8], "little")
        for offset in range(0, byte_length, 8)
    )


@dataclass(frozen=True, slots=True)
class CollatzRuntimeProgram:
    """One normalized typed identity, atom, or binary composition."""

    role: ProgramRole
    exponent: int
    before: ActionProgramID | None = None
    after: ActionProgramID | None = None

    def __post_init__(self) -> None:
        if type(self.role) is not str or self.role not in _ROLES:
            raise ValueError("unknown Collatz runtime program role")
        if type(self.exponent) is not int or self.exponent < 0:
            raise ValueError("Collatz program exponent must be nonnegative")
        children = self.before, self.after
        if self.exponent <= 1:
            if any(child is not None for child in children):
                raise ValueError("identity and primitive programs have no children")
        elif any(type(child) is not ActionProgramID for child in children):
            raise TypeError("a composed Collatz program requires two scoped children")


class CollatzRuntimeProgramArena:
    """Canonical fixed-size component DAG shared by one Collatz index."""

    _KIND = "collatz-runtime-program"

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("Collatz runtime programs require an index ledger")
        self.ledger = ledger
        self.owner = ArenaToken("collatz-runtime-programs")
        ledger.register_execution_root(self)
        prefix = f"collatz-runtime-program-{len(ledger.inventory())}"
        self._node_owner = ledger.register(prefix + "-nodes", "action_program")
        self._key_owner = ledger.register(
            prefix + "-interner", "action_program_interner"
        )
        self._compose_owner = ledger.register(
            prefix + "-compositions", "action_construction_metadata"
        )
        self._nodes: MutableSequence[CollatzRuntimeProgram] = ledger.make_list(
            self._node_owner
        )
        self._keys: MutableMapping[tuple[ProgramRole, int], ActionProgramID] = (
            ledger.make_dict(self._key_owner)
        )
        self._compositions: MutableMapping[
            tuple[ProgramRole, ActionProgramID, ActionProgramID], ActionProgramID
        ] = ledger.make_dict(self._compose_owner)
        ledger.register_container(
            self._compose_owner,
            self._compositions,
            payloads=self._compositions.items,
            composition_count=lambda: len(self._compositions),
        )
        self._identity_owner = ledger.register(
            prefix + "-semantic-identities", "semantic_identity_cache"
        )
        self._identity_authority_owner = ledger.register(
            prefix + "-semantic-identity-authority",
            "semantic_identity_cache_authority",
        )
        self._semantic_identities: LedgerDict[
            tuple[ProgramRole, int],
            tuple[SemanticIdentity, str, tuple[object, ...], int],
        ] = ledger.make_dict(self._identity_owner, write_once=True)
        self._semantic_identity_authority: LedgerDict[
            tuple[ProgramRole, int],
            tuple[SemanticIdentity, str, tuple[object, ...], int],
        ] = ledger.make_dict(self._identity_authority_owner, write_once=True)
        self._identity_storage_nodes = 0
        ledger.register_container(
            self._identity_owner,
            self._semantic_identities,
            node_count=lambda: self._identity_storage_nodes,
            payloads=self._semantic_identities.items,
        )

        self.register_payload_audit()

    @property
    def nodes(self) -> tuple[CollatzRuntimeProgram, ...]:
        return tuple(self._nodes)

    @property
    def interned(self) -> Mapping[tuple[ProgramRole, int], ActionProgramID]:
        return MappingProxyType(self._keys)

    @staticmethod
    def _role(role: ProgramRole) -> ProgramRole:
        if type(role) is not str or role not in _ROLES:
            raise ValueError("unknown Collatz runtime program role")
        return role

    def intern_record(
        self,
        node: CollatzRuntimeProgram,
        reservations: tuple[tuple[int, int, int], ...] = (),
    ) -> ActionProgramID:
        if type(node) is not CollatzRuntimeProgram:
            raise TypeError("Collatz program publication requires an exact node")
        node.__post_init__()
        # Every production component is a power of the one verified primitive
        # for its role.  Its exact exponent is therefore its complete semantic
        # identity.  Canonicalize on that identity before publishing a syntax
        # witness so two parenthesizations cannot acquire different IDs.
        key = node.role, node.exponent
        self.ledger.bump(
            _collatz_keys.COLLATZ_RUNTIME_PROGRAM_KEY_BIT_WORK,
            max(1, node.exponent.bit_length()),
        )
        found = self._keys.get(key)
        if found is not None:
            self.ledger.reserve_many(reservations)
            return found
        self.ledger.reserve_many(
            ((self._node_owner, 1, 1), (self._key_owner, 1, 0), *reservations)
        )
        result = ActionProgramID(self.owner, self._KIND, len(self._nodes))
        self._nodes.append(node)
        self._keys[key] = result
        return result

    def resolve(self, reference: ActionProgramID) -> CollatzRuntimeProgram:
        if type(reference) is not ActionProgramID:
            raise TypeError("expected a scoped Collatz runtime program")
        reference.validate(self.owner, self._KIND, size=len(self._nodes))
        return self._nodes[reference.local_id]

    def validate(self, role: ProgramRole, reference: ActionProgramID) -> int:
        role = self._role(role)
        node = self.resolve(reference)
        if type(node) is not CollatzRuntimeProgram:
            raise TypeError("Collatz runtime program store contains another node type")
        node.__post_init__()
        if node.role != role:
            raise ValueError("Collatz runtime program has another semantic role")
        return reference.local_id

    def semantic_identity(
        self,
        role: ProgramRole,
        reference: ActionProgramID,
    ) -> SemanticIdentity:
        """Return source-free program behavior without an arena ordinal.

        Exact duration distinguishes source-independent time actions. Encode
        it as a tagged tuple of bounded binary limbs rather than an unbounded
        integer or decimal string inside :class:`SemanticIdentity`.
        """
        role = self._role(role)
        node = self.resolve(reference)
        if type(node) is not CollatzRuntimeProgram:
            raise TypeError("Collatz runtime program store contains another node type")
        node.__post_init__()
        if node.role != role:
            raise ValueError("Collatz runtime program has another semantic role")
        return self.semantic_identity_for_exponent(role, node.exponent)

    def audit_semantic_identity(
        self,
        role: ProgramRole,
        reference: ActionProgramID,
    ) -> SemanticIdentity:
        """Read and authenticate an already-issued identity without publishing.

        Payload audits must not repair a missing cache entry or increment
        production counters.  Both stores are read through their backing
        mapping views so this path remains forensic even if normal admission
        is no longer available.
        """
        role = self._role(role)
        node = self.resolve(reference)
        if type(node) is not CollatzRuntimeProgram:
            raise TypeError("Collatz runtime program store contains another node type")
        node.__post_init__()
        if node.role != role:
            raise ValueError("Collatz runtime program has another semantic role")
        identity_store = self._semantic_identities
        authority_store = self._semantic_identity_authority
        if (
            type(identity_store) is not LedgerDict
            or type(authority_store) is not LedgerDict
            or identity_store.ledger is not self.ledger
            or authority_store.ledger is not self.ledger
            or identity_store.owner != self._identity_owner
            or authority_store.owner != self._identity_authority_owner
            or not self.ledger.is_factory_container(identity_store)
            or not self.ledger.is_factory_container(authority_store)
        ):
            raise ValueError("Collatz semantic identity stores lost their owners")
        key = role, node.exponent
        record = identity_store.backing_store.get(key)
        issued = authority_store.backing_store.get(key)
        if record is None or record is not issued:
            raise ValueError("Collatz semantic identity is not already authenticated")
        return self._audit_identity_record(role, node.exponent, record)

    @staticmethod
    def _audit_identity_record(
        role: ProgramRole,
        exponent: int,
        record: object,
    ) -> SemanticIdentity:
        """Check an existing identity row against its exact semantic key."""
        if not is_exact_object_tuple(record) or len(record) != 4:
            raise ValueError("malformed Collatz semantic identity record")
        identity, digest, behavior, stored_exponent = record
        if (
            type(identity) is not SemanticIdentity
            or type(digest) is not str
            or not is_exact_object_tuple(behavior)
            or len(behavior) != 3
            or type(stored_exponent) is not int
            or stored_exponent != exponent
            or identity.digest != digest
            or identity.behavior is not behavior
            or behavior[0] != COLLATZ_RUNTIME_PROGRAM_TAG
            or behavior[1] != role
        ):
            raise ValueError("Collatz semantic identity lost its exact binding")
        descriptor = behavior[2]
        if (
            not is_exact_object_tuple(descriptor)
            or len(descriptor) != 3
            or descriptor[0] != EXACT_EXPONENT_LIMBS_TAG
            or descriptor[1] != exponent.bit_length()
            or not _is_exponent_limbs(descriptor[2])
            or sum(
                limb << (_EXPONENT_LIMB_BITS * index)
                for index, limb in enumerate(descriptor[2])
            )
            != exponent
        ):
            raise ValueError("Collatz semantic identity has a malformed exponent")
        identity.validate()
        return identity

    def semantic_identity_for_exponent(
        self, role: ProgramRole, exponent: int
    ) -> SemanticIdentity:
        """Authenticate or publish one exact role/exponent identity.

        This source-free descriptor operation does not issue a runtime program
        handle. It is useful when the mathematical exponent is too large to
        materialize as an explicit program composition.
        """
        role = self._role(role)
        if type(exponent) is not int or exponent < 0:
            raise ValueError("Collatz semantic exponent must be nonnegative")
        key = role, exponent
        bit_length = exponent.bit_length()
        if bit_length.bit_length() > 64:
            raise ValueError("Collatz exponent descriptor exceeds its bounded metadata")
        self.ledger.bump(
            _collatz_keys.COLLATZ_RUNTIME_IDENTITY_KEY_BIT_WORK, max(1, bit_length)
        )
        record = self._semantic_identities.get(key)
        if record is not None:
            issued = self._semantic_identity_authority.get(key)
            self.ledger.bump(
                _collatz_keys.COLLATZ_RUNTIME_IDENTITY_AUTHORITY_KEY_BIT_WORK,
                max(1, bit_length),
            )
            if (
                record is not issued
                or type(record) is not tuple
                or len(record) != 4
                or type(record[0]) is not SemanticIdentity
                or type(record[1]) is not str
                or type(record[2]) is not tuple
                or len(record[2]) != 3
                or type(record[3]) is not int
                or record[3] != exponent
            ):
                raise ValueError("malformed cached Collatz semantic identity")
            found, digest, behavior_seal, _stored_exponent = record
            descriptor = behavior_seal[2]
            limb_count = (bit_length + _EXPONENT_LIMB_BITS - 1) // _EXPONENT_LIMB_BITS
            if (
                found.digest != digest
                or found.behavior is not behavior_seal
                or behavior_seal[0] != COLLATZ_RUNTIME_PROGRAM_TAG
                or behavior_seal[1] != role
                or not is_object_tuple(descriptor)
                or type(descriptor) is not tuple
                or len(descriptor) != 3
                or descriptor[0] != EXACT_EXPONENT_LIMBS_TAG
                or descriptor[1] != bit_length
                or not is_object_tuple(descriptor[2])
                or type(descriptor[2]) is not tuple
                or len(descriptor[2]) != limb_count
            ):
                # The memo is index-local and its descriptor is an immutable
                # tuple installed with this exact key. The identity/digest
                # seals above detect replacement or mutation without walking
                # every limb on a warm hit.
                raise ValueError("cached Collatz semantic identity lost its seal")
            self.ledger.bump(_collatz_keys.COLLATZ_RUNTIME_IDENTITY_CACHE_HITS)
            return found
        self.ledger.bump(
            _collatz_keys.COLLATZ_RUNTIME_IDENTITY_AUTHORITY_KEY_BIT_WORK,
            max(1, bit_length),
        )
        if key in self._semantic_identity_authority:
            raise ValueError("orphaned Collatz semantic identity authority")

        limb_count = (bit_length + _EXPONENT_LIMB_BITS - 1) // _EXPONENT_LIMB_BITS
        retained_nodes = 1 + limb_count
        self.ledger.reserve_many(
            (
                (self._identity_owner, 1, retained_nodes),
                (self._identity_authority_owner, 1, 0),
            )
        )
        record = None
        node_count_published = False
        try:
            byte_length = (bit_length + 7) // 8
            self.ledger.bump(
                _collatz_keys.COLLATZ_RUNTIME_IDENTITY_TRANSIENT_BYTE_WORK,
                byte_length,
            )
            limbs = _exponent_limbs(exponent)
            if len(limbs) != limb_count:
                raise ArithmeticError("noncanonical Collatz exponent limb count")
            self.ledger.bump(
                _collatz_keys.COLLATZ_RUNTIME_IDENTITY_LIMB_WORK, max(1, limb_count)
            )
            behavior = (
                COLLATZ_RUNTIME_PROGRAM_TAG,
                role,
                (EXACT_EXPONENT_LIMBS_TAG, bit_length, limbs),
            )
            identity = SemanticIdentity(SemanticIdentityDomain.ANONYMOUS, behavior)
            record = (
                identity,
                identity.digest,
                identity.behavior,
                exponent,
            )
            self._semantic_identities[key] = record
            self._semantic_identity_authority[key] = record
            self._identity_storage_nodes += retained_nodes
            node_count_published = True
        except BaseException:
            if node_count_published:
                self._identity_storage_nodes -= retained_nodes
            authority_removed = (
                self._semantic_identity_authority.rollback_unpublished(key, record)
                if record is not None
                else False
            )
            if not authority_removed:
                self.ledger.release(self._identity_authority_owner, entries=1)
            cache_removed = (
                self._semantic_identities.rollback_unpublished(key, record)
                if record is not None
                else False
            )
            if not cache_removed:
                self.ledger.release(self._identity_owner, entries=1)
            self.ledger.release(self._identity_owner, nodes=retained_nodes)
            raise
        self.ledger.bump(
            _collatz_keys.COLLATZ_RUNTIME_IDENTITY_RETAINED_LIMB_BYTES,
            8 * limb_count,
        )
        self.ledger.bump(_collatz_keys.COLLATZ_RUNTIME_IDENTITY_CACHE_MISSES)
        return identity

    def _composition_operands(
        self, role: ProgramRole, before: ActionProgramID, after: ActionProgramID
    ) -> tuple[ProgramRole, CollatzRuntimeProgram, CollatzRuntimeProgram]:
        role = self._role(role)
        first, second = self.resolve(before), self.resolve(after)
        if first.role != role or second.role != role:
            raise ValueError("Collatz program composition crossed component roles")
        return role, first, second

    def composed_semantic_identity(
        self,
        role: ProgramRole,
        before: ActionProgramID,
        after: ActionProgramID,
    ) -> SemanticIdentity:
        """Predict composition semantics without publishing a syntax node."""
        role, first, second = self._composition_operands(role, before, after)
        self.ledger.bump(
            _collatz_keys.COLLATZ_RUNTIME_IDENTITY_SUM_BIT_WORK,
            max(1, first.exponent.bit_length()) + max(1, second.exponent.bit_length()),
        )
        return self.semantic_identity_for_exponent(
            role, first.exponent + second.exponent
        )

    def identity(self, role: ProgramRole) -> ActionProgramID:
        role = self._role(role)
        return self.intern_record(CollatzRuntimeProgram(role, 0))

    def primitive(self, role: ProgramRole) -> ActionProgramID:
        role = self._role(role)
        return self.intern_record(CollatzRuntimeProgram(role, 1))

    def compose(
        self,
        role: ProgramRole,
        before: ActionProgramID,
        after: ActionProgramID,
    ) -> ActionProgramID:
        role, first, second = self._composition_operands(role, before, after)
        if first.exponent == 0:
            return after
        if second.exponent == 0:
            return before
        key = role, before, after
        found = self._compositions.get(key)
        if found is not None:
            self.resolve(found)
            self.ledger.bump(_collatz_keys.COLLATZ_PROGRAM_COMPOSITION_EARLY_HITS)
            return found
        node = CollatzRuntimeProgram(
            role,
            self._sum_exponents(first.exponent, second.exponent),
            before,
            after,
        )
        result = self.intern_record(node, ((self._compose_owner, 1, 0),))
        self._compositions[key] = result
        self.ledger.bump(_collatz_keys.COLLATZ_PROGRAM_COMPOSITIONS)
        return result

    def _sum_exponents(self, first: int, second: int) -> int:
        """Charge the exact duration addition used for a newly composed node."""
        self.ledger.bump(
            _collatz_keys.COLLATZ_RUNTIME_PROGRAM_SUM_BIT_WORK,
            max(1, first.bit_length()) + max(1, second.bit_length()),
        )
        return first + second

    def register_payload_audit(self) -> None:
        root = self

        if type(root) is not CollatzRuntimeProgramArena:
            raise TypeError("Collatz runtime audit requires its exact arena")
        stores = (
            PayloadAuditStoreBinding(root._node_owner, "_nodes", "action_program"),
            PayloadAuditStoreBinding(
                root._key_owner, "_keys", "action_program_interner"
            ),
            PayloadAuditStoreBinding(
                root._compose_owner, "_compositions", "action_construction_metadata"
            ),
            PayloadAuditStoreBinding(
                root._identity_owner, "_semantic_identities", "semantic_identity_cache"
            ),
            PayloadAuditStoreBinding(
                root._identity_authority_owner,
                "_semantic_identity_authority",
                "semantic_identity_cache_authority",
            ),
        )
        register_payload_audit_contract(
            root.ledger, root, "collatz", stores, audit_collatz_runtime_programs
        )

    def audit_payload(self, ledger: object, root: object) -> PayloadAuditContribution:
        """Validate canonical program nodes, compositions and identity witnesses."""
        if root is not self:
            raise TypeError("payload audit callback received another owner")
        from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
        from number_compiler.arithmetic.contracts.semantic_identity import (
            SemanticIdentity,
        )
        from number_compiler.resources.ledger import ResourceLedger

        if (
            type(ledger) is not ResourceLedger
            or type(root) is not CollatzRuntimeProgramArena
        ):
            raise TypeError("Collatz runtime-program audit received a foreign owner")
        arena = root
        approved: list[PayloadAuditEntry] = []
        invalid: list[PayloadAuditEntry] = []

        def record(owner: int, value: object, valid: bool) -> None:
            entry = PayloadAuditEntry(owner, value)
            (approved if valid else invalid).append(entry)

        identity_row = ledger.inventory_owner(arena._identity_owner)
        authority_row = ledger.inventory_owner(arena._identity_authority_owner)
        root_valid = (
            arena.ledger is ledger
            and identity_row.role == "semantic_identity_cache"
            and identity_row.entries == len(arena._semantic_identities)
            and identity_row.nodes == arena._identity_storage_nodes
            and authority_row.role == "semantic_identity_cache_authority"
            and authority_row.entries == len(arena._semantic_identity_authority)
            and authority_row.nodes == 0
            and len(arena._semantic_identities)
            == len(arena._semantic_identity_authority)
        )
        if not root_valid:
            invalid.append(PayloadAuditEntry(arena._node_owner, arena))

        for identity_key, identity_record in arena._semantic_identities.items():
            valid = (
                type(identity_key) is tuple
                and len(identity_key) == 2
                and type(identity_key[0]) is str
                and identity_key[0]
                in {"root", "affine", "output", "physical-tick", "valuation", "frame"}
                and type(identity_key[1]) is int
                and identity_key[1] >= 0
                and arena._semantic_identity_authority.get(identity_key)
                is identity_record
                and type(identity_record) is tuple
                and len(identity_record) == 4
            )
            try:
                if type(identity_record) is not tuple or len(identity_record) != 4:
                    raise ValueError("malformed Collatz semantic identity row")
                identity, digest, behavior, exponent = identity_record
                if type(behavior) is not tuple or len(behavior) != 3:
                    raise ValueError("malformed Collatz identity behavior")
                descriptor = behavior[2]
                if (
                    not is_object_tuple(descriptor)
                    or type(descriptor) is not tuple
                    or len(descriptor) != 3
                ):
                    raise ValueError("malformed Collatz exponent descriptor")
                limbs = descriptor[2]
                valid &= (
                    type(identity) is SemanticIdentity
                    and type(digest) is str
                    and identity.digest == digest
                    and identity.behavior is behavior
                    and type(exponent) is int
                    and exponent == identity_key[1]
                    and behavior[0] == COLLATZ_RUNTIME_PROGRAM_TAG
                    and behavior[1] == identity_key[0]
                    and descriptor[0] == EXACT_EXPONENT_LIMBS_TAG
                    and descriptor[1] == exponent.bit_length()
                    and _is_exponent_limbs(limbs)
                    and sum(limb << (64 * index) for index, limb in enumerate(limbs))
                    == exponent
                )
                identity.validate()
            except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                valid = False
            record(arena._identity_owner, identity_key, valid)
            record(arena._identity_owner, identity_record, valid)
            record(arena._identity_authority_owner, identity_key, valid)
            record(arena._identity_authority_owner, identity_record, valid)

        for index, program in enumerate(arena._nodes):
            if type(program) is not CollatzRuntimeProgram:
                record(arena._node_owner, program, False)
                continue
            valid = True
            stored_handle = None
            try:
                program.__post_init__()
                handle = ActionProgramID(arena.owner, arena._KIND, index)
                stored_handle = arena._keys.get((program.role, program.exponent))
                valid &= arena.resolve(handle) is program
                valid &= stored_handle == handle
                for child in (program.before, program.after):
                    if child is not None:
                        arena.resolve(child)
            except (TypeError, ValueError, IndexError, AttributeError):
                valid = False
            record(arena._node_owner, program, valid)
            if stored_handle is not None:
                record(arena._key_owner, stored_handle, valid)

        for interner_key, handle in arena._keys.items():
            valid = (
                type(interner_key) is tuple
                and len(interner_key) == 2
                and type(interner_key[0]) is str
                and type(interner_key[1]) is int
                and type(handle) is ActionProgramID
            )
            try:
                program = arena.resolve(handle)
                valid &= (program.role, program.exponent) == interner_key
            except (TypeError, ValueError, IndexError, AttributeError):
                valid = False
            record(arena._key_owner, interner_key, valid)
            record(arena._key_owner, handle, valid)

        for composition_key, result in arena._compositions.items():
            valid = (
                type(composition_key) is tuple
                and len(composition_key) == 3
                and type(composition_key[0]) is str
            )
            try:
                if type(composition_key) is not tuple or len(composition_key) != 3:
                    raise ValueError("malformed Collatz composition key")
                first, second = (
                    arena.resolve(composition_key[1]),
                    arena.resolve(composition_key[2]),
                )
                actual = arena.resolve(result)
                valid &= first.role == second.role == composition_key[0] == actual.role
                valid &= actual.exponent == first.exponent + second.exponent
                valid &= (
                    actual.before == composition_key[1]
                    and actual.after == composition_key[2]
                )
            except (TypeError, ValueError, IndexError, AttributeError):
                valid = False
            record(arena._compose_owner, composition_key, valid)
            record(arena._compose_owner, result, valid)

        return PayloadAuditContribution(tuple(approved), tuple(invalid))


__all__ = ["CollatzRuntimeProgram", "CollatzRuntimeProgramArena"]


def _is_exponent_limbs(value: object) -> TypeGuard[tuple[int, ...]]:
    """Validate exact limb tuples at the forensic payload boundary."""
    return (
        is_object_tuple(value)
        and type(value) is tuple
        and all(type(limb) is int and 0 <= limb < 1 << 64 for limb in value)
    )


def audit_collatz_runtime_programs(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Closure-free ledger entry point for its exact family owner."""
    if type(root) is not CollatzRuntimeProgramArena:
        raise TypeError("Collatz payload audit received another owner")
    return root.audit_payload(ledger, root)
