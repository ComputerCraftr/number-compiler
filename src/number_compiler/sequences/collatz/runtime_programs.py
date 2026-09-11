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

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.field_action import ProgramRole

_ROLES: tuple[ProgramRole, ...] = (
    "root",
    "affine",
    "output",
    "physical-tick",
    "valuation",
    "frame",
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

    def _intern(
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
        if node.role != role:
            raise ValueError("Collatz runtime program has another semantic role")
        return reference.local_id

    def semantic_identity(
        self,
        role: ProgramRole,
        reference: ActionProgramID,
    ) -> SemanticIdentity:
        """Return source-free program behavior without an arena ordinal.

        Exponents are geometry-like metadata and may exceed one machine limb;
        encode them as tagged decimal metadata rather than an arithmetic payload
        inside :class:`SemanticIdentity`.
        """
        role = self._role(role)
        node = self.resolve(reference)
        if node.role != role:
            raise ValueError("Collatz runtime program has another semantic role")
        behavior = (
            "collatz-runtime-program-v1",
            role,
            ("exact-exponent", str(node.exponent)),
        )
        return SemanticIdentity("", behavior)

    def composed_semantic_identity(
        self,
        role: ProgramRole,
        before: ActionProgramID,
        after: ActionProgramID,
    ) -> SemanticIdentity:
        """Predict composition semantics without publishing a syntax node."""
        role = self._role(role)
        first, second = self.resolve(before), self.resolve(after)
        if first.role != role or second.role != role:
            raise ValueError("Collatz program composition crossed component roles")
        behavior = (
            "collatz-runtime-program-v1",
            role,
            ("exact-exponent", str(first.exponent + second.exponent)),
        )
        return SemanticIdentity("", behavior)

    def identity(self, role: ProgramRole) -> ActionProgramID:
        role = self._role(role)
        return self._intern(CollatzRuntimeProgram(role, 0))

    def primitive(self, role: ProgramRole) -> ActionProgramID:
        role = self._role(role)
        return self._intern(CollatzRuntimeProgram(role, 1))

    def compose(
        self,
        role: ProgramRole,
        before: ActionProgramID,
        after: ActionProgramID,
    ) -> ActionProgramID:
        role = self._role(role)
        first, second = self.resolve(before), self.resolve(after)
        if first.role != role or second.role != role:
            raise ValueError("Collatz program composition crossed component roles")
        if first.exponent == 0:
            return after
        if second.exponent == 0:
            return before
        key = role, before, after
        found = self._compositions.get(key)
        if found is not None:
            self.resolve(found)
            self.ledger.bump("collatz_program_composition_early_hits")
            return found
        node = CollatzRuntimeProgram(
            role,
            first.exponent + second.exponent,
            before,
            after,
        )
        result = self._intern(node, ((self._compose_owner, 1, 0),))
        self._compositions[key] = result
        self.ledger.bump("collatz_program_compositions")
        return result


__all__ = ["CollatzRuntimeProgram", "CollatzRuntimeProgramArena"]
