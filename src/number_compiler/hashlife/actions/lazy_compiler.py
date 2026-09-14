"""Immutable composition syntax, compiled under the application's ledger.

This compiler never constructs the Cartesian boundary domain of a composition.
The complete interface is interpreted by the iterative lazy view evaluator.
"""

from __future__ import annotations

import hashlib
from collections.abc import Mapping, MutableMapping, MutableSequence
from dataclasses import dataclass
from types import MappingProxyType
from typing import cast

from number_compiler.arithmetic.contracts.block_definition import (
    is_compatibility_composition,
)
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudget,
    BlockEffect,
    BoundarySide,
    BoundaryState,
    _effect_key,
)
from number_compiler.arithmetic.contracts.block_power_types import BlockPower
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.resources.ledger import ResourceLedger


class UnsupportedInterfaceError(TypeError):
    """A custom primitive lacks a complete finite interface."""


@dataclass(frozen=True, slots=True)
class CompilerCompositionKey:
    first: ActionProgramID
    second: ActionProgramID

    def __post_init__(self) -> None:
        if (
            type(self.first) is not ActionProgramID
            or type(self.second) is not ActionProgramID
            or self.first.kind != "action-program"
            or self.second.kind != "action-program"
            or self.first.owner is not self.second.owner
        ):
            raise ValueError("compiler composition requires scoped canonical child IDs")


class ProgramComposition:
    """Output-complete syntax. Boundary interpretation requires lazy views."""

    __slots__ = (
        "__weakref__",
        "_sealed",
        "base",
        "blank",
        "blank_left_tail",
        "blank_right_tail",
        "canonical_key",
        "depth",
        "exponent",
        "first",
        "handle",
        "node_id",
        "second",
        "stable_blank_output",
        "supports_predecessor_trace",
    )

    def __init__(
        self, first: BlockEffect, second: BlockEffect, handle: ActionProgramID
    ) -> None:
        if type(handle) is not ActionProgramID or handle.kind != "action-program":
            raise TypeError("compiled syntax requires a scoped action program ID")
        self.first, self.second, self.handle = first, second, handle
        self.base, self.blank = first.base, first.blank
        self.exponent = first.exponent + second.exponent
        self.node_id = handle.local_id
        digest = hashlib.sha256(
            repr((_effect_key(first), _effect_key(second))).encode()
        ).hexdigest()
        self.canonical_key = (
            "action-program-v2",
            SemanticIdentity(digest, (_effect_key(first), _effect_key(second))),
        )
        self.blank_left_tail = first.blank_left_tail + second.blank_left_tail
        self.blank_right_tail = first.blank_right_tail + second.blank_right_tail
        self.stable_blank_output = (
            first.stable_blank_output and second.stable_blank_output
        )
        self.supports_predecessor_trace = False
        self.depth = 1 + max(getattr(first, "depth", 1), getattr(second, "depth", 1))
        self._sealed = True

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("action program syntax is immutable")
        object.__setattr__(self, name, value)

    def __delattr__(self, name: str) -> None:
        raise AttributeError("immutable definition attributes cannot be deleted")

    def initial(self, side: BoundarySide) -> BoundaryState:
        raise UnsupportedInterfaceError(
            "composed programs require the lazy view evaluator"
        )

    def advance(
        self, side: BoundarySide, state: BoundaryState, symbol: int
    ) -> BoundaryState:
        raise UnsupportedInterfaceError(
            "composed programs require the lazy view evaluator"
        )

    def emit(self, left: BoundaryState, symbol: int, right: BoundaryState) -> int:
        raise UnsupportedInterfaceError(
            "composed programs require the lazy view evaluator"
        )

    def boundary_universe(self, side: BoundarySide) -> None:
        return None

    def predecessor(self, side: BoundarySide, state: BoundaryState) -> None:
        return None

    def operator_nodes(self) -> int:
        seen: set[int] = set()
        stack: list[BlockEffect] = [self]
        while stack:
            node = stack.pop()
            if id(node) in seen:
                continue
            seen.add(id(node))
            if isinstance(node, ProgramComposition):
                stack.extend((node.first, node.second))
        return len(seen)

    def runtime_stats(self) -> dict[str, int]:
        return {"operator_nodes": self.operator_nodes()}


class LazyCompiler:
    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger, self.token = ledger, ArenaToken("operator-compiler")
        ledger.register_execution_root(self)
        self.owner = ledger.register(
            "compiler-programs", "compiled_action_program", "INDEX_OWNED"
        )
        self.index_owner = ledger.register(
            "compiler-interner", "compiled_action_interner", "INDEX_OWNED"
        )
        self._nodes: MutableSequence[BlockEffect] = ledger.make_list(self.owner)
        self._ids: MutableMapping[object, int] = ledger.make_dict(self.index_owner)
        ledger.register_container(
            self.owner,
            self._nodes,
            node_count=lambda: len(self._nodes),
            payloads=self._payloads,
        )
        ledger.register_container(
            self.index_owner,
            self._ids,
            payloads=lambda: self._ids.items(),
            composition_count=self._composition_count,
        )

    @property
    def ids(self) -> Mapping[object, int]:
        return MappingProxyType(self._ids)

    @property
    def nodes(self) -> tuple[BlockEffect, ...]:
        return tuple(self._nodes)

    def _composition_count(self) -> int:
        return sum(isinstance(node, ProgramComposition) for node in self._nodes)

    def _payloads(self) -> list[object]:
        # The audit follows actual composition children, not just scoped IDs.
        return list(self._nodes)

    def atom(self, effect: BlockEffect) -> BlockEffect:
        from number_compiler.arithmetic.contracts.kernel_admission import immutable_atom

        self._validate_program(effect)
        if isinstance(effect, ProgramComposition):
            return effect
        clone = immutable_atom(effect)
        key = _effect_key(effect)
        found = self._ids.get(key)
        if found is not None:
            return self._nodes[found]
        self.ledger.reserve_many(((self.owner, 1, 1), (self.index_owner, 1, 0)))
        self._ids[key] = len(self._nodes)
        self._nodes.append(clone)
        return clone

    def import_effect(self, effect: BlockEffect) -> BlockEffect:
        from number_compiler.arithmetic.contracts.kernel_admission import admit_effect

        # Reject any unsupported/cyclic child before publishing even a valid
        # sibling. Import is an admission boundary, not incremental validation.
        admission_visits = admit_effect(effect)
        imported: dict[int, BlockEffect] = {}
        stack = [(effect, False)]
        visits = 0
        while stack:
            node, ready = stack.pop()
            visits += 1
            if id(node) in imported:
                continue
            if is_compatibility_composition(node) or isinstance(
                node, ProgramComposition
            ):
                if not ready:
                    stack.extend(
                        (
                            (cast(BlockEffect, node), True),
                            (node.second, False),
                            (node.first, False),
                        )
                    )
                    continue
                result = self.compose(
                    imported[id(node.first)], imported[id(node.second)]
                )
            else:
                result = self.atom(node)
            imported[id(node)] = result
        self.ledger.bump("compiler_admission_dag_visits", admission_visits)
        self.ledger.bump("compiler_import_dag_visits", visits)
        return imported[id(effect)]

    def compose(self, first: BlockEffect, second: BlockEffect) -> BlockEffect:
        from number_compiler.arithmetic.contracts.kernel_admission import immutable_atom

        self._validate_program(first)
        self._validate_program(second)
        # Validate both operands before a warm semantic-key hit can conceal an
        # unknown atom or retain a mutable compatibility runtime as syntax.
        shared = first is second
        if not isinstance(first, ProgramComposition):
            first = immutable_atom(first)
        if shared:
            second = first
        elif not isinstance(second, ProgramComposition):
            second = immutable_atom(second)
        if first.base != second.base or first.blank != second.blank:
            raise ValueError("incompatible program alphabets")
        # Assign canonical child identities before the parent lookup. New atoms
        # and their parent are published by one atomic reservation.
        pending_atoms: dict[object, tuple[int, BlockEffect]] = {}
        handles: list[ActionProgramID] = []
        for child in (first, second):
            if isinstance(child, ProgramComposition):
                handles.append(child.handle)
                continue
            semantic = _effect_key(child)
            child_id = self._ids.get(semantic)
            if child_id is None:
                staged = pending_atoms.get(semantic)
                if staged is None:
                    staged = (len(self._nodes) + len(pending_atoms), child)
                    pending_atoms[semantic] = staged
                child_id = staged[0]
            handles.append(ActionProgramID(self.token, "action-program", child_id))
        self.ledger.bump("composition_requests")
        key = CompilerCompositionKey(*handles)
        found = self._ids.get(key)
        if found is not None:
            self.ledger.bump("composition_cache_hits")
            return self._nodes[found]
        allocations = 1 + len(pending_atoms)
        self.ledger.reserve_many(
            ((self.owner, allocations, allocations), (self.index_owner, allocations, 0))
        )
        for semantic, (child_id, child) in pending_atoms.items():
            self._ids[semantic] = child_id
            self._nodes.append(child)
        first, second = (self._nodes[handle.local_id] for handle in handles)
        handle = ActionProgramID(self.token, "action-program", len(self._nodes))
        node = ProgramComposition(first, second, handle)
        self._ids[key] = len(self._nodes)
        self._nodes.append(node)
        self.ledger.register_root(self.owner, handle)
        self.ledger.bump("composition_evaluations")
        return node

    def reference(self, effect: BlockEffect) -> ActionProgramID:
        """Return an admitted canonical identity without compiling anything."""
        self._validate_program(effect)
        if isinstance(effect, ProgramComposition):
            return effect.handle
        found = self._ids.get(_effect_key(effect))
        if found is None or self._nodes[found] is not effect:
            raise ValueError("primitive is not this compiler's canonical definition")
        return ActionProgramID(self.token, "action-program", found)

    def resolve(self, handle: ActionProgramID) -> BlockEffect:
        if type(handle) is not ActionProgramID:
            raise TypeError("compiler lookup requires an action program handle")
        handle.validate(self.token, "action-program", size=len(self._nodes))
        return self._nodes[handle.local_id]

    def power(self, effect: BlockEffect, exponent: int) -> BlockPower:
        if exponent < 0:
            raise ValueError("negative program exponent")
        self._validate_program(effect)
        atom = self.atom(effect)
        operations = 0

        def combine(a: BlockEffect | None, b: BlockEffect | None) -> BlockEffect | None:
            nonlocal operations
            if a is None:
                return b
            if b is None:
                return a
            operations += 1
            # Every operand is a power of this one fixed operator, so these
            # factors commute without reordering its primitive word. Put the
            # largest power first: its complete source parent can then be
            # reused before evaluating the smaller remainder on an image.
            return self.compose(b, a)

        root = binary_power(
            cast(BlockEffect | None, atom), exponent, identity=None, compose=combine
        ).value
        return BlockPower(
            effect.base,
            exponent,
            root,
            0 if root is None else root.operator_nodes(),
            operations,
            getattr(root, "depth", 1),
            BlockContextBudget(),
        )

    def _validate_program(self, effect: BlockEffect) -> None:
        """Check scoped syntax before warm interning or zero-power shortcuts."""
        if isinstance(effect, ProgramComposition):
            handle = effect.handle.validate(
                self.token, "action-program", size=len(self._nodes)
            )
            if self._nodes[handle.local_id] is not effect:
                raise ValueError(
                    "action handle does not identify its registered program"
                )
