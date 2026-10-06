"""Independent provenance and fixed-table audit of reachable input profiles.

The finite tables describe original primitive interfaces. Audit work is local
and never executes a runtime, observes a source, or changes ledger counters.
"""

from __future__ import annotations

from collections.abc import Iterator
from typing import TYPE_CHECKING, TypedDict

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSort,
    ProductSort,
    SemanticFunctionID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import FactoredFunctionID
from number_compiler.hashlife.interfaces.semantic_reachable_profile import (
    ReachableCodec,
    ReachableCodecKey,
    ReachableDecodeKey,
    SemanticProfileArena,
    SemanticProfileID,
    SemanticReachableProfile,
)
from number_compiler.hashlife.interfaces.semantic_reachable_profile import (
    _ReachableDefinition as ReachableDefinition,
)
from number_compiler.hashlife.interfaces.semantic_state_codec import CodecRequest
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructuredNode,
    StructureID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_containers import audit_mapping_items
from number_compiler.resources.stores import LedgerDict, LedgerList

if TYPE_CHECKING:
    from number_compiler.resources.semantic_payload import SemanticPayloadRegistry


class SemanticProfilePayloadRegistry:
    record_types: tuple[type[object], ...] = (
        SemanticProfileID,
        SemanticReachableProfile,
        ReachableCodec,
        ReachableCodecKey,
        ReachableDecodeKey,
    )

    def __init__(
        self, ledger: ResourceLedger, semantic: SemanticPayloadRegistry
    ) -> None:
        self.semantic = semantic
        self.valid_objects: set[int] = set()
        self.invalid_bindings: set[tuple[int, int]] = set()
        self.profiles: dict[ArenaToken, tuple[bool, ...]] = {}
        # Reuse only within this inventory pass.  The key binds the current
        # record, codec, component, and node shape so a product child or a
        # later query cannot inherit another decoder's audit result.
        self._part_audits: dict[tuple[object, ...], bool] = {}
        self._expected_profiles: dict[tuple[ArenaToken, ActionProgramID], object] = {}
        actual = dict(ledger.iter_containers())
        self.arenas = tuple(
            root
            for root in ledger.iter_execution_roots()
            if type(root) is SemanticProfileArena
            and root.ledger is ledger
            and root.runtime.ledger is ledger
            and root.runtime.semantic_functions in semantic.functions
        )
        for arena in self.arenas:
            hooks = arena.runtime.family_hooks
            profile_type = None if hooks is None else hooks.source_profile_type
            if isinstance(profile_type, type) and profile_type not in self.record_types:
                self.record_types = (*self.record_types, profile_type)
        for arena in self.arenas:
            stores = (
                (arena.node_owner, arena.nodes, LedgerList),
                (arena.key_owner, arena.keys, LedgerDict),
                (arena.records.owner, arena.records._data, LedgerDict),
                (arena.decodes.owner, arena.decodes._data, LedgerDict),
            )
            if any(
                actual.get(owner) is not store
                or type(store) is not kind
                or not ledger.is_factory_container(store)
                for owner, store, kind in stores
            ):
                self.invalid_bindings.update(
                    (owner, id(store)) for owner, store, _ in stores
                )
                continue
            checks = []
            for record in arena.nodes:
                try:
                    valid = self._profile(arena, record)
                except (ValueError, TypeError, AttributeError, IndexError, KeyError):
                    valid = False
                checks.append(valid)
                if valid:
                    self.valid_objects.update((id(record), id(record.definition)))
                else:
                    self.invalid_bindings.add((arena.node_owner, id(record)))
            self.profiles[arena.token] = tuple(checks)
            for action, handle in arena.keys.items():
                if (
                    type(action) is not ActionProgramID
                    or not self.handle(handle)
                    or handle.owner is not arena.token
                    or arena.nodes[handle.local_id].action != action
                ):
                    self.invalid_bindings.update(
                        ((arena.key_owner, id(action)), (arena.key_owner, id(handle)))
                    )
            for key, codec in audit_mapping_items(arena.records):
                try:
                    valid = self._codec(arena, key, codec)
                except (ValueError, TypeError, AttributeError, IndexError, KeyError):
                    valid = False
                if valid:
                    self.valid_objects.update(
                        (id(key), id(key.request), id(codec), id(codec.request))
                    )
                else:
                    self.invalid_bindings.update(
                        (
                            (arena.records.owner, id(key)),
                            (arena.records.owner, id(codec)),
                        )
                    )
            for decode_key, result in audit_mapping_items(arena.decodes):
                try:
                    valid = (
                        type(decode_key) is ReachableDecodeKey
                        and type(decode_key.component) is int
                        and decode_key.component in (0, 1, 2)
                        and type(decode_key.codec) is ReachableCodecKey
                        and self._codec(
                            arena, decode_key.codec, arena.records.get(decode_key.codec)
                        )
                        and self._decode(
                            arena,
                            arena.records[decode_key.codec],
                            decode_key.component,
                            result,
                        )
                    )
                except (ValueError, TypeError, AttributeError, IndexError, KeyError):
                    valid = False
                if valid:
                    self.valid_objects.update(
                        (
                            id(decode_key),
                            id(decode_key.codec),
                            id(decode_key.codec.request),
                        )
                    )
                else:
                    self.invalid_bindings.update(
                        (
                            (arena.decodes.owner, id(decode_key)),
                            (arena.decodes.owner, id(result)),
                        )
                    )

    def handle(self, value: object) -> bool:
        return (
            type(value) is SemanticProfileID
            and type(value.owner) is ArenaToken
            and type(value.kind) is str
            and value.kind == "semantic-reachable-profile"
            and type(value.local_id) is int
            and value.owner in self.profiles
            and 0 <= value.local_id < len(self.profiles[value.owner])
            and self.profiles[value.owner][value.local_id]
        )

    def valid(self, value: object) -> bool:
        return (
            self.handle(value)
            if type(value) is SemanticProfileID
            else id(value) in self.valid_objects
        )

    def _profile(
        self,
        arena: SemanticProfileArena,
        record: object,
    ) -> bool:
        hooks = arena.runtime.family_hooks
        if (
            type(record) is not SemanticReachableProfile
            or type(record.side) is not int
            or record.side != 0
            or type(record.action) is not ActionProgramID
            or hooks is None
            or hooks.source_profile_type is None
            or type(record.definition) is not hooks.source_profile_type
        ):
            return False
        definition = record.definition
        expected_key = (arena.token, record.action)
        expected = self._expected_profiles.get(expected_key)
        if expected is None:
            if not hooks.admits_source_profile(arena.runtime, record.action):
                return False
            expected = hooks.source_profile(arena.runtime, record.action)
            self._expected_profiles[expected_key] = expected
        if (
            type(definition.version) is not int
            or type(definition.initial) is not int
            or type(definition.kernel_digest) is not str
            or type(definition.digest) is not str
            or type(definition.functions) is not tuple
            or type(definition.states) is not tuple
            or type(definition.transitions) is not tuple
            or type(definition.predecessors) is not tuple
            or type(definition.profile_role) is not str
            or not definition.profile_role
            or type(definition.anchor_width) is not int
            or type(definition.primitive_left_count) is not int
            or type(definition.argument_count) is not int
            or definition.primitive_left_count < 1
            or definition.argument_count < 1
            or definition.anchor_width
            != (definition.primitive_left_count - 1).bit_length()
            or not definition.functions
            or not definition.states
            or len(definition.transitions) != len(definition.states)
            or len(definition.predecessors) != len(definition.states)
        ):
            return False
        for rows, width in (
            (definition.functions, definition.argument_count),
            (definition.transitions, 3),
            (definition.predecessors, 2),
        ):
            if any(
                type(row) is not tuple
                or len(row) != width
                or any(type(x) is not int for x in row)
                for row in rows
            ):
                return False
        if (
            any(
                type(state.anchor) is not int or type(state.continuation) is not int
                for state in definition.states
            )
            or definition != expected
        ):
            return False
        if not hooks.admits_source_profile(arena.runtime, record.action):
            return False
        node = arena.runtime.actions.resolve(record.action)
        return node.kind == "compose"

    def _codec(self, arena: SemanticProfileArena, key: object, codec: object) -> bool:
        if (
            type(key) is not ReachableCodecKey
            or not self.handle(key.profile)
            or key.profile.owner is not arena.token
            or type(key.request) is not CodecRequest
            or type(codec) is not ReachableCodec
            or codec.owner is not arena.token
            or not self.handle(codec.profile)
            or codec.profile != key.profile
            or type(codec.request) is not CodecRequest
            or codec.request != key.request
            or codec.structure is not None
            or type(codec.ports) is not tuple
            or arena.structures not in self.semantic.structures
        ):
            return False
        request = key.request
        if not _request_exact(codec.request) or not _request_exact(request):
            return False
        if (
            type(request.action) is not ActionProgramID
            or type(request.side) is not int
            or request.side != 0
            or type(request.namespace) is not PortVariable
            or request.namespace.bit != 0
        ):
            return False
        PortVariable.__post_init__(request.namespace)
        record = arena.nodes[key.profile.local_id]
        definition = arena.nodes[key.profile.local_id].definition
        role = f"{definition.profile_role}/{definition.digest}/{request.namespace.role}"
        expected = (
            FinitePort(
                PortVariable(request.namespace.time, request.namespace.side, role, 0),
                len(definition.states),
            ),
        )
        return (
            request.action == record.action
            and codec.ports == expected
            and all(
                type(port) is FinitePort
                and type(port.cardinality) is int
                and type(port.variable) is PortVariable
                and _port_exact(port.variable)
                for port in codec.ports
            )
        )

    def _decode(
        self,
        arena: SemanticProfileArena,
        codec: ReachableCodec,
        component: int,
        value: object,
    ) -> bool:
        structures = arena.structures
        if (
            structures is None
            or type(value) is not StructureID
            or value.owner is not structures.token
            or not self.semantic._structure_handle(value)
        ):
            return False
        node = structures.resolve(value)
        if node.signature.inputs != codec.ports:
            return False
        definition = arena.nodes[codec.profile.local_id].definition
        target = AtomSort("primitive-left-state", definition.primitive_left_count)
        argument = FinitePort(
            PortVariable(0, 0, "semantic-argument", 0), definition.argument_count
        )
        if component == 2:
            return (
                node.kind == "product"
                and node.signature.output
                == ProductSort((target, FunctionSort((argument,), target)))
                and len(node.components) == 2
                and all(
                    self._part(arena, codec, index, structures.resolve(child))
                    for index, child in enumerate(node.components)
                )
            )
        return self._part(arena, codec, component, node)

    def _part(
        self,
        arena: SemanticProfileArena,
        codec: ReachableCodec,
        component: int,
        node: StructuredNode,
    ) -> bool:
        definition = arena.nodes[codec.profile.local_id].definition
        key = (
            id(arena),
            id(codec),
            id(definition),
            component,
            id(node),
            node.kind,
            node.signature,
            node.atom,
            node.valid,
            node.body,
            node.components,
            node.bound,
        )
        if key in self._part_audits:
            return self._part_audits[key]
        valid = self._audit_part(arena, codec, component, node, definition)
        self._part_audits[key] = valid
        return valid

    @staticmethod
    def _audit_part(
        arena: SemanticProfileArena,
        codec: ReachableCodec,
        component: int,
        node: StructuredNode,
        definition: ReachableDefinition,
    ) -> bool:
        structures = arena.structures
        assert structures is not None
        target = AtomSort("primitive-left-state", definition.primitive_left_count)
        argument = FinitePort(
            PortVariable(0, 0, "semantic-argument", 0), definition.argument_count
        )
        if component == 1:
            if (
                node.kind != "function"
                or node.signature.output != FunctionSort((argument,), target)
                or node.body is None
                or len(node.bound) != 1
            ):
                return False
            body = structures.resolve(node.body)
            return _table_agrees(
                structures,
                body.atom,
                codec.ports[0],
                node.bound[0],
                definition,
                domain=node.valid,
            )
        return (
            node.kind == "atom"
            and node.signature.output == target
            and _table_agrees(structures, node.atom, codec.ports[0], None, definition)
        )


def _table_agrees(
    structures: StructureArena,
    value: FactoredFunctionID | None,
    code: FinitePort,
    argument: FinitePort | None,
    definition: ReachableDefinition,
    *,
    domain: SemanticFunctionID | None = None,
) -> bool:
    """Check outputs and optional parent domain in one Boolean-DAG walk."""
    if value is None:
        return False
    factored = structures.bits.resolve(value)
    functions = structures.functions
    expected_inputs = (code,) if argument is None else (code, argument)
    target = AtomSort("primitive-left-state", definition.primitive_left_count)
    if (
        len(factored.signature.inputs) != len(expected_inputs)
        or set(factored.signature.inputs) != set(expected_inputs)
        or factored.signature.output != target
    ):
        return False
    if domain is not None:
        domain_function = functions.resolve(domain)
        if (
            domain_function.signature.inputs != (code,)
            or domain_function.signature.output != BOOL
        ):
            return False
    roots = tuple(
        item.local_id
        for item in (
            *factored.bits,
            factored.valid,
            *((domain,) if domain is not None else ()),
        )
    )
    pending = [(roots, 0, 0, 0, 0)]
    visited: set[tuple[tuple[int, ...], int, int, int, int]] = set()
    while pending:
        current, code_mask, code_value, arg_mask, arg_value = pending.pop()
        visit_key = (current, code_mask, code_value, arg_mask, arg_value)
        if visit_key in visited:
            continue
        visited.add(visit_key)
        nodes = tuple(functions.nodes[index] for index in current)
        decisions = [node.variable for node in nodes if node.variable is not None]
        if decisions:
            variable = min(decisions)
            if (variable.time, variable.side, variable.role) == (
                code.variable.time,
                code.variable.side,
                code.variable.role,
            ):
                if not 0 <= variable.bit < code.bits:
                    return False
                mask, number = code_mask | 1 << variable.bit, code_value
                for bit in (0, 1):
                    child = tuple(
                        (node.high if bit else node.low)
                        if node.variable == variable
                        else index
                        for index, node in zip(current, nodes)
                    )
                    pending.append(
                        (child, mask, number | bit << variable.bit, arg_mask, arg_value)
                    )
            elif argument is not None and (
                variable.time,
                variable.side,
                variable.role,
            ) == (
                argument.variable.time,
                argument.variable.side,
                argument.variable.role,
            ):
                if not 0 <= variable.bit < argument.bits:
                    return False
                for bit in (0, 1):
                    child = tuple(
                        (node.high if bit else node.low)
                        if node.variable == variable
                        else index
                        for index, node in zip(current, nodes)
                    )
                    pending.append(
                        (
                            child,
                            code_mask,
                            code_value,
                            arg_mask | 1 << variable.bit,
                            arg_value | bit << variable.bit,
                        )
                    )
            else:
                return False
            continue
        if any(
            node.terminal is None
            or node.terminal.kind != "atom"
            or type(node.terminal.value) is not int
            for node in nodes
        ):
            return False
        terminals = tuple(node.terminal for node in nodes)
        output_count = len(factored.bits)
        observed = sum(
            terminal.value << bit
            for bit, terminal in enumerate(terminals[:output_count])
            if terminal is not None
        )
        valid_terminal = terminals[output_count]
        domain_terminal = terminals[output_count + 1] if domain is not None else None
        assert valid_terminal is not None
        valid = valid_terminal.value
        for ordinal in _cube_values(code.bits, code_mask, code_value):
            expected_domain = int(ordinal < len(definition.states))
            if domain_terminal is not None and domain_terminal.value != expected_domain:
                return False
            for selector in _cube_values(
                0 if argument is None else argument.bits, arg_mask, arg_value
            ):
                admitted = ordinal < len(definition.states) and (
                    argument is None or selector < definition.argument_count
                )
                if valid != int(admitted):
                    return False
                if admitted:
                    reachable_state = definition.states[ordinal]
                    expected = (
                        reachable_state.anchor
                        if argument is None
                        else definition.functions[reachable_state.continuation][
                            selector
                        ]
                    )
                    if observed != expected:
                        return False
    return True


def _cube_values(bits: int, mask: int, value: int) -> Iterator[int]:
    free = ((1 << bits) - 1) & ~mask
    subset = free
    while True:
        yield value | subset
        if not subset:
            return
        subset = (subset - 1) & free


def _port_exact(port: PortVariable) -> bool:
    return (
        type(port.time) is int
        and type(port.side) is int
        and type(port.bit) is int
        and type(port.role) is str
        and port.time >= 0
        and port.side in (0, 1)
        and port.bit >= 0
    )


def _request_exact(request: CodecRequest) -> bool:
    return (
        type(request.action) is ActionProgramID
        and type(request.action.local_id) is int
        and type(request.action.kind) is str
        and type(request.action.owner) is ArenaToken
        and type(request.side) is int
        and request.side == 0
        and type(request.namespace) is PortVariable
        and _port_exact(request.namespace)
        and request.namespace.bit == 0
    )


class ProfileStorageMetrics(TypedDict):
    reachable_profile_definition_records: int
    reachable_profile_definition_integer_slots: int
    reachable_profile_codec_records: int
    reachable_profile_decoder_cache_entries: int


def profile_storage_metrics(ledger: ResourceLedger) -> ProfileStorageMetrics:
    """Actual retained record/slot counts; no Python-byte estimate or node sum."""
    actual = dict(ledger.iter_containers())
    arenas = tuple(
        arena
        for arena in ledger.iter_execution_roots()
        if type(arena) is SemanticProfileArena and arena.ledger is ledger
    )
    if not arenas:
        return {
            "reachable_profile_definition_records": 0,
            "reachable_profile_definition_integer_slots": 0,
            "reachable_profile_codec_records": 0,
            "reachable_profile_decoder_cache_entries": 0,
        }
    definitions: dict[int, ReachableDefinition] = {}
    codecs = decodes = 0
    for arena in arenas:
        if actual.get(arena.node_owner) is arena.nodes:
            for record in arena.nodes:
                hooks = arena.runtime.family_hooks
                expected_type = None if hooks is None else hooks.source_profile_type
                if (
                    type(record) is SemanticReachableProfile
                    and isinstance(expected_type, type)
                    and type(record.definition) is expected_type
                ):
                    definitions[id(record.definition)] = record.definition
        if actual.get(arena.records.owner) is arena.records._data:
            codecs += len(arena.records)
        if actual.get(arena.decodes.owner) is arena.decodes._data:
            decodes += len(arena.decodes)
    slots = 0
    for definition in definitions.values():
        slots += int(type(definition.version) is int) + int(
            type(definition.initial) is int
        )
        if type(definition.states) is tuple:
            slots += sum(
                int(type(state.anchor) is int) + int(type(state.continuation) is int)
                for state in definition.states
                if type(state.anchor) is int and type(state.continuation) is int
            )
        for rows in (
            definition.functions,
            definition.transitions,
            definition.predecessors,
        ):
            if type(rows) is tuple:
                slots += sum(
                    sum(type(value) is int for value in row)
                    for row in rows
                    if type(row) is tuple
                )
    return {
        "reachable_profile_definition_records": len(definitions),
        "reachable_profile_definition_integer_slots": slots,
        "reachable_profile_codec_records": codecs,
        "reachable_profile_decoder_cache_entries": decodes,
    }
