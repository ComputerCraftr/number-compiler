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
from number_compiler.hashlife.interfaces.semantic_state_codec import CodecRequest
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructuredNode,
    StructureID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.physical_collatz_pair_certificate import (
        C4PairLeftCertificate,
    )
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
        actual = dict(ledger.iter_containers())
        self.arenas = tuple(
            root
            for root in ledger.iter_execution_roots()
            if type(root) is SemanticProfileArena
            and root.ledger is ledger
            and root.runtime.ledger is ledger
            and root.runtime.semantic_functions in semantic.functions
        )
        self._physical_type: type[object] | None = None
        self._certificate_type: type[object] | None = None
        self._state_type: type[object] | None = None
        self._raw_digest = ""
        expected = None
        if self.arenas:
            from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
                PhysicalCollatzFourBlockEffect,
            )
            from number_compiler.arithmetic.contracts.physical_collatz_pair_certificate import (
                RAW_DIGEST,
                C4PairLeftCertificate,
                ReachableLeftState,
                load_verified_c4_pair_left,
            )

            self._physical_type = PhysicalCollatzFourBlockEffect
            self._certificate_type = C4PairLeftCertificate
            self._state_type = ReachableLeftState
            self._raw_digest = RAW_DIGEST
            self.record_types = (*self.record_types, C4PairLeftCertificate)
            expected = load_verified_c4_pair_left()
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
                    valid = self._profile(arena, record, expected)
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
            for key, codec in arena.records._data.items():
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
            for decode_key, result in arena.decodes._data.items():
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
        expected: C4PairLeftCertificate | None,
    ) -> bool:
        certificate_type = self._certificate_type
        state_type = self._state_type
        physical_type = self._physical_type
        if (
            type(record) is not SemanticReachableProfile
            or type(record.side) is not int
            or record.side != 0
            or type(record.action) is not ActionProgramID
            or certificate_type is None
            or type(record.definition) is not certificate_type
        ):
            return False
        definition = record.definition
        if (
            type(definition.version) is not int
            or type(definition.initial) is not int
            or type(definition.kernel_digest) is not str
            or type(definition.digest) is not str
            or type(definition.functions) is not tuple
            or type(definition.states) is not tuple
            or type(definition.transitions) is not tuple
            or type(definition.predecessors) is not tuple
            or len(definition.functions) != 921
            or len(definition.states) != 1234
            or len(definition.transitions) != 1234
            or len(definition.predecessors) != 1234
        ):
            return False
        for rows, width in (
            (definition.functions, 90),
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
                type(state) is not state_type
                or type(state.anchor) is not int
                or type(state.continuation) is not int
                for state in definition.states
            )
            or definition != expected
        ):
            return False
        node = arena.runtime.actions.resolve(record.action)
        if node.kind != "compose":
            return False
        for child in (node.first, node.second):
            action = arena.runtime.actions.reference(child)
            if arena.runtime.actions.resolve(action).kind != "atom":
                return False
            effect = arena.runtime.actions.primitive(action)
            if physical_type is None or type(effect) is not physical_type:
                return False
            validate = getattr(effect, "validate", None)
            if not callable(validate):
                return False
            validate()
        return True

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
        role = f"z-reachable-c4-left/{self._raw_digest}/{request.namespace.role}"
        expected = (
            FinitePort(
                PortVariable(request.namespace.time, request.namespace.side, role, 0),
                1234,
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
        target = AtomSort("primitive-left-state", 50)
        argument = FinitePort(PortVariable(0, 0, "semantic-argument", 0), 90)
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

    @staticmethod
    def _part(
        arena: SemanticProfileArena,
        codec: ReachableCodec,
        component: int,
        node: StructuredNode,
    ) -> bool:
        structures = arena.structures
        assert structures is not None
        target = AtomSort("primitive-left-state", 50)
        argument = FinitePort(PortVariable(0, 0, "semantic-argument", 0), 90)
        definition = arena.nodes[codec.profile.local_id].definition
        if component == 1:
            if (
                node.kind != "function"
                or node.signature.output != FunctionSort((argument,), target)
                or node.body is None
                or len(node.bound) != 1
                or not _valid_domain(structures, node.valid, codec.ports[0])
            ):
                return False
            body = structures.resolve(node.body)
            return _table_agrees(
                structures, body.atom, codec.ports[0], node.bound[0], definition
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
    definition: C4PairLeftCertificate,
) -> bool:
    """Walk existing Boolean decisions and check each fixed-domain cube."""
    if value is None:
        return False
    factored = structures.bits.resolve(value)
    functions = structures.functions
    roots = tuple(item.local_id for item in (*factored.bits, factored.valid))
    pending = [(roots, 0, 0, 0, 0)]
    while pending:
        current, code_mask, code_value, arg_mask, arg_value = pending.pop()
        nodes = tuple(functions.nodes[index] for index in current)
        decisions = [node.variable for node in nodes if node.variable is not None]
        if decisions:
            variable = min(decisions)
            if (variable.time, variable.side, variable.role) == (
                code.variable.time,
                code.variable.side,
                code.variable.role,
            ):
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
        if any(node.terminal is None or node.terminal.kind != "atom" for node in nodes):
            return False
        terminals = tuple(node.terminal for node in nodes)
        observed = sum(
            terminal.value << bit
            for bit, terminal in enumerate(terminals[:-1])
            if terminal is not None
        )
        last = terminals[-1]
        assert last is not None
        valid = last.value
        for ordinal in _cube_values(code.bits, code_mask, code_value):
            for selector in _cube_values(
                0 if argument is None else argument.bits, arg_mask, arg_value
            ):
                admitted = ordinal < 1234 and (argument is None or selector < 90)
                if valid != int(admitted):
                    return False
                if admitted:
                    state = definition.states[ordinal]
                    expected = (
                        state.anchor
                        if argument is None
                        else definition.functions[state.continuation][selector]
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


def _valid_domain(
    structures: StructureArena, function: SemanticFunctionID, code: FinitePort
) -> bool:
    pending = [(function.local_id, 0, 0)]
    while pending:
        identity, mask, value = pending.pop()
        node = structures.functions.nodes[identity]
        if node.variable is not None:
            variable = node.variable
            if (variable.time, variable.side, variable.role) != (
                code.variable.time,
                code.variable.side,
                code.variable.role,
            ):
                return False
            pending.extend(
                (
                    (node.low, mask | 1 << variable.bit, value),
                    (node.high, mask | 1 << variable.bit, value | 1 << variable.bit),
                )
            )
        else:
            terminal = node.terminal
            if terminal is None or terminal.kind != "atom":
                return False
            if any(
                terminal.value != int(ordinal < 1234)
                for ordinal in _cube_values(code.bits, mask, value)
            ):
                return False
    return True


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
    from number_compiler.arithmetic.contracts.physical_collatz_pair_certificate import (
        C4PairLeftCertificate,
        ReachableLeftState,
    )

    definitions: dict[int, C4PairLeftCertificate] = {}
    codecs = decodes = 0
    for arena in arenas:
        if actual.get(arena.node_owner) is arena.nodes:
            for record in arena.nodes:
                if (
                    type(record) is SemanticReachableProfile
                    and type(record.definition) is C4PairLeftCertificate
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
                if type(state) is ReachableLeftState
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
