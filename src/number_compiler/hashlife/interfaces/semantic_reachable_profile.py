"""Explicit certified reachable inputs, separate from universal state codecs.

Only the fixed source-initial C4;C4 LEFT domain is narrowed. The decoder is a
complete finite function of its ordinal and original primitive argument; it
contains no source binding or observed future state.
"""

from __future__ import annotations

from collections.abc import MutableMapping, MutableSequence
from dataclasses import dataclass
from itertools import islice
from typing import TYPE_CHECKING, Protocol, cast

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    ArenaToken,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
    FunctionSignature,
    FunctionSort,
    ProductSort,
    union_inputs,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
from number_compiler.hashlife.interfaces.semantic_bits import BooleanCircuit
from number_compiler.hashlife.interfaces.semantic_state_codec import CodecRequest
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructureBuilder,
    StructuredNode,
    StructureID,
    allocate_bound_aliases,
)
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


class _ReachableState(Protocol):
    anchor: int
    continuation: int


class ReachableDefinition(Protocol):
    version: int
    initial: int
    kernel_digest: str
    states: tuple[_ReachableState, ...]
    functions: tuple[tuple[int, ...], ...]
    transitions: tuple[tuple[int, int, int], ...]
    predecessors: tuple[tuple[int, int], ...]
    digest: str
    profile_role: str
    anchor_width: int
    primitive_left_count: int
    argument_count: int


@dataclass(frozen=True, slots=True)
class SemanticProfileID(ArenaHandle):
    """One arena's explicit admissibility contract."""


@dataclass(frozen=True, slots=True)
class SemanticReachableProfile:
    action: ActionProgramID
    side: int
    definition: ReachableDefinition


@dataclass(frozen=True, slots=True)
class ReachableCodecKey:
    profile: SemanticProfileID
    request: CodecRequest


@dataclass(frozen=True, slots=True)
class ReachableCodec:
    owner: ArenaToken
    profile: SemanticProfileID
    request: CodecRequest
    ports: tuple[FinitePort, ...]
    structure: StructureID | None = None

    @property
    def encoded_bits(self) -> int:
        return sum(port.bits for port in self.ports)


@dataclass(frozen=True, slots=True)
class ReachableDecodeKey:
    codec: ReachableCodecKey
    component: int


class SemanticProfileArena:
    def __init__(self, runtime: DiamondRuntime) -> None:
        self.runtime, self.ledger = runtime, runtime.ledger
        self.token = ArenaToken("semantic-reachable-profiles")
        self.structures: StructureArena | None = None
        suffix = len(self.ledger.inventory())
        self.node_owner = self.ledger.register(
            f"semantic-reachable-profiles-{suffix}", "semantic_reachable_profile"
        )
        self.key_owner = self.ledger.register(
            f"semantic-reachable-profile-keys-{suffix}", "semantic_reachable_profile"
        )
        self.nodes: MutableSequence[SemanticReachableProfile] = self.ledger.make_list(
            self.node_owner
        )
        self.keys: MutableMapping[ActionProgramID, SemanticProfileID] = (
            self.ledger.make_dict(self.key_owner)
        )
        owner = self.ledger.register(
            f"semantic-reachable-codecs-{suffix}", "semantic_reachable_codec"
        )
        self.records: OwnedMemo[ReachableCodecKey, ReachableCodec] = OwnedMemo(
            self.ledger, owner, nodes_per_entry=1
        )
        decode_owner = self.ledger.register(
            f"semantic-reachable-decodes-{suffix}", "semantic_reachable_decode"
        )
        self.decodes: OwnedMemo[ReachableDecodeKey, StructureID] = OwnedMemo(
            self.ledger, decode_owner
        )
        self.ledger.register_execution_root(self)

    def source_initial_profile(self, action: ActionProgramID) -> SemanticProfileID:
        hooks = self.runtime.family_hooks
        if hooks is None or not hooks.admits_source_profile(self.runtime, action):
            raise UnsupportedInterfaceError(
                "family has no certified reachable profile for this action"
            )
        found = self.keys.get(action)
        if found is not None:
            self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_PROFILE_REQUESTS)
            self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_PROFILE_HITS)
            return found
        self.ledger.reserve_many(((self.node_owner, 1, 1), (self.key_owner, 1, 0)))
        self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_PROFILE_REQUESTS)
        self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_PROFILE_EVALUATIONS)
        try:
            definition = cast(
                ReachableDefinition,
                hooks.source_profile(self.runtime, action),
            )
        except BaseException:
            self.ledger.release(self.node_owner, entries=1, nodes=1)
            self.ledger.release(self.key_owner, entries=1)
            raise
        profile = SemanticProfileID(
            self.token, "semantic-reachable-profile", len(self.nodes)
        )
        self.nodes.append(SemanticReachableProfile(action, 0, definition))
        self.keys[action] = profile
        self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_PROFILE_ADMISSIONS)
        return profile

    def resolve(self, profile: SemanticProfileID) -> SemanticReachableProfile:
        if type(profile) is not SemanticProfileID:
            raise ValueError("reachable profile needs its exact scoped ID type")
        profile.validate(self.token, "semantic-reachable-profile", size=len(self.nodes))
        return self.nodes[profile.local_id]

    def ports(
        self,
        profile: SemanticProfileID,
        action: ActionProgramID,
        side: int,
        namespace: PortVariable,
    ) -> tuple[FinitePort, ...]:
        record = self.resolve(profile)
        if type(side) is not int or side not in (0, 1):
            raise ValueError("reachable profile requires an exact side")
        if type(namespace) is not PortVariable:
            raise ValueError("reachable profile requires a typed namespace")
        PortVariable.__post_init__(namespace)
        if namespace.bit != 0:
            raise ValueError("reachable namespace must be a base port")
        node = self.runtime.actions.resolve(action)
        if node.kind == "atom":
            primitive = self.runtime.higher.expressions.primitive(action)
            if primitive is None:
                raise UnsupportedInterfaceError(
                    "primitive profile domain must already be admitted"
                )
            return (FinitePort(namespace, len(primitive.domain(BoundarySide(side)))),)
        hooks = self.runtime.family_hooks
        if (
            action != record.action
            or side != record.side
            or hooks is None
            or not hooks.admits_source_profile(self.runtime, action)
        ):
            raise UnsupportedInterfaceError(
                "profile has no certified domain for this composed input"
            )
        role = f"{record.definition.profile_role}/{record.definition.digest}/{namespace.role}"
        return (
            FinitePort(
                PortVariable(namespace.time, namespace.side, role, 0),
                len(record.definition.states),
            ),
        )

    def binding(
        self,
        profile: SemanticProfileID,
        action: ActionProgramID,
        side: int,
        namespace: PortVariable,
        structures: StructureArena,
    ) -> FinitePort | ReachableCodec:
        ports = self.ports(profile, action, side, namespace)
        if (
            type(structures) is not StructureArena
            or structures.ledger is not self.ledger
        ):
            raise ValueError("reachable decoder needs the runtime structure arena")
        if self.structures is not None and structures is not self.structures:
            raise ValueError("reachable decoder belongs to another structure arena")
        if self.runtime.actions.resolve(action).kind == "atom":
            self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_CODEC_REQUESTS)
            self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_CODEC_PRIMITIVE_PORTS)
            return ports[0]
        key = ReachableCodecKey(profile, CodecRequest(action, side, namespace))
        found = self.records.get(key)
        if found is not None:
            self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_CODEC_REQUESTS)
            self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_CODEC_HITS)
            return found
        if (
            self.ledger.max_cache_entries is not None
            and self.ledger.entries >= self.ledger.max_cache_entries
        ):
            raise BlockContextBudgetExceeded(
                "reachable decoder needs one metadata entry"
            )
        result = ReachableCodec(self.token, profile, key.request, ports)
        self.records[key] = result
        self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_CODEC_REQUESTS)
        self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_CODEC_EVALUATIONS)
        self.structures = structures
        return result

    def component(
        self, codec: ReachableCodec, index: int, structures: StructureArena
    ) -> StructureID:
        self.validate_codec(codec, structures)
        if type(index) is not int or index not in (0, 1):
            raise ValueError("reachable state has exactly two components")
        key = ReachableDecodeKey(ReachableCodecKey(codec.profile, codec.request), index)
        found = self._lookup_decode(key)
        if found is not None:
            return found
        definition = self.resolve(codec.profile).definition
        ports = codec.ports
        builder = StructureBuilder(structures)
        outer = builder.circuit(ports)
        code = ports[0]
        valid = self._filter(outer, code, outer.one)
        target = AtomSort("primitive-left-state", definition.primitive_left_count)
        if index == 0:
            anchor_leaves = {
                index: tuple(
                    outer.one
                    if index < len(definition.states)
                    and definition.states[index].anchor & (1 << bit)
                    else outer.zero
                    for bit in range(definition.anchor_width)
                )
                for index in range(1 << code.bits)
            }
            self._table_work(
                len(anchor_leaves),
                definition.anchor_width,
                len(definition.states),
                len(anchor_leaves),
            )
            roots = self._lookup(outer, code, anchor_leaves)
            signature = FunctionSignature(ports, target)
            root = builder.atom(signature, roots, valid)
            self.ledger.bump(
                _interfaces_keys.SEMANTIC_REACHABLE_DECODER_TABLE_CELLS,
                len(definition.states),
            )
            return self._publish_decode(builder, root, key)
        argument = FinitePort(
            PortVariable(0, 0, "semantic-argument", 0),
            definition.argument_count,
        )
        aliases = allocate_bound_aliases(ports, (argument,))
        joint = union_inputs(ports, aliases)
        circuit = builder.circuit(joint)
        selector = aliases[0]
        # The selector precedes the outer ordinal in canonical binder order.
        # Build each fixed table column once, then select it by the primitive
        # argument. This traverses only the admitted immutable certificate.
        columns: dict[int, tuple[int, ...]] = {}
        tables = _FixedTableLookup(self, circuit, code, definition.anchor_width)
        for value in range(1 << selector.bits):
            values = (
                tuple(
                    definition.functions[state.continuation][value]
                    for state in definition.states
                )
                + (0,) * ((1 << code.bits) - len(definition.states))
                if value < definition.argument_count
                else (0,) * (1 << code.bits)
            )
            self.ledger.bump(
                _interfaces_keys.SEMANTIC_REACHABLE_DECODER_PADDED_LEAF_ROWS,
                len(values),
            )
            self.ledger.bump(
                _interfaces_keys.SEMANTIC_REACHABLE_DECODER_CERTIFICATE_WORD_READS,
                len(definition.states) if value < definition.argument_count else 0,
            )
            self.record_peak(
                "semantic_reachable_decoder_numeric_column_slots_peak",
                len(values) * (2 if value else 1),
            )
            columns[value] = tables.compile(values)
            self.ledger.bump(
                _interfaces_keys.SEMANTIC_REACHABLE_DECODER_TABLE_CELLS,
                len(definition.states) if value < definition.argument_count else 0,
            )
        body_roots = self._lookup(circuit, selector, columns)
        body_valid = circuit.conjunction(
            self._filter(circuit, code, circuit.one),
            self._filter(circuit, selector, circuit.one),
        )
        function_signature = FunctionSignature(ports, FunctionSort((argument,), target))
        function = builder.numeric_function(
            function_signature, joint, body_roots, body_valid, valid, aliases
        )
        return self._publish_decode(builder, function, key)

    def _publish_decode(
        self, builder: StructureBuilder, root: int, key: ReachableDecodeKey
    ) -> StructureID:
        from number_compiler.hashlife.interfaces.semantic_structure_publication import (
            prepare_structures,
        )

        prepared = None
        try:
            prepared = prepare_structures(builder, (root,))
            prepared.reserve_with(((self.decodes.owner, 1, 0),))
            prepared.publish_reserved()
            self.decodes.publish_reserved(key, prepared.roots[0])
            self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_DECODER_COMPILATIONS)
            return prepared.roots[0]
        finally:
            if prepared is None:
                builder.tx.close()
            else:
                prepared.cancel()

    def _lookup_decode(self, key: ReachableDecodeKey) -> StructureID | None:
        found = self.decodes.get(key)
        if found is not None:
            self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_DECODER_REQUESTS)
            self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_DECODER_HITS)
            return found
        if (
            self.ledger.max_cache_entries is not None
            and self.ledger.entries >= self.ledger.max_cache_entries
        ):
            raise BlockContextBudgetExceeded(
                "reachable decoder needs one metadata entry"
            )
        self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_DECODER_REQUESTS)
        self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_DECODER_EVALUATIONS)
        return None

    def decode(self, codec: ReachableCodec, structures: StructureArena) -> StructureID:
        self.validate_codec(codec, structures)
        key = ReachableDecodeKey(ReachableCodecKey(codec.profile, codec.request), 2)
        found = self._lookup_decode(key)
        if found is not None:
            return found
        first = self.component(codec, 0, structures)
        second = self.component(codec, 1, structures)
        builder = StructureBuilder(structures)
        circuit = builder.circuit(codec.ports)
        valid = self._filter(circuit, codec.ports[0], circuit.one)
        signature = FunctionSignature(
            codec.ports,
            ProductSort(
                (
                    structures.resolve(first).signature.output,
                    structures.resolve(second).signature.output,
                )
            ),
        )
        root = builder.intern(
            StructuredNode(
                signature,
                "product",
                builder.function_reference(valid),
                components=(first, second),
            )
        )
        return self._publish_decode(builder, root, key)

    def record_peak(self, name: str, value: int) -> None:
        self.ledger.counters[name] = max(self.ledger.counters.get(name, 0), value)

    def _table_work(
        self, padded_rows: int, width: int, valid_rows: int, live_rows: int
    ) -> None:
        self.ledger.bump(
            _interfaces_keys.SEMANTIC_REACHABLE_DECODER_PADDED_LEAF_ROWS,
            padded_rows,
        )
        self.ledger.bump(
            _interfaces_keys.SEMANTIC_REACHABLE_DECODER_LEAF_BIT_SLOTS,
            padded_rows * width,
        )
        self.ledger.bump(
            _interfaces_keys.SEMANTIC_REACHABLE_DECODER_CERTIFICATE_BIT_TESTS,
            valid_rows * width,
        )
        self.record_peak("semantic_reachable_decoder_local_rows_peak", live_rows)
        self.record_peak(
            "semantic_reachable_decoder_local_bit_references_peak", live_rows * width
        )

    def _lookup(
        self,
        circuit: BooleanCircuit,
        selector: FinitePort,
        leaves: dict[int, tuple[int, ...]],
        *,
        retained_rows: int = 0,
    ) -> tuple[int, ...]:
        # Caller retains the initial table during all reduction levels. Count
        # it once while shared, separately after the first replacement.
        original = leaves
        width = len(leaves[0])
        for bit in reversed(range(selector.bits)):
            count = 1 << bit
            live = (
                retained_rows
                + len(leaves)
                + count
                + (0 if leaves is original else len(original))
            )
            self.record_peak("semantic_reachable_decoder_local_rows_peak", live)
            self.record_peak(
                "semantic_reachable_decoder_local_bit_references_peak", live * width
            )
            self.ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_DECODER_LOOKUP_LEVELS)
            self.ledger.bump(
                _interfaces_keys.SEMANTIC_REACHABLE_DECODER_LOOKUP_ROWS,
                count,
            )
            self.ledger.bump(
                _interfaces_keys.SEMANTIC_REACHABLE_DECODER_LOOKUP_DECISIONS,
                count * width,
            )
            variable = PortVariable(
                selector.variable.time,
                selector.variable.side,
                selector.variable.role,
                bit,
            )
            leaves = {
                prefix: tuple(
                    circuit.tx.decision(circuit.signature, variable, low, high)
                    for low, high in zip(
                        leaves[prefix], leaves[prefix | (1 << bit)], strict=True
                    )
                )
                for prefix in range(count)
            }
        return leaves[0]

    def _filter(self, circuit: BooleanCircuit, port: FinitePort, accepted: int) -> int:
        size = 1 << port.bits
        self.ledger.bump(
            _interfaces_keys.SEMANTIC_REACHABLE_DECODER_DOMAIN_LEAF_ROWS,
            size,
        )
        self.record_peak("semantic_reachable_decoder_domain_references_peak", size)
        leaves = {
            value: accepted if value < port.cardinality else circuit.zero
            for value in range(size)
        }
        for bit in reversed(range(port.bits)):
            count = 1 << bit
            self.record_peak(
                "semantic_reachable_decoder_domain_references_peak", len(leaves) + count
            )
            self.ledger.bump(
                _interfaces_keys.SEMANTIC_REACHABLE_DECODER_DOMAIN_LOOKUP_ROWS,
                count,
            )
            variable = PortVariable(
                port.variable.time, port.variable.side, port.variable.role, bit
            )
            leaves = {
                prefix: circuit.tx.decision(
                    circuit.signature,
                    variable,
                    leaves[prefix],
                    leaves[prefix | (1 << bit)],
                )
                for prefix in range(count)
            }
        return leaves[0]

    def validate_codec(self, codec: ReachableCodec, structures: StructureArena) -> None:
        if type(codec) is not ReachableCodec or codec.owner is not self.token:
            raise ValueError("foreign reachable codec")
        if type(structures) is not StructureArena or structures is not self.structures:
            raise ValueError("reachable codec belongs to another structure arena")
        expected = self.ports(
            codec.profile,
            codec.request.action,
            codec.request.side,
            codec.request.namespace,
        )
        key = ReachableCodecKey(codec.profile, codec.request)
        if self.records.get(key) is not codec or codec.ports != expected:
            raise ValueError("reachable codec was not issued by this arena")


class _FixedTableLookup:
    """Transient, source-independent cofactor sharing for one fixed table.

    Keys contain only immutable certified table columns and their bit level.
    They are never retained by an index or associated with source coordinates.
    A duplicate column/subtable is looked up before constructing its children.
    """

    def __init__(
        self,
        arena: SemanticProfileArena,
        circuit: BooleanCircuit,
        port: FinitePort,
        width: int,
    ) -> None:
        self.arena, self.circuit, self.port, self.width = arena, circuit, port, width
        self.memo: dict[tuple[int, tuple[int, ...]], tuple[int, ...]] = {}
        self.value_slots = 0

    def compile(self, values: tuple[int, ...]) -> tuple[int, ...]:
        root = (0, values)
        pending: list[tuple[tuple[int, tuple[int, ...]], bool]] = [(root, False)]
        pending_slots = len(values)
        ledger, circuit = self.arena.ledger, self.circuit
        while pending:
            self.arena.record_peak(
                "semantic_reachable_decoder_subtable_pending_frames_peak", len(pending)
            )
            self.arena.record_peak(
                "semantic_reachable_decoder_subtable_pending_value_slots_peak",
                pending_slots,
            )
            (bit, table), ready = pending.pop()
            pending_slots -= len(table)
            key = (bit, table)
            ledger.bump(_interfaces_keys.SEMANTIC_REACHABLE_DECODER_SUBTABLE_FRAMES)
            ledger.bump(
                _interfaces_keys.SEMANTIC_REACHABLE_DECODER_SUBTABLE_KEY_VALUE_HASH_VISITS,
                len(table),
            )
            if key in self.memo:
                ledger.bump(
                    _interfaces_keys.SEMANTIC_REACHABLE_DECODER_SUBTABLE_EARLY_HITS
                )
                continue
            if ready:
                ledger.bump(
                    _interfaces_keys.SEMANTIC_REACHABLE_DECODER_SUBTABLE_CREATED_VALUE_SLOTS,
                    len(table),
                )
                ledger.bump(
                    _interfaces_keys.SEMANTIC_REACHABLE_DECODER_SUBTABLE_KEY_VALUE_HASH_VISITS,
                    len(table),
                )
                low = self.memo[(bit + 1, table[::2])]
                high = self.memo[(bit + 1, table[1::2])]
                if low == high:
                    result = low
                    ledger.bump(
                        _interfaces_keys.SEMANTIC_REACHABLE_DECODER_SUBTABLE_EQUAL_CHILDREN
                    )
                else:
                    variable = PortVariable(
                        self.port.variable.time,
                        self.port.variable.side,
                        self.port.variable.role,
                        bit,
                    )
                    result = tuple(
                        circuit.tx.decision(circuit.signature, variable, left, right)
                        for left, right in zip(low, high, strict=True)
                    )
                    ledger.bump(
                        _interfaces_keys.SEMANTIC_REACHABLE_DECODER_SUBTABLE_BIT_DECISIONS,
                        self.width,
                    )
            else:
                ledger.bump(
                    _interfaces_keys.SEMANTIC_REACHABLE_DECODER_SUBTABLE_EVALUATIONS
                )
                first = table[0]
                uniform = True
                compared = 0
                for value in islice(table, 1, None):
                    compared += 1
                    if value != first:
                        uniform = False
                        break
                ledger.bump(
                    _interfaces_keys.SEMANTIC_REACHABLE_DECODER_SUBTABLE_UNIFORM_COMPARISONS,
                    compared,
                )
                if uniform:
                    result = tuple(
                        circuit.one if first & (1 << index) else circuit.zero
                        for index in range(self.width)
                    )
                    ledger.bump(
                        _interfaces_keys.SEMANTIC_REACHABLE_DECODER_CERTIFICATE_BIT_TESTS,
                        self.width,
                    )
                    ledger.bump(
                        _interfaces_keys.SEMANTIC_REACHABLE_DECODER_SUBTABLE_CONSTANTS
                    )
                else:
                    low_key, high_key = (bit + 1, table[::2]), (bit + 1, table[1::2])
                    ledger.bump(
                        _interfaces_keys.SEMANTIC_REACHABLE_DECODER_SUBTABLE_CREATED_VALUE_SLOTS,
                        len(table),
                    )
                    pending.extend(((key, True), (high_key, False), (low_key, False)))
                    pending_slots += len(table) * 2
                    continue
            ledger.bump(
                _interfaces_keys.SEMANTIC_REACHABLE_DECODER_SUBTABLE_KEY_VALUE_HASH_VISITS,
                len(table),
            )
            self.memo[key] = result
            self.value_slots += len(table)
            self.arena.record_peak(
                "semantic_reachable_decoder_subtable_memo_keys_peak", len(self.memo)
            )
            self.arena.record_peak(
                "semantic_reachable_decoder_subtable_memo_value_slots_peak",
                self.value_slots,
            )
            self.arena.record_peak(
                "semantic_reachable_decoder_subtable_memo_result_references_peak",
                len(self.memo),
            )
        ledger.bump(
            _interfaces_keys.SEMANTIC_REACHABLE_DECODER_SUBTABLE_KEY_VALUE_HASH_VISITS,
            len(values),
        )
        return self.memo[root]
