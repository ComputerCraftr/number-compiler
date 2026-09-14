"""Complete primitive and one-composition boundary input codecs.

For primitive A,B, State(A;B) is an anchor and an arbitrary function from the
ORIGINAL opposite A domain to the B domain. Each function entry is an
independent formal primitive port. No composed state universe is enumerated.
Storage ports are powers of two; unused codes decode to primitive ordinal0.
Original kernel domains remain unchanged. This is a total surjective encoding,
not an admission of unused ordinals to a kernel. A composition whose child is
itself composed is deliberately unsupported.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
    FunctionSignature,
    FunctionSort,
    ProductSort,
    _union_inputs,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import (
    FactoredFunctionID,
    _Circuit,
    _PendingFunction,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructuredNode,
    StructureID,
    _aliases,
    _Builder,
)
from number_compiler.resources.ledger import OwnedMemo

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


@dataclass(frozen=True, slots=True)
class CodecRequest:
    action: ActionProgramID
    side: int
    namespace: PortVariable


@dataclass(frozen=True, slots=True)
class StateCodec:
    owner: ArenaToken
    request: CodecRequest
    anchor_action: ActionProgramID
    continuation_action: ActionProgramID | None
    anchor_port: FinitePort
    anchor_cardinality: int
    continuation_cardinality: int | None
    component_ports: tuple[FinitePort, ...]
    argument_port: FinitePort | None
    ports: tuple[FinitePort, ...]
    structure: StructureID

    @property
    def encoded_bits(self) -> int:
        return sum(port.bits for port in self.ports)


@dataclass(frozen=True, slots=True)
class _Admitted:
    first: ActionProgramID
    second: ActionProgramID | None
    anchor_count: int
    opposite_count: int
    target_count: int


_DEFAULT_PORT_VARIABLE_1 = PortVariable(0, 0, "parameter", 0)


class StateCodecArena:
    def __init__(self, runtime: DiamondRuntime, structures: StructureArena) -> None:
        if (
            type(structures) is not StructureArena
            or structures.ledger is not runtime.ledger
        ):
            raise ValueError("state codec and structures must share the runtime ledger")
        self.runtime, self.structures, self.ledger = runtime, structures, runtime.ledger
        self.token = ArenaToken("semantic-state-codecs")
        self.ledger.register_execution_root(self)
        owner = self.ledger.register(
            f"semantic-state-codecs-{len(self.ledger.inventory())}",
            "semantic_state_codec",
        )
        self.records: OwnedMemo[CodecRequest, StateCodec] = OwnedMemo(
            self.ledger, owner, nodes_per_entry=1
        )

    def _admit(self, request: CodecRequest) -> _Admitted:
        return _admit_state(self.runtime, request)

    def compile(
        self,
        action: ActionProgramID,
        side: int,
        namespace: PortVariable = _DEFAULT_PORT_VARIABLE_1,
    ) -> StateCodec:
        request = CodecRequest(action, side, namespace)
        admitted = self._admit(request)
        found = self.records.get(request)
        if found is not None:
            self.ledger.bump("semantic_state_codec_hits")
            return found
        if (
            self.ledger.max_cache_entries is not None
            and self.ledger.entries >= self.ledger.max_cache_entries
        ):
            raise BlockContextBudgetExceeded("state codec needs one metadata entry")
        if (
            self.ledger.max_cache_entries is not None
            and not self.structures.nodes
            and self.ledger.entries + 2 > self.ledger.max_cache_entries
        ):
            # A fresh structure arena cannot satisfy a codec request with the
            # metadata slot alone: every codec also publishes a semantic root.
            # Reject before opening construction workspace so a failed atomic
            # publication does not alter live or peak resource accounting.
            raise BlockContextBudgetExceeded(
                "state codec needs metadata and a semantic root"
            )

        def port(role: str, count: int) -> FinitePort:
            return FinitePort(
                PortVariable(
                    namespace.time,
                    namespace.side,
                    f"state-codec/{namespace.role}/{role}",
                    0,
                ),
                count,
            )

        anchor = port("anchor", 1 << (admitted.anchor_count - 1).bit_length())
        entries = (
            ()
            if admitted.second is None
            else tuple(
                port(f"entry-{index:08}", 1 << (admitted.target_count - 1).bit_length())
                for index in range(admitted.opposite_count)
            )
        )
        ports = _union_inputs((anchor,), entries)
        argument = (
            None
            if admitted.second is None
            else FinitePort(
                PortVariable(0, 0, "semantic-argument", 0), admitted.opposite_count
            )
        )
        builder = _Builder(self.structures)
        outer = builder.circuit(ports)
        valid = outer.one
        anchor_roots = _decoded_numeric_port(outer, anchor, admitted.anchor_count)
        output = AtomSort(
            "primitive-left-state" if side == 0 else "primitive-right-state",
            admitted.anchor_count,
        )
        anchor_signature = FunctionSignature(ports, output)
        anchor_bit = builder.intern_bit(
            _PendingFunction(anchor_signature, anchor_roots, valid)
        )
        anchor_node = builder.intern(
            StructuredNode(
                anchor_signature,
                "atom",
                self.structures.functions._handle(valid),
                atom=self.structures.bits._handle(anchor_bit),
            )
        )
        root = anchor_node
        if argument is not None:
            aliases = _aliases(ports, (argument,))
            joint = _union_inputs(ports, aliases)
            circuit = builder.circuit(joint)
            selector = aliases[0]
            target = AtomSort(
                "primitive-left-state" if side == 0 else "primitive-right-state",
                admitted.target_count,
            )
            width = (admitted.target_count - 1).bit_length()
            # Each independent storage code decodes locally; no Cartesian
            # all-entry admissibility mask is distributed through the mux.
            leaves = {
                index: _decoded_numeric_port(circuit, entry, admitted.target_count)
                for index, entry in enumerate(entries)
            }
            leaves.update(
                (index, (circuit.zero,) * width)
                for index in range(len(entries), 1 << selector.bits)
            )
            body_roots = _lookup(circuit, selector, leaves)
            body_valid = _filter(circuit, selector, circuit.one)
            body_signature = FunctionSignature(joint, target)
            body_bit = builder.intern_bit(
                _PendingFunction(body_signature, body_roots, body_valid)
            )
            body = builder.intern(
                StructuredNode(
                    body_signature,
                    "atom",
                    self.structures.functions._handle(body_valid),
                    atom=self.structures.bits._handle(body_bit),
                )
            )
            function_signature = FunctionSignature(
                ports, FunctionSort((argument,), target)
            )
            function = builder.intern(
                StructuredNode(
                    function_signature,
                    "function",
                    self.structures.functions._handle(valid),
                    body=self.structures._handle(body),
                    bound=aliases,
                )
            )
            signature = FunctionSignature(
                ports, ProductSort((output, function_signature.output))
            )
            root = builder.intern(
                StructuredNode(
                    signature,
                    "product",
                    self.structures.functions._handle(valid),
                    components=(
                        self.structures._handle(anchor_node),
                        self.structures._handle(function),
                    ),
                )
            )
        from number_compiler.hashlife.interfaces.semantic_structure_publication import (
            prepare_structures,
        )

        prepared = None
        try:
            prepared = prepare_structures(builder, (root,))
            result = StateCodec(
                self.token,
                request,
                admitted.first,
                admitted.second,
                anchor,
                admitted.anchor_count,
                None if admitted.second is None else admitted.target_count,
                entries,
                argument,
                ports,
                prepared.roots[0],
            )
            prepared.reserve_with(((self.records.owner, 1, 1),))
            prepared.publish_reserved()
            self.records._data[request] = result
            self.ledger.bump("semantic_state_codec_compilations")
            self.ledger.bump(
                "semantic_state_codec_primitive_component_ports", len(ports)
            )
            return result
        finally:
            if prepared is None:
                builder.tx.close()
            else:
                prepared.cancel()

    def _validate(self, codec: StateCodec) -> None:
        if type(codec) is not StateCodec or codec.owner is not self.token:
            raise ValueError("foreign state codec")
        self._admit(codec.request)
        if self.records.get(codec.request) is not codec:
            raise ValueError("state codec metadata was not issued by this arena")
        self.structures.resolve(codec.structure)

    def anchor(self, codec: StateCodec) -> StructureID:
        self._validate(codec)
        return (
            codec.structure
            if codec.continuation_action is None
            else self.structures.component(codec.structure, 0)
        )

    def evaluate_continuation(
        self, codec: StateCodec, argument: FactoredFunctionID
    ) -> StructureID:
        self._validate(codec)
        self.structures.bits.resolve(argument)
        if codec.argument_port is None:
            raise ValueError("primitive state has no continuation")
        function = self.structures.component(codec.structure, 1)
        return self.structures.apply(function, {codec.argument_port.variable: argument})


def _filter(
    circuit: _Circuit, port: FinitePort, accepted: int, bit: int | None = None
) -> int:
    """A fixed primitive domain test with an already constructed later suffix."""
    leaves = {
        value: accepted
        if value < port.cardinality and (bit is None or value & (1 << bit))
        else circuit.zero
        for value in range(1 << port.bits)
    }
    for index in reversed(range(port.bits)):
        variable = PortVariable(
            port.variable.time, port.variable.side, port.variable.role, index
        )
        leaves = {
            prefix: circuit.tx.decision(
                circuit.signature,
                variable,
                leaves[prefix],
                leaves[prefix | (1 << index)],
            )
            for prefix in range(1 << index)
        }
    return leaves[0]


def _decoded_numeric_port(
    circuit: _Circuit, storage: FinitePort, cardinality: int
) -> tuple[int, ...]:
    """A primitive ordinal, with every unused storage code normalized to zero."""
    original = FinitePort(storage.variable, cardinality)
    return tuple(
        _filter(circuit, original, circuit.one, bit) for bit in range(storage.bits)
    )


def _lookup(
    circuit: _Circuit, selector: FinitePort, leaves: dict[int, tuple[int, ...]]
) -> tuple[int, ...]:
    for bit in reversed(range(selector.bits)):
        variable = PortVariable(
            selector.variable.time, selector.variable.side, selector.variable.role, bit
        )
        leaves = {
            prefix: tuple(
                circuit.tx.decision(circuit.signature, variable, low, high)
                for low, high in zip(leaves[prefix], leaves[prefix | (1 << bit)])
            )
            for prefix in range(1 << bit)
        }
    return leaves[0]


def _admit_state(runtime: DiamondRuntime, request: CodecRequest) -> _Admitted:
    if (
        type(request) is not CodecRequest
        or type(request.side) is not int
        or request.side not in (0, 1)
    ):
        raise ValueError("state codec requires an exact boundary direction")
    if type(request.namespace) is not PortVariable:
        raise ValueError("state codec namespace requires a typed port")
    PortVariable.__post_init__(request.namespace)
    if request.namespace.bit != 0:
        raise ValueError("state codec namespace must be a base port")
    action = runtime.actions.resolve(request.action)
    if action.kind == "atom":
        first, second = request.action, None
    elif action.kind == "compose":
        first = runtime.actions.reference(action.first)
        second = runtime.actions.reference(action.second)
        if any(
            runtime.actions.resolve(child).kind != "atom" for child in (first, second)
        ):
            raise ValueError(
                "state codec supports only two primitive children, not a composed function domain"
            )
    else:
        raise ValueError(
            "state codec requires a primitive or two-primitive composition"
        )
    kernels = runtime.higher.expressions
    a = kernels.primitive(first)
    b = None if second is None else kernels.primitive(second)
    if a is None or second is not None and b is None:
        raise ValueError("codec primitive kernels must be admitted before construction")
    side = BoundarySide(request.side)
    return _Admitted(
        first,
        second,
        len(a.domain(side)),
        len(a.domain(BoundarySide(1 - request.side))),
        0 if b is None else len(b.domain(side)),
    )


@dataclass(frozen=True, slots=True)
class StateCodecSpec:
    request: CodecRequest
    first: ActionProgramID
    second: ActionProgramID | None
    anchor_cardinality: int
    opposite_cardinality: int
    continuation_cardinality: int
    ports: tuple[FinitePort, ...]


def describe_state(
    runtime: DiamondRuntime,
    action: ActionProgramID,
    side: int,
    namespace: PortVariable = _DEFAULT_PORT_VARIABLE_1,
) -> StateCodecSpec:
    """Read-only admission and flat encoding declaration, without arena creation."""
    request = CodecRequest(action, side, namespace)
    admitted = _admit_state(runtime, request)

    def port(role: str, cardinality: int) -> FinitePort:
        return FinitePort(
            PortVariable(
                namespace.time,
                namespace.side,
                f"state-codec/{namespace.role}/{role}",
                0,
            ),
            1 << (cardinality - 1).bit_length(),
        )

    ports: tuple[FinitePort, ...] = (port("anchor", admitted.anchor_count),)
    if admitted.second is not None:
        ports += tuple(
            port(f"entry-{index:08}", admitted.target_count)
            for index in range(admitted.opposite_count)
        )
    return StateCodecSpec(
        request,
        admitted.first,
        admitted.second,
        admitted.anchor_count,
        admitted.opposite_count,
        admitted.target_count,
        ports,
    )
