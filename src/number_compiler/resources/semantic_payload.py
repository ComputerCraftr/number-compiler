"""Independent structural audit of the finite semantic publication boundary.

The audit walks actual index-owned containers. Familiar record names and
caller-supplied kernel digests do not establish provenance. It performs no
function reduction, primitive observation, or retained allocation.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import cast

from number_compiler.arithmetic.automata.primitive_semantics import (
    PrimitiveSemantics,
    PrimitiveSemanticsAdapter,
)
from number_compiler.arithmetic.carry.reverse_port_functions import (
    MAX_CLOSED_REVERSE_BASE,
    MIN_CLOSED_REVERSE_BASE,
    ReverseLeftTransfer,
    ReversePortFunction,
    ReverseRightTransfer,
)
from number_compiler.arithmetic.carry.reverse_sector_transfer import (
    ReverseCarrySectorTransfer,
    SectorCarrySums,
)
from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
    FunctionSort,
    ProductSort,
    SemanticFunctionID,
    SemanticNode,
    SemanticRequest,
    SemanticSort,
    SemanticTerminal,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    _signature as validate_signature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.arithmetic.radix_port_functions import (
    DivisionCarry,
    RadixPortFunction,
)
from number_compiler.arithmetic.radix_transfer import RadixRemainderTransfer
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.hashlife.interfaces.semantic_bits import (
    BinaryDivision,
    BitFunctionArena,
    FactoredFunction,
    FactoredFunctionID,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    DiamondKey,
    DiamondQuotientID,
    MacroComponents,
    MacroInterface,
    QuotientRecord,
    StructureArena,
    StructuredNode,
    StructureID,
    _aliases,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.semantic_auxiliary_payload import (
    SemanticAuxiliaryPayloadRegistry,
)
from number_compiler.resources.semantic_primitive_payload import (
    PrimitiveMacroPayloadRegistry,
)


class SemanticPayloadRegistry:
    record_types = (
        ReversePortFunction,
        ReverseLeftTransfer,
        ReverseRightTransfer,
        ReverseCarrySectorTransfer,
        SectorCarrySums,
        RadixPortFunction,
        DivisionCarry,
        RadixRemainderTransfer,
        SemanticFunctionID,
        SemanticNode,
        SemanticTerminal,
        SemanticRequest,
        FinitePort,
        AtomSort,
        ProductSort,
        FunctionSort,
        FunctionSignature,
        FactoredFunctionID,
        FactoredFunction,
        BinaryDivision,
        DiamondQuotientID,
        DiamondKey,
        MacroInterface,
        MacroComponents,
        QuotientRecord,
        PrimitiveSemantics,
        StructureID,
        StructuredNode,
    )

    def __init__(
        self,
        ledger: ResourceLedger,
        kernel_key: Callable[[object], bool],
        kernel_handle: Callable[[object], bool],
        expression_valid: Callable[[object], bool] | None = None,
    ) -> None:
        self.kernel_key, self.kernel_handle = kernel_key, kernel_handle
        self.expression_valid = expression_valid
        actual = dict(ledger.iter_containers())
        roots = tuple(ledger.iter_execution_roots())
        self.functions = tuple(
            root
            for root in roots
            if type(root) is SemanticFunctionArena
            and root.ledger is ledger
            and actual.get(root.node_owner) is root.nodes
            and actual.get(root.key_owner) is root.keys
            and actual.get(root.memo_owner) is root.memo
        )
        self.bits = tuple(
            root
            for root in roots
            if type(root) is BitFunctionArena
            and root.ledger is ledger
            and root.functions in self.functions
            and actual.get(root.node_owner) is root.nodes
            and actual.get(root.key_owner) is root.keys
        )
        self.quotients = tuple(
            root
            for root in roots
            if type(root) is DiamondQuotientArena
            and root.ledger is ledger
            and root.functions in self.functions
            and actual.get(root._node_owner) is root._nodes
            and actual.get(root._key_owner) is root._keys
        )
        self.primitives = tuple(
            root
            for root in roots
            if type(root) is PrimitiveSemanticsAdapter
            and root.ledger is ledger
            and root.functions in self.functions
            and actual.get(root.records.owner) is root.records._data
        )
        self.structures = tuple(
            root
            for root in roots
            if type(root) is StructureArena
            and root.ledger is ledger
            and root.bits in self.bits
            and actual.get(root.node_owner) is root.nodes
            and actual.get(root.key_owner) is root.keys
        )
        self.nodes: dict[int, bool] = {}
        self.terminals: dict[int, bool] = {}
        self.valid_functions: dict[object, tuple[bool, ...]] = {}
        for arena in self.functions:
            valid: list[bool] = []
            for index, node in enumerate(arena.nodes):
                accepted = self._node(arena, index, node, valid)
                valid.append(accepted)
                self.nodes[id(node)] = accepted
                if type(node) is SemanticNode and node.terminal is not None:
                    self.terminals[id(node.terminal)] = accepted
            self.valid_functions[arena.token] = tuple(valid)
        self.structure_records: dict[int, bool] = {}
        self.valid_structures: dict[object, tuple[bool, ...]] = {}
        for scope in self.structures:
            checks: list[bool] = []
            for index, structured in enumerate(scope.nodes):
                try:
                    accepted = self._structured(scope, index, structured, checks)
                except (ValueError, TypeError, AttributeError, IndexError, KeyError):
                    accepted = False
                checks.append(accepted)
                self.structure_records[id(structured)] = accepted
            self.valid_structures[scope.token] = tuple(checks)
        self.primitive_macros = PrimitiveMacroPayloadRegistry(ledger, self)
        self.primitive_macros.audit()
        self.auxiliary = SemanticAuxiliaryPayloadRegistry(ledger, self)

    def recognizes(self, value: object) -> bool:
        return (
            type(value)
            in (
                *self.record_types,
                *self.auxiliary.record_types,
                *self.primitive_macros.record_types,
            )
            or type(value) is PortSignatureID
            and value.kind == "diamond-semantic-signature"
        )

    @staticmethod
    def _signature(value: object) -> bool:
        try:
            if type(value) is not FunctionSignature:
                return False
            validate_signature(value)
            return True
        except (ValueError, TypeError, AttributeError):
            return False

    def handle(self, value: object) -> bool:
        if (
            type(value) is not SemanticFunctionID
            or type(value.owner) is not ArenaToken
            or type(value.kind) is not str
            or value.kind != "semantic-function"
            or type(value.local_id) is not int
            or value.local_id < 0
        ):
            return False
        known = self.valid_functions.get(value.owner)
        return (
            known is not None and value.local_id < len(known) and known[value.local_id]
        )

    def _node(
        self, arena: SemanticFunctionArena, index: int, node: object, prior: list[bool]
    ) -> bool:
        if (
            type(node) is not SemanticNode
            or not self._signature(node.signature)
            or type(node.support) is not tuple
            or type(node.low) is not int
            or type(node.high) is not int
            or any(type(variable) is not PortVariable for variable in node.support)
        ):
            return False
        if node.terminal is not None:
            terminal = node.terminal
            if (
                type(terminal) is not SemanticTerminal
                or node.variable is not None
                or node.low != -1
                or node.high != -1
                or node.support
                or type(terminal.references) is not tuple
                or type(terminal.value) is not int
                or type(terminal.kind) is not str
            ):
                return False
            if any(
                type(child) is not int or not 0 <= child < index or not prior[child]
                for child in terminal.references
            ):
                return False
            output = node.signature.output
            if terminal.kind == "invalid":
                return terminal.value == 0 and not terminal.references
            if terminal.kind == "atom":
                return (
                    type(output) is AtomSort
                    and 0 <= terminal.value < output.cardinality
                    and not terminal.references
                )
            if terminal.value != 0:
                return False
            if terminal.kind == "function":
                return (
                    type(output) is FunctionSort
                    and len(terminal.references) == 1
                    and arena.nodes[terminal.references[0]].signature
                    == FunctionSignature(output.inputs, output.output)
                )
            if terminal.kind == "product":
                return (
                    type(output) is ProductSort
                    and len(terminal.references) == len(output.items)
                    and all(
                        arena.nodes[child].signature == FunctionSignature((), sort)
                        for child, sort in zip(
                            terminal.references, output.items, strict=True
                        )
                    )
                )
            return False
        variable = node.variable
        if type(variable) is not PortVariable:
            return False
        try:
            PortVariable.__post_init__(variable)
        except (TypeError, ValueError):
            return False
        port = next(
            (
                port
                for port in node.signature.inputs
                if port.variable
                == PortVariable(variable.time, variable.side, variable.role, 0)
            ),
            None,
        )
        if port is None or variable.bit >= port.bits:
            return False
        if any(
            type(child) is not int or not 0 <= child < index or not prior[child]
            for child in (node.low, node.high)
        ):
            return False
        left, right = arena.nodes[node.low], arena.nodes[node.high]
        support = tuple(sorted({variable, *left.support, *right.support}))
        return (
            node.low != node.high
            and left.signature == right.signature == node.signature
            and all(variable < child for child in left.support + right.support)
            and node.support == support
        )

    def _factored(self, value: FactoredFunction) -> bool:
        if (
            not self._signature(value.signature)
            or type(value.signature.output) is not AtomSort
            or type(value.bits) is not tuple
        ):
            return False
        functions = value.bits + (value.valid,)
        if len(value.bits) != (
            value.signature.output.cardinality - 1
        ).bit_length() or not all(self.handle(fn) for fn in functions):
            return False
        owners = {fn.owner for fn in functions}
        if len(owners) != 1:
            return False
        arena = next(
            arena for arena in self.functions if arena.token is value.valid.owner
        )
        return all(
            arena.nodes[fn.local_id].signature
            == FunctionSignature(value.signature.inputs, BOOL)
            for fn in functions
        )

    def _bit_handle(self, value: object) -> bool:
        return type(value) is FactoredFunctionID and any(
            value.owner is arena.token and self._factored(arena.resolve(value))
            for arena in self.bits
        )

    def _structure_handle(self, value: object) -> bool:
        if (
            type(value) is not StructureID
            or type(value.owner) is not ArenaToken
            or type(value.kind) is not str
            or value.kind != "semantic-structure"
            or type(value.local_id) is not int
            or value.local_id < 0
        ):
            return False
        known = self.valid_structures.get(value.owner)
        return (
            known is not None and value.local_id < len(known) and known[value.local_id]
        )

    def _structured(
        self, arena: StructureArena, index: int, value: object, prior: list[bool]
    ) -> bool:
        if (
            type(value) is not StructuredNode
            or not self._signature(value.signature)
            or type(value.kind) is not str
            or type(value.components) is not tuple
            or not self._signature(FunctionSignature(value.bound, BOOL))
            or not self.handle(value.valid)
            or value.valid.owner is not arena.functions.token
            or arena.functions.signature(value.valid)
            != FunctionSignature(value.signature.inputs, BOOL)
        ):
            return False
        children = value.components + (() if value.body is None else (value.body,))
        for child in children:
            if (
                type(child) is not StructureID
                or child.owner is not arena.token
                or type(child.kind) is not str
                or child.kind != "semantic-structure"
                or type(child.local_id) is not int
                or not 0 <= child.local_id < index
                or not prior[child.local_id]
            ):
                return False
        output = value.signature.output
        if value.kind == "atom":
            return (
                type(output) is AtomSort
                and not children
                and not value.bound
                and self._bit_handle(value.atom)
                and type(value.atom) is FactoredFunctionID
                and value.atom.owner is arena.bits.token
                and arena.bits.resolve(value.atom).signature == value.signature
                and arena.bits.resolve(value.atom).valid == value.valid
            )
        if value.atom is not None:
            return False
        if value.kind == "product":
            return (
                type(output) is ProductSort
                and value.body is None
                and not value.bound
                and len(value.components) == len(output.items)
                and all(
                    arena.nodes[child.local_id].signature
                    == FunctionSignature(value.signature.inputs, sort)
                    and arena.nodes[child.local_id].valid == value.valid
                    for child, sort in zip(value.components, output.items, strict=True)
                )
            )
        if value.kind == "function":
            if (
                type(output) is not FunctionSort
                or value.components
                or value.body is None
            ):
                return False
            if value.bound != _aliases(
                value.signature.inputs, output.inputs, output.output
            ):
                return False
            joint = tuple(
                sorted(
                    value.signature.inputs + value.bound, key=lambda port: port.variable
                )
            )
            return arena.nodes[value.body.local_id].signature == FunctionSignature(
                joint, output.output
            )
        return False

    def _interface(self, value: MacroInterface) -> bool:
        if not self.kernel_key(value.kernel) and not self.primitive_macros.contract(
            value.kernel
        ):
            return False
        for arena in self.quotients:
            if (
                self.handle(value.admissible)
                and value.admissible.owner is arena.functions.token
            ):
                arena._validate_interface(value)
                return True
        return False

    def _quotient_record(self, value: QuotientRecord) -> bool:
        for arena in self.quotients:
            if value.signature.owner is arena.owner:
                arena._validate_components(value.signature, value.components)
                return self._interface(arena.interface(value.signature)) and all(
                    self._closed_function(fn)
                    if type(fn) in (RadixPortFunction, ReversePortFunction)
                    else type(fn) is StructureID
                    and self._structure_handle(fn)
                    and fn.owner is arena.structures.token
                    for fn in value.components.functions()
                )
        return False

    def _radix_function(self, value: RadixPortFunction) -> bool:
        value.__post_init__()
        return self._signature(value.signature)

    def _reverse_function(self, value: ReversePortFunction) -> bool:
        """Validate a bounded closed reverse function and its slot policy."""
        value.__post_init__()
        if (
            not MIN_CLOSED_REVERSE_BASE <= value.base <= MAX_CLOSED_REVERSE_BASE
            or not self._signature(value.signature)
            or tuple(port.cardinality for port in value.signature.inputs)
            != (4 * value.base + 3, 5)
            or value.truth_bits.bit_length() > 4 * value.base + 3
        ):
            return False
        coefficients = {
            "constant": 1,
            "left-transfer": 5,
            "right-transfer": 2,
            "output": 8,
            "predicate": 0,
        }[value.kind]
        limbs = int(value.kind == "predicate")
        return (
            value.retained_coefficient_slots == coefficients
            and value.retained_limb_slots == limbs
        )

    @staticmethod
    def _reverse_sector(value: ReverseCarrySectorTransfer) -> bool:
        """Validate the bounded transfer independently of its retained count."""
        value.__post_init__()
        expected_classes = (1, 2, 4, 8)
        if (
            value.base != 10
            or tuple(sector.classes for sector in value.sectors) != expected_classes
        ):
            return False
        limb_slots = 0
        for sector in value.sectors:
            if type(sector) is not SectorCarrySums:
                return False
            sector.__post_init__()
            limb_slots += len(sector.symbols)
            limb_slots += sum(len(row) for row in sector.before)
            limb_slots += sum(len(row) for row in sector.after)
        return limb_slots == 75 and value.retained_slots() == 76

    def _closed_function(self, value: object) -> bool:
        if type(value) is RadixPortFunction:
            return self._radix_function(value)
        if type(value) is ReversePortFunction:
            return self._reverse_function(value)
        return False

    def _request(self, value: SemanticRequest) -> bool:
        if type(value.operation) is str and value.operation == "bit-admissibility":
            return (
                type(value.roots) is tuple
                and not value.roots
                and self._signature(FunctionSignature(value.ports, BOOL))
            )
        if (
            type(value.operation) is not str
            or type(value.roots) is not tuple
            or not value.roots
            or not all(self.handle(fn) for fn in value.roots)
            or len({fn.owner for fn in value.roots}) != 1
            or not self._signature(FunctionSignature(value.ports, BOOL))
        ):
            return False
        arena = next(
            arena for arena in self.functions if arena.token is value.roots[0].owner
        )
        signatures = tuple(arena.nodes[fn.local_id].signature for fn in value.roots)
        if value.operation in ("ite", "construction-ite"):
            return (
                len(signatures) == 3
                and not value.ports
                and signatures[0].output == BOOL
                and signatures[1].output == signatures[2].output
                and (
                    value.operation == "ite"
                    or signatures[0].inputs
                    == signatures[1].inputs
                    == signatures[2].inputs
                )
            )
        if value.operation == "product":
            return not value.ports
        if value.operation == "curry":
            return len(signatures) == 1 and all(
                port in signatures[0].inputs for port in value.ports
            )
        if (
            value.operation not in ("apply", "substitute")
            or len(signatures) != len(value.ports) + 1
        ):
            return False
        domain = signatures[0].inputs
        if value.operation == "apply":
            output = signatures[0].output
            if type(output) is not FunctionSort or output.inputs != value.ports:
                return False
            domain = output.inputs
        return all(
            port in domain
            and type(signature.output) is AtomSort
            and signature.output.cardinality == port.cardinality
            for port, signature in zip(value.ports, signatures[1:], strict=True)
        )

    def valid(self, value: object) -> bool:
        try:
            return self._valid(value)
        except (ValueError, TypeError, AttributeError, IndexError, KeyError):
            return False

    def _valid(self, value: object) -> bool:
        if type(value) in (
            ReversePortFunction,
            ReverseLeftTransfer,
            ReverseRightTransfer,
            ReverseCarrySectorTransfer,
            SectorCarrySums,
            RadixPortFunction,
            DivisionCarry,
            RadixRemainderTransfer,
        ):
            if type(value) is ReversePortFunction:
                return self._reverse_function(value)
            if type(value) is ReverseLeftTransfer:
                value.__post_init__()
                return value.base == 10
            if type(value) is ReverseRightTransfer:
                value.__post_init__()
                return value.base == 10
            if type(value) is ReverseCarrySectorTransfer:
                return self._reverse_sector(value)
            if type(value) is SectorCarrySums:
                value.__post_init__()
                return True
            if type(value) is RadixPortFunction:
                return self._radix_function(value)
            if type(value) is DivisionCarry:
                value.__post_init__()
                return True
            if type(value) is RadixRemainderTransfer:
                value.__post_init__()
                return True
        if type(value) in self.primitive_macros.record_types:
            return id(value) in self.primitive_macros.valid_objects
        if type(value) in self.auxiliary.record_types:
            return self.auxiliary.valid(value)
        if type(value) is StructuredNode:
            return self.structure_records.get(id(value), False)
        if type(value) is StructureID:
            return self._structure_handle(value)
        if type(value) is SemanticFunctionID:
            return self.handle(value)
        if type(value) is SemanticNode:
            return self.nodes.get(id(value), False)
        if type(value) is SemanticTerminal:
            return self.terminals.get(id(value), False)
        if type(value) is FunctionSignature:
            return self._signature(value)
        if type(value) in (AtomSort, ProductSort, FunctionSort):
            return self._signature(FunctionSignature((), cast(SemanticSort, value)))
        if type(value) is FinitePort:
            return self._signature(FunctionSignature((value,), BOOL))
        if type(value) is SemanticRequest:
            return self._request(value)
        if type(value) is FactoredFunction:
            return self._factored(value)
        if type(value) is FactoredFunctionID:
            return self._bit_handle(value)
        if type(value) is BinaryDivision:
            return self._bit_handle(value.remainder) and self._bit_handle(
                value.quotient
            )
        if isinstance(value, (DiamondQuotientID, PortSignatureID)):
            for arena in self.quotients:
                if value.owner is not arena.owner:
                    continue
                if type(value) is DiamondQuotientID:
                    return self._quotient_record(arena.resolve(value))
                if type(value) is PortSignatureID:
                    return self._interface(arena.interface(value))
            return False
        if type(value) is MacroInterface:
            return self._interface(value)
        if type(value) is MacroComponents:
            return (
                value.reverse_sectors is None
                or type(value.reverse_sectors) is ReverseCarrySectorTransfer
                and self._reverse_sector(value.reverse_sectors)
            ) and all(
                self._closed_function(fn)
                if type(fn) in (RadixPortFunction, ReversePortFunction)
                else self._structure_handle(fn)
                for fn in value.functions()
            )
        if type(value) is QuotientRecord:
            return self._quotient_record(value)
        if type(value) is DiamondKey:
            for arena in self.quotients:
                if (
                    type(value.before) is DiamondQuotientID
                    and value.before.owner is arena.owner
                ):
                    arena._validate_key(value)
                    return (
                        self._quotient_record(arena.resolve(value.before))
                        and self._quotient_record(arena.resolve(value.after))
                        and self._interface(arena.interface(value.signature))
                    )
            return False
        if type(value) is PrimitiveSemantics:
            if not self.kernel_handle(value.kernel):
                return False
            for adapter in self.primitives:
                if any(record is value for record in adapter.records.values()):
                    kernel = adapter.kernels.kernel(value.kernel)
                    if type(value.ports) is not tuple or len(value.ports) != 3:
                        return False
                    signature = FunctionSignature(value.ports, BOOL)
                    if not self._signature(signature):
                        return False
                    if not all(
                        type(item) is int
                        for item in (
                            value.initial_left,
                            value.initial_right,
                            value.base,
                            value.blank,
                            value.blank_left_tail,
                            value.blank_right_tail,
                        )
                    ):
                        return False
                    if (
                        value.initial_left,
                        value.initial_right,
                        value.base,
                        value.blank,
                        value.blank_left_tail,
                        value.blank_right_tail,
                        value.stable_blank_output,
                    ) != (
                        kernel.initial(BoundarySide.LEFT),
                        kernel.initial(BoundarySide.RIGHT),
                        kernel.base,
                        kernel.blank,
                        kernel.effect.blank_left_tail,
                        kernel.effect.blank_right_tail,
                        kernel.effect.stable_blank_output,
                    ):
                        return False
                    expected = (
                        AtomSort("primitive-left-state", kernel.left_count),
                        AtomSort("primitive-symbol", kernel.blank + 1),
                        AtomSort("primitive-right-state", kernel.right_count),
                    )
                    if (
                        (value.left_sort, value.symbol_sort, value.right_sort)
                        != expected
                        or type(value.stable_blank_output) is not bool
                        or tuple(port.cardinality for port in value.ports)
                        != tuple(sort.cardinality for sort in expected)
                    ):
                        return False
                    for fn, output in (
                        (value.advance_left, value.left_sort),
                        (value.advance_right, value.right_sort),
                        (value.emit, value.symbol_sort),
                    ):
                        if (
                            not self.handle(fn)
                            or fn.owner is not adapter.functions.token
                        ):
                            return False
                        if adapter.functions.signature(fn) != FunctionSignature(
                            value.ports, output
                        ):
                            return False
                    return True
        return False
