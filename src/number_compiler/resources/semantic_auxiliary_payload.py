"""Read-only ownership and complete-interface audit for semantic adapters.

All lookup tables here last for one inventory snapshot. No primitive is
observed, semantic function reduced, or runtime work counter incremented.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
    FunctionSort,
    ProductSort,
    SemanticFunctionID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitSubstitutionKey,
    FactoredFunction,
    FactoredFunctionID,
)
from number_compiler.hashlife.interfaces.semantic_state_codec import (
    CodecRequest,
    StateCodec,
    StateCodecArena,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureDeclarationKey,
)
from number_compiler.projection.radix_fused_action import (
    FusedDivisionAction,
    FusedRadixArena,
    FusedRadixBindingKey,
)
from number_compiler.projection.radix_original_source import (
    OriginalAffineSummary,
    OriginalAffineSummaryKey,
    OriginalRadixArena,
    OriginalRadixKey,
    OriginalRadixSource,
    OriginalShiftTransfer,
    OriginalThreeCarryAction,
    _OriginalAffineWorkspaceInventory,
)
from number_compiler.projection.source_audit import (
    RadixProjectionAuditSource,
    RadixProjectionSourceAuditor,
    checked_projection_audit_source,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.semantic_admission_payload import (
    SemanticAdmissionPayloadRegistry,
)
from number_compiler.resources.semantic_composition_payload import (
    SemanticCompositionPayloadRegistry,
)
from number_compiler.resources.semantic_declaration_payload import (
    SemanticDeclarationPayloadRegistry,
)
from number_compiler.resources.semantic_profile_payload import (
    SemanticProfilePayloadRegistry,
)
from number_compiler.resources.stores import LedgerDict

if TYPE_CHECKING:
    from number_compiler.resources.semantic_payload import SemanticPayloadRegistry


class SemanticAuxiliaryPayloadRegistry:
    record_types = (
        CodecRequest,
        StateCodec,
        FusedDivisionAction,
        FusedRadixBindingKey,
        OriginalRadixKey,
        OriginalRadixSource,
        OriginalShiftTransfer,
        OriginalThreeCarryAction,
        OriginalAffineSummaryKey,
        OriginalAffineSummary,
        _OriginalAffineWorkspaceInventory,
        BitSubstitutionKey,
        StructureDeclarationKey,
        *SemanticAdmissionPayloadRegistry.record_types,
        *SemanticProfilePayloadRegistry.record_types,
    )

    def __init__(
        self, ledger: ResourceLedger, semantic: SemanticPayloadRegistry
    ) -> None:
        self.semantic = semantic
        self.boolean_checks: dict[tuple[SemanticFunctionID, bool], bool] = {}
        actual = dict(ledger.iter_containers())
        roots = tuple(ledger.iter_execution_roots())
        self.codecs = tuple(
            root
            for root in roots
            if type(root) is StateCodecArena
            and root.ledger is ledger
            and root.runtime.ledger is ledger
            and root.structures in semantic.structures
            and actual.get(root.records.owner) is root.records._data
        )
        self.fused = tuple(
            root
            for root in roots
            if type(root) is FusedRadixArena
            and root.ledger is ledger
            and root.functions in semantic.functions
            and actual.get(root.owner) is root.actions
        )
        self.codec_records = {
            id(record): arena
            for arena in self.codecs
            for _, record in _items(arena.records._data)
        }
        self.codec_requests = {
            id(key): (arena, record)
            for arena in self.codecs
            for key, record in _items(arena.records._data)
        }
        self.fused_records = {
            id(record): arena
            for arena in self.fused
            for key, record in _items(arena.actions)
            if key is record
        }
        self.originals = tuple(
            root
            for root in roots
            if type(root) is OriginalRadixArena
            and root.ledger is ledger
            and actual.get(root.owner) is root.sources
        )
        self.original_records: set[int] = set()
        self.original_summary_records: set[int] = set()
        self.original_workspace_records: set[int] = set()
        self.invalid_bindings: set[tuple[int, int]] = set()
        self.compositions = SemanticCompositionPayloadRegistry(ledger, semantic)
        self.invalid_bindings.update(self.compositions.invalid_bindings)
        self.declarations = SemanticDeclarationPayloadRegistry(ledger, semantic)
        self.invalid_bindings.update(self.declarations.invalid_bindings)
        self.profiles = SemanticProfilePayloadRegistry(ledger, semantic)
        self.record_types = (
            CodecRequest,
            StateCodec,
            FusedDivisionAction,
            FusedRadixBindingKey,
            OriginalRadixKey,
            OriginalRadixSource,
            OriginalShiftTransfer,
            OriginalThreeCarryAction,
            OriginalAffineSummaryKey,
            OriginalAffineSummary,
            _OriginalAffineWorkspaceInventory,
            BitSubstitutionKey,
            StructureDeclarationKey,
            *SemanticAdmissionPayloadRegistry.record_types,
            *self.profiles.record_types,
        )
        self.invalid_bindings.update(self.profiles.invalid_bindings)
        self.admissions = SemanticAdmissionPayloadRegistry(
            ledger, semantic, self.profiles
        )
        self.invalid_bindings.update(self.admissions.invalid_bindings)
        for bit_arena in semantic.bits:
            owner = bit_arena._scalar_sources.owner
            if actual.get(owner) is not bit_arena._scalar_sources._data:
                self.invalid_bindings.add((owner, id(bit_arena._scalar_sources._data)))
                continue
            for source, target in _items(bit_arena._scalar_sources._data):
                try:
                    accepted = (
                        semantic.handle(source)
                        and type(source) is SemanticFunctionID
                        and source.owner is bit_arena.functions.token
                        and semantic._bit_handle(target)
                        and type(target) is FactoredFunctionID
                        and target.owner is bit_arena.token
                    )
                    if (
                        accepted
                        and type(source) is SemanticFunctionID
                        and type(target) is FactoredFunctionID
                    ):
                        factored = bit_arena.resolve(target)
                        accepted = (
                            bit_arena.functions.signature(source) == factored.signature
                            and all(
                                fn.owner is bit_arena.functions.token
                                for fn in (*factored.bits, factored.valid)
                            )
                            and _scalar_agreement(bit_arena.functions, source, factored)
                        )
                except (ValueError, TypeError, AttributeError, IndexError):
                    accepted = False
                if not accepted:
                    self.invalid_bindings.update(
                        ((owner, id(source)), (owner, id(target)))
                    )
        for original in self.originals:
            stores = (
                (original._shift_owner, original._shift_nodes),
                (original._shift_key_owner, original._shift_keys),
                (original._carry_owner, original._carry_nodes),
                (original._carry_key_owner, original._carry_keys),
                (original._summary_owner, original._affine_summaries),
                (original._workspace_owner, original._workspace),
            )
            if (
                any(actual.get(owner) is not store for owner, store in stores)
                or type(original._workspace.entries) is not int
                or type(original._workspace.nodes) is not int
                or original._workspace.entries != 0
                or original._workspace.nodes != 0
            ):
                self.invalid_bindings.add((original.owner, id(original)))
                continue
            self.original_workspace_records.add(id(original._workspace))
            for key, record in _items(original.sources):
                try:
                    admitted = _original_encoding(key, record)
                except (ValueError, TypeError, AttributeError):
                    admitted = False
                if admitted:
                    self.original_records.update((id(key), id(record)))
                else:
                    self.invalid_bindings.update(
                        ((original.owner, id(key)), (original.owner, id(record)))
                    )
            for key, record in _items(original._shift_nodes):
                try:
                    if type(record) is OriginalShiftTransfer:
                        record.__post_init__()
                        valid = (
                            type(key) is int
                            and 0 <= key < original._next_shift
                            and original._shift_keys.get(record) == key
                        )
                    else:
                        valid = False
                except (TypeError, ValueError, KeyError, AttributeError):
                    valid = False
                if valid:
                    self.original_summary_records.update((id(key), id(record)))
                else:
                    self.invalid_bindings.add((original._shift_owner, id(record)))
            for key, record in _items(original._carry_nodes):
                try:
                    if type(record) is OriginalThreeCarryAction:
                        record.__post_init__()
                        valid = (
                            type(key) is int
                            and 0 <= key < original._next_carry
                            and original._carry_keys.get(record) == key
                        )
                    else:
                        valid = False
                except (TypeError, ValueError, KeyError, AttributeError):
                    valid = False
                if valid:
                    self.original_summary_records.update((id(key), id(record)))
                else:
                    self.invalid_bindings.add((original._carry_owner, id(record)))
            for key, record in _items(original._shift_keys):
                valid = (
                    type(key) is OriginalShiftTransfer
                    and type(record) is int
                    and original._shift_nodes.get(record) is key
                )
                if valid:
                    self.original_summary_records.update((id(key), id(record)))
                else:
                    self.invalid_bindings.add((original._shift_key_owner, id(key)))
            for key, record in _items(original._carry_keys):
                valid = (
                    type(key) is OriginalThreeCarryAction
                    and type(record) is int
                    and original._carry_nodes.get(record) is key
                )
                if valid:
                    self.original_summary_records.update((id(key), id(record)))
                else:
                    self.invalid_bindings.add((original._carry_key_owner, id(key)))
            for key, record in _items(original._affine_summaries):
                try:
                    valid = _original_affine_summary(original, key, record)
                except (ValueError, TypeError, AttributeError, IndexError, KeyError):
                    valid = False
                if valid:
                    self.original_summary_records.update((id(key), id(record)))
                else:
                    self.invalid_bindings.update(
                        (
                            (original._summary_owner, id(key)),
                            (original._summary_owner, id(record)),
                        )
                    )
        from number_compiler.projection.lazy_radix import RadixProjection

        source_records: list[RadixProjectionAuditSource] = []
        for root in roots:
            if not isinstance(root, RadixProjectionSourceAuditor):
                continue
            source = checked_projection_audit_source(root, ledger)
            if source is not None:
                source_records.append(source)
        sources = tuple(source_records)

        self.projection_maps: set[int] = set()
        for term in sources:
            store = term.projections
            if (
                type(store) is not LedgerDict
                or actual.get(store.owner) is not store
                or not ledger.is_factory_container(store)
            ):
                continue
            valid_map = True
            for radix, projection in _items(store):
                valid_entry = (
                    type(radix) is int
                    and 2 <= radix <= 1 << 63
                    and type(projection) is RadixProjection
                    and any(projection is root for root in roots)
                    and projection.ledger is ledger
                    and type(projection.radix) is int
                    and projection.radix == radix
                    and (
                        projection._bound_source is None
                        or projection._bound_source is term.source
                    )
                    and (
                        projection._bound_steps is None
                        or type(projection._bound_steps) is int
                        and projection._bound_steps == term.steps
                    )
                )
                if not valid_entry:
                    valid_map = False
                    self.invalid_bindings.update(
                        ((store.owner, id(radix)), (store.owner, id(projection)))
                    )
            if valid_map:
                self.projection_maps.add(id(store))
        self.projection_sources: set[int] = set()
        self.binding_keys: set[int] = set()
        for projection in roots:
            if (
                type(projection) is not RadixProjection
                or projection.ledger is not ledger
            ):
                continue
            terms = tuple(
                term
                for term in sources
                if term.source is projection._bound_source
                and type(term.steps) is int
                and term.steps == projection._bound_steps
            )
            if terms:
                self.projection_sources.add(id(projection))
            owner = projection._fused_actions.owner
            if actual.get(owner) is not projection._fused_actions._data:
                continue
            for key, record in _items(projection._fused_actions._data):
                try:
                    accepted = (
                        type(key) is FusedRadixBindingKey
                        and type(key.index) is int
                        and 0 <= key.index < 4
                        and type(record) is FusedDivisionAction
                        and projection._fused in self.fused
                        and self.fused_records.get(id(record)) is projection._fused
                        and self.valid(record)
                        and type(projection.radix) is int
                        and record.radix == projection.radix
                        and record.stages == key.index + 1
                        and any(
                            term.steps in (0, 1)
                            and term.seed_digits
                            and record.physical
                            == (term.steps == 1 and bool(term.seed_digits[0]))
                            and record.level == (len(term.seed_digits) + 1).bit_length()
                            for term in terms
                        )
                    )
                except (ValueError, TypeError, AttributeError, IndexError):
                    accepted = False
                if accepted:
                    self.binding_keys.add(id(key))
                else:
                    self.invalid_bindings.update(
                        ((owner, id(key)), (owner, id(record)))
                    )

    def valid(self, value: object) -> bool:
        if type(value) is StateCodec:
            arena = self.codec_records.get(id(value))
            return arena is not None and self._codec(arena, value)
        if type(value) is CodecRequest:
            if id(value) in self.profiles.valid_objects:
                return True
            found = self.codec_requests.get(id(value))
            return (
                found is not None
                and type(found[1]) is StateCodec
                and found[1].request is value
                and self._codec(found[0], found[1])
            )
        if type(value) is FusedDivisionAction:
            fused = self.fused_records.get(id(value))
            return fused is not None and self._fused(fused, value)
        if type(value) is FusedRadixBindingKey:
            return id(value) in self.binding_keys
        if type(value) in (OriginalRadixKey, OriginalRadixSource):
            return id(value) in self.original_records
        if type(value) in (
            OriginalShiftTransfer,
            OriginalThreeCarryAction,
            OriginalAffineSummaryKey,
            OriginalAffineSummary,
        ):
            return id(value) in self.original_summary_records
        if type(value) is _OriginalAffineWorkspaceInventory:
            return id(value) in self.original_workspace_records
        if type(value) is BitSubstitutionKey:
            return id(value) in self.compositions.keys
        if type(value) is StructureDeclarationKey:
            return id(value) in self.declarations.keys
        if type(value) in self.profiles.record_types:
            return self.profiles.valid(value)
        if type(value) in self.admissions.record_types:
            return id(value) in self.admissions.valid_objects
        return False

    def _codec(self, arena: StateCodecArena, value: StateCodec) -> bool:
        request = value.request
        if (
            type(value.owner) is not ArenaToken
            or value.owner is not arena.token
            or type(request) is not CodecRequest
            or type(request.action) is not ActionProgramID
            or type(request.side) is not int
            or request.side not in (0, 1)
            or type(request.namespace) is not PortVariable
            or type(value.anchor_cardinality) is not int
            or type(value.component_ports) is not tuple
            or type(value.ports) is not tuple
        ):
            return False
        PortVariable.__post_init__(request.namespace)
        if request.namespace.bit != 0:
            return False
        node = arena.runtime.actions.resolve(request.action)
        if node.kind == "atom":
            first, second = request.action, None
        elif node.kind == "compose":
            first = arena.runtime.actions.reference(node.first)
            second = arena.runtime.actions.reference(node.second)
            if any(
                arena.runtime.actions.resolve(item).kind != "atom"
                for item in (first, second)
            ):
                return False
        else:
            return False
        if (
            type(value.anchor_action) is not ActionProgramID
            or value.anchor_action != first
            or (second is None and value.continuation_action is not None)
            or (
                second is not None
                and (
                    type(value.continuation_action) is not ActionProgramID
                    or value.continuation_action != second
                )
            )
        ):
            return False
        expressions = arena.runtime.higher.expressions
        anchor_kernel = expressions.primitive(first)
        target_kernel = None if second is None else expressions.primitive(second)
        if anchor_kernel is None or second is not None and target_kernel is None:
            return False
        side = BoundarySide(request.side)
        count = len(anchor_kernel.domain(side))
        opposite = len(anchor_kernel.domain(BoundarySide(1 - request.side)))
        target_count = (
            None if target_kernel is None else len(target_kernel.domain(side))
        )
        if (
            value.anchor_cardinality != count
            or value.continuation_cardinality != target_count
            or target_count is not None
            and type(value.continuation_cardinality) is not int
        ):
            return False
        namespace = request.namespace

        def port(role: str, cardinality: int) -> FinitePort:
            return FinitePort(
                PortVariable(
                    namespace.time,
                    namespace.side,
                    f"state-codec/{namespace.role}/{role}",
                    0,
                ),
                cardinality,
            )

        anchor = port("anchor", 1 << (count - 1).bit_length())
        entries = (
            ()
            if target_count is None
            else tuple(
                port(f"entry-{index:08}", 1 << (target_count - 1).bit_length())
                for index in range(opposite)
            )
        )
        argument = (
            None
            if second is None
            else FinitePort(PortVariable(0, 0, "semantic-argument", 0), opposite)
        )
        ports = tuple(sorted((anchor, *entries), key=lambda item: item.variable))
        if (
            not self.semantic._signature(FunctionSignature(value.ports, BOOL))
            or not self.semantic._signature(
                FunctionSignature(value.component_ports, BOOL)
            )
            or type(value.anchor_port) is not FinitePort
            or not self.semantic._signature(
                FunctionSignature((value.anchor_port,), BOOL)
            )
            or value.anchor_port != anchor
            or value.component_ports != entries
            or value.ports != ports
        ):
            return False
        if argument is None:
            if value.argument_port is not None:
                return False
        elif (
            type(value.argument_port) is not FinitePort
            or not self.semantic._signature(
                FunctionSignature((value.argument_port,), BOOL)
            )
            or value.argument_port != argument
        ):
            return False
        name = "primitive-left-state" if request.side == 0 else "primitive-right-state"
        anchor_sort = AtomSort(name, count)
        output = (
            anchor_sort
            if target_count is None or argument is None
            else ProductSort(
                (anchor_sort, FunctionSort((argument,), AtomSort(name, target_count)))
            )
        )
        return (
            self.semantic._structure_handle(value.structure)
            and value.structure.owner is arena.structures.token
            and arena.structures.resolve(value.structure).signature
            == FunctionSignature(ports, output)
        )

    def _fused(self, arena: FusedRadixArena, value: FusedDivisionAction) -> bool:
        if (
            type(value.radix) is not int
            or not 2 <= value.radix <= 12
            or type(value.stages) is not int
            or not 1 <= value.stages <= 4
            or type(value.level) is not int
            or not 0 <= value.level <= 64
            or type(value.physical) is not bool
            or type(value.ports) is not tuple
            or type(value.physical_exit) is not tuple
            or len(value.physical_exit) != 2
            or type(value.division_exit) is not tuple
            or len(value.division_exit) != value.stages
            or not self.semantic._signature(FunctionSignature(value.ports, BOOL))
        ):
            return False
        expected = (
            FinitePort(PortVariable(0, 0, "radix-physical", 0), 3),
            *(
                FinitePort(PortVariable(stage + 1, 1, "radix-carry", 0), value.radix)
                for stage in range(value.stages)
            ),
            FinitePort(
                PortVariable(value.stages + 1, 0, "radix-coordinate", 0),
                1 << value.level,
            ),
        )
        if value.ports != expected or any(
            type(part) is not tuple or len(part) != expected[index + 1].bits
            for index, part in enumerate(value.division_exit)
        ):
            return False
        functions = (
            *value.physical_exit,
            *(fn for part in value.division_exit for fn in part),
            value.output,
            value.active,
            value.valid,
        )
        signature = FunctionSignature(expected, BOOL)
        if not all(
            self.semantic.handle(fn)
            and fn.owner is arena.functions.token
            and arena.functions.signature(fn) == signature
            for fn in functions
        ):
            return False
        for fn in functions:
            mode = fn == value.valid
            key = (fn, mode)
            if key not in self.boolean_checks:
                self.boolean_checks[key] = _masked_boolean(
                    arena.functions, fn, expected, exact_mask=mode
                )
            if not self.boolean_checks[key]:
                return False
        return True


def _items(container: object) -> tuple[tuple[object, object], ...]:
    # Read verified factory backing directly: Mapping.items would rehash a
    # maliciously mutated immutable key before the auditor validates it.
    if type(container) is LedgerDict and container.ledger.is_factory_container(
        container
    ):
        return tuple(container._data.items())
    return ()


def _original_encoding(key: object, record: object) -> bool:
    if (
        type(key) is not OriginalRadixKey
        or type(record) is not OriginalRadixSource
        or type(key.construction) is not OriginalSourceConstruction
        or record.construction is not key.construction
        or type(key.radix) is not int
        or type(record.radix) is not int
        or key.radix != record.radix
        or not 2 <= record.radix <= 1 << 63
        or type(key.binary_start) is not int
        or type(record.binary_start) is not int
        or key.binary_start != 0
        or record.binary_start != 0
        or type(record.digits) is not tuple
        or not record.digits
        or any(
            type(digit) is not int or not 0 <= digit < record.radix
            for digit in record.digits
        )
        or len(record.digits) > 1
        and record.digits[-1] == 0
    ):
        return False
    source = key.construction.validate_source()
    if (
        source.base != 2
        or not source.digits
        or len(record.digits) > len(source.digits)
        or any(bit not in (0, 1) for bit in source.digits)
    ):
        return False
    # Independently divide the alleged radix encoding by two, checking each
    # original source bit. Every temporary arithmetic value stays below 2**64.
    digits = list(record.digits)
    for position in range(len(source.digits)):
        bit = source.digits[position]
        carry = 0
        for index in reversed(range(len(digits))):
            digits[index], carry = divmod(carry * record.radix + digits[index], 2)
        if carry != bit:
            return False
        while len(digits) > 1 and not digits[-1]:
            digits.pop()
    return digits == [0]


def _original_affine_summary(
    arena: OriginalRadixArena,
    key: object,
    record: object,
) -> bool:
    """Validate summary ownership and every canonical dyadic composition."""
    if (
        type(key) is not OriginalAffineSummaryKey
        or type(record) is not OriginalAffineSummary
    ):
        return False
    key.__post_init__()
    record.__post_init__()
    source = next(
        (
            value
            for source_key, value in _items(arena.sources)
            if source_key == key.source
        ),
        None,
    )
    if type(source) is not OriginalRadixSource:
        return False
    count = len(source.digits)
    if record.size < count or record.size >= 2 * count or record.width > count:
        return False
    shift_nodes = tuple(arena._shift_nodes.get(item) for item in record.shift_tree)
    carry_nodes = tuple(arena._carry_nodes.get(item) for item in record.carry_tree)
    if any(type(item) is not OriginalShiftTransfer for item in shift_nodes) or any(
        type(item) is not OriginalThreeCarryAction for item in carry_nodes
    ):
        return False
    shifts = tuple(item for item in shift_nodes if type(item) is OriginalShiftTransfer)
    carries = tuple(
        item for item in carry_nodes if type(item) is OriginalThreeCarryAction
    )
    modulus = 1 << key.shift
    shift_identity = OriginalShiftTransfer(modulus, 1 % modulus, 0)
    carry_identity = OriginalThreeCarryAction((0, 1, 2))
    if shifts[0] != shift_identity or carries[0] != carry_identity:
        return False
    division_carry = 0
    expected_width = 1
    active = False
    for position in range(count - 1, -1, -1):
        total = division_carry * source.radix + source.digits[position]
        quotient, division_carry = divmod(total, modulus)
        if quotient and not active:
            expected_width, active = position + 1, True
        expected_shift = OriginalShiftTransfer(
            modulus,
            source.radix % modulus,
            source.digits[position] % modulus,
        )
        expected_carry = OriginalThreeCarryAction(
            (
                (3 * quotient) // source.radix,
                (3 * quotient + 1) // source.radix,
                (3 * quotient + 2) // source.radix,
            )
        )
        if (
            shifts[record.size + position] != expected_shift
            or carries[record.size + position] != expected_carry
        ):
            return False
    if record.width != expected_width:
        return False
    for position in range(count, record.size):
        if (
            shifts[record.size + position] != shift_identity
            or carries[record.size + position] != carry_identity
        ):
            return False
    for node in range(record.size - 1, 0, -1):
        low, high = 2 * node, 2 * node + 1
        before, after = shifts[high], shifts[low]
        expected_shift = OriginalShiftTransfer(
            modulus,
            after.multiplier * before.multiplier % modulus,
            (after.multiplier * before.offset + after.offset) % modulus,
        )
        expected_carry = OriginalThreeCarryAction(
            (
                carries[high].outputs[carries[low].outputs[0]],
                carries[high].outputs[carries[low].outputs[1]],
                carries[high].outputs[carries[low].outputs[2]],
            )
        )
        if shifts[node] != expected_shift or carries[node] != expected_carry:
            return False
    return True


def _masked_boolean(
    arena: SemanticFunctionArena,
    function: SemanticFunctionID,
    ports: tuple[FinitePort, ...],
    *,
    exact_mask: bool,
) -> bool:
    """Check totality/unused-code normalization by symbolic cubes, not tables.

    A cube has a legal point exactly when each port's fixed minimum is in its
    declared domain. It has an illegal point when any possible maximum is out.
    Coordinates therefore need no enumeration, including 64-bit coordinates.
    """
    # Power-of-two ports, especially the spatial coordinate, have no invalid
    # codes. Their assignments must not multiply the auditor's memo states.
    restricted = tuple(
        port for port in ports if port.cardinality & (port.cardinality - 1)
    )
    positions = {port.variable: index for index, port in enumerate(restricted)}
    initial = tuple((0, (1 << port.bits) - 1) for port in restricted)
    pending = [(function.local_id, initial)]
    seen: set[tuple[int, tuple[tuple[int, int], ...]]] = set()
    while pending:
        local, cube = pending.pop()
        if (local, cube) in seen:
            continue
        seen.add((local, cube))
        node = arena.nodes[local]
        if node.terminal is not None:
            if node.terminal.kind != "atom":
                return False
            legal = all(
                low < port.cardinality
                for port, (low, _) in zip(restricted, cube, strict=True)
            )
            illegal = any(
                low | remaining >= port.cardinality
                for port, (low, remaining) in zip(restricted, cube, strict=True)
            )
            if (
                node.terminal.value
                and illegal
                or exact_mask
                and not node.terminal.value
                and legal
            ):
                return False
            continue
        variable = node.variable
        if variable is None:
            return False
        index = positions.get(
            PortVariable(variable.time, variable.side, variable.role, 0)
        )
        if index is None:
            pending.extend(((node.low, cube), (node.high, cube)))
            continue
        low, remaining = cube[index]
        bit = 1 << variable.bit
        for child, value in ((node.low, low), (node.high, low | bit)):
            pending.append(
                (child, cube[:index] + ((value, remaining & ~bit),) + cube[index + 1 :])
            )
    return True


def _scalar_agreement(
    arena: SemanticFunctionArena, source: SemanticFunctionID, target: FactoredFunction
) -> bool:
    """Compare a scalar DAG to its encoded bits by simultaneous cofactors.

    Each state is a tuple of existing node IDs, not an input tuple. Shared
    cofactors are visited once; no domain table or new semantic node is made.
    """
    pending: list[tuple[int, ...]] = [
        (source.local_id, *(bit.local_id for bit in target.bits), target.valid.local_id)
    ]
    seen: set[tuple[int, ...]] = set()
    while pending:
        state = pending.pop()
        if state in seen:
            continue
        seen.add(state)
        nodes = tuple(arena.nodes[identity] for identity in state)
        variables = tuple(node.variable for node in nodes if node.variable is not None)
        if not variables:
            scalar = nodes[0].terminal
            terminals = tuple(node.terminal for node in nodes[1:])
            if scalar is None or any(
                leaf is None or leaf.kind != "atom" for leaf in terminals
            ):
                return False
            actual = tuple(leaf.value for leaf in terminals if leaf is not None)
            expected = (
                tuple((scalar.value >> bit) & 1 for bit in range(len(target.bits)))
                + (1,)
                if scalar.kind == "atom"
                else (0,) * (len(target.bits) + 1)
            )
            if scalar.kind not in ("atom", "invalid") or actual != expected:
                return False
            continue
        variable = min(variables)
        pending.append(
            tuple(
                node.low if node.variable == variable else identity
                for identity, node in zip(state, nodes, strict=True)
            )
        )
        pending.append(
            tuple(
                node.high if node.variable == variable else identity
                for identity, node in zip(state, nodes, strict=True)
            )
        )
    return True
