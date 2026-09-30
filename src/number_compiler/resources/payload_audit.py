"""Payload audit with one canonical implementation owner."""

from __future__ import annotations

from collections.abc import Iterator, Mapping, Sequence
from dataclasses import fields, is_dataclass
from typing import TYPE_CHECKING, TypeGuard, cast

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.block_effect import BlockEffect, _effect_key
from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaHandle,
    ArenaToken,
    CarryBit,
    ExactEndpoint,
    ExactSource,
    FrameTransform,
    LoweringCapability,
    TransferSummaryID,
    WordLimb,
)
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.dyadic_tile import DyadicSpan, DyadicTile
from number_compiler.resources.cache_gc_metrics import cache_event_owner_audit
from number_compiler.resources.callback_payload_audit import (
    audit_callback_future_payloads,
)
from number_compiler.resources.ledger import LedgerSnapshot, OwnedMemo, ResourceLedger
from number_compiler.resources.numeric_payload import numeric_aggregate_audit
from number_compiler.resources.payload_containers import audit_mapping_items
from number_compiler.resources.payload_schema import valid_semantic_record
from number_compiler.resources.proof_payload_admission import (
    audit_registered_proof_payloads,
    proof_geometry_fields,
    proof_opaque_types,
)
from number_compiler.resources.proof_payload_admission import (
    proof_objects as _proof_objects,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
        PhysicalCollatzFourBlockEffect,
    )
    from number_compiler.resources.payload_policy import PayloadAudit


def audit_registered_payloads(
    ledger: ResourceLedger,
    *,
    snapshot: LedgerSnapshot | None = None,
    fresh: bool = True,
) -> PayloadAudit:
    """Inspect retained objects rather than slot names. IDs may be arbitrarily large.
    Arithmetic data must fit local words. Sources and lowered endpoints have separate
    roles and are not lazy summaries. Unknown representations remain visible.
    """
    from number_compiler.resources.payload_policy import (
        _DIGIT_FIELDS,
        _HISTORY_FIELDS,
        PayloadAudit,
        _role,
    )

    execution_roots = tuple(ledger.iter_execution_roots())
    root_signature = ledger.audit_root_signature() if not fresh else None
    if not fresh:
        cached = ledger.cached_payload_audit(root_signature)
        if type(cached) is PayloadAudit:
            return cached
    elif not execution_roots:
        cached = ledger.cached_payload_audit()
        if type(cached) is PayloadAudit:
            return cached
    audit_version = ledger.mutation_version
    from number_compiler.arithmetic.contracts.block_kernel import (
        BaseBlockEffect,
        FiniteBlockEffect,
        _BaseLeftState,
        _BaseRightState,
    )
    from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
    from number_compiler.arithmetic.functions.finite_port_action import (
        PortComponent,
        PortVariable,
        _ChoiceIndexKey,
    )
    from number_compiler.arithmetic.functions.finite_port_substitution import (
        SubstitutionKey,
        _PortIndexComponent,
        _SubstitutionIndexKey,
    )
    from number_compiler.arithmetic.radix_division import SymbolicBinaryDivisionEffect
    from number_compiler.hashlife.actions.lazy_compiler import ProgramComposition
    from number_compiler.hashlife.execution.continuations.concrete_port_scheduler import (
        ConcretePortScheduler,
    )
    from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
        ResolveExpr,
    )
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.execution.continuations.higher_primitive_tables import (
        HigherPrimitiveTables,
    )
    from number_compiler.hashlife.execution.diamond_payload import (
        DiamondPayloadRegistry,
    )
    from number_compiler.hashlife.execution.field_images import RecursiveFieldImageArena
    from number_compiler.hashlife.execution.field_transfers import FieldTransferArena
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID
    from number_compiler.hashlife.interfaces.diamond_kernel import (
        PrimitiveKernel,
    )
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondQuotientArena,
        LocalInterfaceID,
    )
    from number_compiler.hashlife.observation.diamond_observers import (
        NonblankBlockEffect,
    )
    from number_compiler.hashlife.tiles.tile_behavior_memo import (
        _validate_published as validate_published_behavior,
    )
    from number_compiler.hashlife.tiles.tile_result_records import (
        BehaviorBindingKey,
        CompletedBehaviorClassification,
    )
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
    from number_compiler.projection.digit_terminal import (
        DigitNormalizeBlockEffect,
        _DigitLeftState,
    )
    from number_compiler.projection.lazy_radix import RadixProjection
    from number_compiler.projection.microblock_cache import (
        ExactMicroblock,
        MicroblockCache,
        MicroblockKey,
    )
    from number_compiler.projection.point_response import (
        PointResponse,
        PointResponseRegister,
    )
    from number_compiler.resources.associated_action_payload_audit import (
        audit_associated_action_payloads,
    )
    from number_compiler.resources.behavior_payload_audit import (
        BehaviorPayloadValidator,
    )
    from number_compiler.resources.field_action_payload_audit import (
        audit_field_action_payloads,
    )
    from number_compiler.resources.field_image_payload_audit import (
        audit_field_image_payloads,
    )
    from number_compiler.resources.finite_port_payload_audit import audit_finite_ports
    from number_compiler.resources.higher_payload_audit import audit_higher_payloads
    from number_compiler.resources.higher_primitive_payload import (
        valid_higher_primitive_table,
    )
    from number_compiler.resources.radix_provider_payload_audit import (
        audit_radix_provider_payloads,
    )
    from number_compiler.resources.reverse_source_payload_audit import (
        audit_reverse_source_payloads,
    )
    from number_compiler.resources.semantic_payload import SemanticPayloadRegistry
    from number_compiler.resources.source_bound_payload_audit import (
        audit_source_bound_payloads,
    )
    from number_compiler.resources.support_payload_audit import (
        audit_support_payloads,
    )
    from number_compiler.resources.tile_dependency_leases import (
        audit_tile_dependency_leases,
    )
    from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect

    def physical_four(value: object) -> TypeGuard[PhysicalCollatzFourBlockEffect]:
        if type(value).__name__ != "PhysicalCollatzFourBlockEffect":
            return False
        from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
            PhysicalCollatzFourBlockEffect,
        )

        return type(value) is PhysicalCollatzFourBlockEffect

    diamond = DiamondPayloadRegistry(ledger)
    from number_compiler.resources.payload_geometry import geometry_field_policy

    geometry_fields = geometry_field_policy()
    geometry_fields.update(proof_geometry_fields())
    literal_types = (
        BaseBlockEffect,
        FiniteBlockEffect,
        DigitNormalizeBlockEffect,
        CollatzPhysicalBlockEffect,
        NonblankBlockEffect,
        SymbolicBinaryDivisionEffect,
    )
    roles = {item.owner: _role(item.role) for item in ledger.inventory()}
    seen: set[tuple[int, int]] = set()
    forbidden: set[tuple[int, int]] = set()
    cache_event_owners, cache_event_invalid = cache_event_owner_audit(
        execution_roots,
        ledger,
    )
    forbidden.update(cache_event_invalid)
    field_actions = audit_field_action_payloads(ledger)
    field_images = audit_field_image_payloads(ledger)
    radix_providers = audit_radix_provider_payloads(ledger)
    higher_payloads = audit_higher_payloads(ledger)
    from number_compiler.resources.payload_owner_scopes import field_owner_scopes

    support_payloads = audit_support_payloads(ledger)
    forbidden.update(field_actions.invalid)
    forbidden.update(field_images.invalid)
    forbidden.update(radix_providers.invalid)
    forbidden.update(higher_payloads.invalid)
    forbidden.update(support_payloads.invalid)
    forbidden.update(audit_registered_proof_payloads(ledger))
    forbidden.update(audit_callback_future_payloads(ledger))
    concrete_private_index_owners = {
        owner
        for root in execution_roots
        if type(root) is ConcretePortScheduler and root.ledger is ledger
        for owner in (root._virtual_owner, root._virtual_key_owner)
    }
    quotient_scopes = {
        root.owner: root
        for root in execution_roots
        if type(root) is DiamondQuotientArena and root.ledger is ledger
    }
    action_owners, output_owners = field_owner_scopes(execution_roots)
    for root in execution_roots:
        if type(root) is RecursiveFieldImageArena:
            image_carrier = root
            action_owner = image_carrier.action_owner
            output_owner = image_carrier.output_owner
            node_owner = image_carrier._node_owner
        elif type(root) is FieldTransferArena:
            transfer_carrier = root
            action_owner = transfer_carrier.action_owner
            output_owner = transfer_carrier.output_owner
            node_owner = transfer_carrier._node_owner
        else:
            continue
        if action_owner not in action_owners or output_owner not in output_owners:
            forbidden.add((node_owner, id(root)))
    huge: set[tuple[int, int]] = set()
    unknown: set[tuple[int, int]] = set()
    approved_keys: set[object] = set()
    approved_metadata: set[int] = set()
    definition_source: Iterator[tuple[int, object]] | None = iter(
        ledger.iter_payloads()
    )
    definitions: list[tuple[int, object]] = []
    definition_seen: set[int] = set()
    state_bound, pair_bound, radix_bound = 6, 1, 2
    response_records: dict[int, int] = {}
    actual_containers = dict(ledger.iter_containers())
    source_bound = audit_source_bound_payloads(
        ledger, execution_roots, actual_containers
    )
    forbidden.update(source_bound.invalid)
    reverse_source = audit_reverse_source_payloads(
        ledger, execution_roots, actual_containers
    )
    forbidden.update(reverse_source.invalid)
    associated = audit_associated_action_payloads(
        ledger, execution_roots, actual_containers
    )
    forbidden.update(associated.invalid)
    behaviors = BehaviorPayloadValidator(ledger)
    valid_behavior_records: set[int] = set()
    for root in execution_roots:
        if type(root) is not CompletedResultArena or root.ledger is not ledger:
            continue
        for behavior_key, behavior_value in root._memo.items():
            if type(behavior_key) is not BehaviorBindingKey:
                continue
            try:
                if type(behavior_value) is not CompletedBehaviorClassification:
                    raise TypeError("behavior binding contains another result sort")
                validate_published_behavior(root, behavior_key, behavior_value)
            except (TypeError, ValueError, AttributeError):
                forbidden.update(
                    (
                        (root._memo_owner, id(behavior_key)),
                        (root._memo_owner, id(behavior_value)),
                    )
                )
            else:
                valid_behavior_records.update((id(behavior_key), id(behavior_value)))
    for root in execution_roots:
        if type(root) is not TileScheduler or root.ledger is not ledger:
            continue
        if root._source_only:
            continue
        approved, invalid = audit_tile_dependency_leases(
            root._causal_dependencies,
            actual_containers,
        )
        approved_metadata.update(approved)
        forbidden.update(invalid)
    source_tiles: dict[ArenaToken, set[int]] = {}
    finite_audit = audit_finite_ports(
        ledger, ledger.iter_execution_roots(), actual_containers, forbidden
    )
    finite_arenas = finite_audit.arenas
    finite_index_owners = finite_audit.index_owners
    finite_choice_records = finite_audit.choices
    finite_substitution_records = finite_audit.substitutions
    finite_support_records = finite_audit.support_tuples
    microblock_roots: dict[int, MicroblockCache] = {}
    primitive_table_roots: dict[int, tuple[HigherPrimitiveTables, str]] = {}
    for root in ledger.iter_execution_roots():
        if (
            type(root) is MicroblockCache
            and root.ledger is ledger
            and roles.get(root.owner) == "exact_microblock"
            and actual_containers.get(root.owner) is root.blocks
        ):
            microblock_roots[root.owner] = root
        if type(root) is HigherPrimitiveTables and root.ledger is ledger:
            if actual_containers.get(root._interface_owner) is root._interfaces:
                primitive_table_roots[root._interface_owner] = (root, "interface")
            if actual_containers.get(root._step_owner) is root._steps:
                primitive_table_roots[root._step_owner] = (root, "step")
            if actual_containers.get(root._emit_owner) is root._outputs:
                primitive_table_roots[root._emit_owner] = (root, "emit")
        if (
            type(root) is SourceGeometry
            and root.ledger is ledger
            and actual_containers.get(root.owner) is root.nodes
        ):
            source_tiles[root.token] = {node.node_id for node in root.nodes.values()}
        elif type(root) is RadixProjection:
            radix_bound = max(radix_bound, root.radix)
        elif type(root) is PointResponseRegister:
            if (
                root.ledger is not ledger
                or root.compiler.ledger is not ledger
                or roles.get(root.owner) != "observation_memo"
                or actual_containers.get(root.owner) is not root._value
                or len(root._value) > 1
            ):
                forbidden.add((root.owner, id(root._value)))
                continue
            for response in root._value:
                if type(response) is not PointResponse:
                    continue
                try:
                    effect = root.compiler.resolve(response.program)
                except (TypeError, ValueError):
                    continue
                if (
                    type(response.position) is int
                    and response.position >= 0
                    and type(response.value) is int
                    and 0 <= response.value <= effect.blank
                ):
                    response_records[id(response)] = root.owner
    while definitions or definition_source is not None:
        if definitions:
            definition_owner, definition = definitions.pop()
        else:
            assert definition_source is not None
            try:
                definition_owner, definition = next(definition_source)
            except StopIteration:
                definition_source = None
                continue
        if id(definition) in definition_seen:
            continue
        definition_seen.add(id(definition))
        proof_c4 = False
        if physical_four(definition):
            try:
                definition.validate()
            except (TypeError, ValueError):
                continue
            proof_c4 = True
        if (
            type(definition) in literal_types
            or type(definition) is ProgramComposition
            or proof_c4
        ):
            effect = cast(BlockEffect, definition)
            radix_bound = max(radix_bound, effect.base)
            if type(definition) is BaseBlockEffect:
                pair_bound = max(pair_bound, definition.blank)
            if type(definition) is FiniteBlockEffect:
                state_bound = max(
                    state_bound, definition.left_count, definition.right_count
                )
            elif type(definition) is SymbolicBinaryDivisionEffect:
                state_bound = max(state_bound, 2 * definition.radix)
            else:
                state_bound = max(state_bound, effect.blank)
            key = _effect_key(effect)
            metadata_nodes: list[object] = [key]
            candidate_metadata: set[int] = set()
            try:
                while metadata_nodes:
                    part = metadata_nodes.pop()
                    if (
                        type(part) not in (tuple, SemanticIdentity)
                        or id(part) in approved_metadata
                        or id(part) in candidate_metadata
                    ):
                        continue
                    candidate_metadata.add(id(part))
                    if type(part) is tuple:
                        metadata_nodes.extend(part)
                    elif type(part) is SemanticIdentity:
                        behaviors.validate_identity(part)
                        metadata_nodes.append(part.behavior)
            except (TypeError, ValueError, AttributeError):
                forbidden.add((definition_owner, id(definition)))
                continue
            approved_keys.add(key)
            approved_metadata.update(candidate_metadata)
            if type(definition) is ProgramComposition:
                definitions.extend(
                    (
                        (definition_owner, definition.first),
                        (definition_owner, definition.second),
                    )
                )
        elif type(definition) is PrimitiveKernel:
            definitions.append((definition_owner, definition.effect))
        elif isinstance(definition, Mapping):
            definitions.extend((definition_owner, item) for item in definition.values())
        elif isinstance(definition, Sequence) and not isinstance(
            definition, (str, bytes)
        ):
            definitions.extend((definition_owner, item) for item in definition)

    def approved_key(value: object) -> bool:
        if id(value) in approved_metadata:
            return True
        if type(value) is tuple:
            try:
                return value in approved_keys
            except TypeError:
                return False
        return False

    semantic = SemanticPayloadRegistry(
        ledger, approved_key, diamond._handle, diamond.valid
    )
    forbidden.update(semantic.auxiliary.invalid_bindings)
    forbidden.update(semantic.primitive_macros.invalid_bindings)
    retained_snapshot = ledger.snapshot() if snapshot is None else snapshot
    identity_bound = retained_snapshot.nodes + retained_snapshot.entries + 2
    semantic_hints: dict[type[object], dict[str, object]] = {}
    record_opaque = (
        *literal_types,
        ProgramComposition,
        ExactSource,
        ExactEndpoint,
        CarryFn,
        *proof_opaque_types(),
    )
    state_records = (_BaseLeftState, _BaseRightState, _DigitLeftState)
    radix_fields = frozenset(
        (
            "radix",
            "width",
            "ledger",
            "_microblocks",
            "_fused",
            "_fused_actions",
            "_bound_source",
            "_bound_steps",
            "_native_source",
        )
    )
    checked_components: dict[int, tuple[object, bool]] = {}

    def semantic_component(value: object) -> bool:
        checked = checked_components.get(id(value))
        if checked is not None and checked[0] is value:
            return checked[1]
        valid = semantic_component_uncached(value)
        checked_components[id(value)] = value, valid
        return valid

    def semantic_component_uncached(value: object) -> bool:
        if source_bound.recognizes(value):
            return source_bound.valid(value)
        if reverse_source.recognizes(value):
            return reverse_source.valid(value)
        if associated.recognizes(value):
            return associated.valid(value)
        if type(value) in (BehaviorBindingKey, CompletedBehaviorClassification):
            return id(value) in valid_behavior_records
        if behaviors.recognizes(value):
            return behaviors.valid(value)
        if type(value) is _ChoiceIndexKey:
            return id(value) in finite_choice_records
        if type(value) is _SubstitutionIndexKey:
            return id(value) in finite_substitution_records
        if type(value) is _PortIndexComponent:
            return any(
                id(value) == id(component)
                for arena in finite_arenas.values()
                for key in arena._substitution.memo
                for component in key.components
            )
        if type(value) is tuple and id(value) in finite_support_records:
            return True
        if id(value) in higher_payloads.approved:
            return True
        if id(value) in support_payloads.approved:
            return True
        if id(value) in field_actions.approved:
            return True
        if id(value) in field_images.approved:
            return True
        if id(value) in radix_providers.approved:
            return True
        if id(value) in reverse_source.approved:
            return True
        if id(value) in semantic.auxiliary.projection_maps:
            return True  # Actual radix parameter -> owned execution context, not digit storage.
        if semantic.recognizes(value):
            return semantic.valid(value)
        if type(value) is SubstitutionKey:
            if (
                type(value.function) is not TransferSummaryID
                or type(value.components) is not tuple
            ):
                return False
            arena = finite_arenas.get(value.function.owner)
            if arena is None:
                return False
            try:
                arena._resolve(value.function)
                previous: PortVariable | None = None
                for component in value.components:
                    if (
                        type(component) is not PortComponent
                        or type(component.variable) is not PortVariable
                    ):
                        return False
                    variable = component.variable
                    if (
                        any(
                            type(part) is not int or part < 0
                            for part in (variable.time, variable.side, variable.bit)
                        )
                        or type(variable.role) is not str
                        or not variable.role
                    ):
                        return False
                    if previous is not None and variable <= previous:
                        return False
                    if type(component.function) is not TransferSummaryID:
                        return False
                    arena._resolve(component.function)
                    previous = component.variable
            except (TypeError, ValueError, AttributeError):
                return False
            return True
        if physical_four(value):
            try:
                value.validate()
            except (TypeError, ValueError):
                return False
            return True
        if diamond.recognizes(value):
            return diamond.valid(value)
        if diamond.domain(value):
            return True
        if type(value) is PointResponse:
            return id(value) in response_records
        if approved_key(value):
            return True
        if type(value) in geometry_fields:
            valid_record = valid_semantic_record(
                value,
                geometry=geometry_fields,
                opaque=record_opaque,
                states=state_records,
                identity_bound=identity_bound,
                state_bound=state_bound,
                pair_bound=pair_bound,
                radix_bound=radix_bound,
                source_handle_valid=lambda handle: (
                    type(handle.local_id) is int
                    and handle.local_id in source_tiles.get(handle.owner, set())
                ),
                resolved_hints=semantic_hints,
            )
            return valid_record
        if type(value) is RadixProjection:
            return set(vars(value)) == radix_fields
        return type(value) in record_opaque or value is ledger

    head_scopes = {
        root.expression_heads.owner: root
        for root in ledger.iter_execution_roots()
        if type(root) is DiamondRuntime
    }
    forbidden.update(diamond.expressions.invalid_response_objects)
    forbidden.update(diamond.higher.invalid_response_objects)
    forbidden.update(diamond.continuations.invalid_response_objects)
    forbidden.update(diamond.interfaces.invalid_response_objects)
    for owner, container in ledger.iter_containers():
        role = roles[owner]
        if role == "higher_primitive_kernel_table":
            table = primitive_table_roots.get(owner)
            if table is None or not valid_higher_primitive_table(*table, container):
                forbidden.add((owner, id(container)))
            continue
        if role == "exact_microblock":
            cache = microblock_roots.get(owner)
            if (
                cache is None
                or container is not cache.blocks
                or not isinstance(container, Mapping)
                or len(container) > cache.MAX_ENTRIES
            ):
                forbidden.add((owner, id(container)))
            else:
                payload_bytes = 0
                for key, value in audit_mapping_items(container):
                    if (
                        type(key) is not MicroblockKey
                        or type(value) is not ExactMicroblock
                    ):
                        forbidden.update(((owner, id(key)), (owner, id(value))))
                        continue
                    try:
                        key.__post_init__()
                        value.__post_init__()
                    except (TypeError, ValueError):
                        forbidden.update(((owner, id(key)), (owner, id(value))))
                        continue
                    payload_bytes += value.payload_bytes
                if (
                    payload_bytes > cache.MAX_PAYLOAD_BYTES
                    or payload_bytes != cache.payload_bytes
                ):
                    forbidden.add((owner, id(container)))
        scope = head_scopes.get(owner)
        if scope is not None and isinstance(container, Mapping):
            for request, result in audit_mapping_items(container):
                first = (
                    diamond.expressions.expression(request.expression)
                    if type(request) is ResolveExpr
                    else None
                )
                second = (
                    diamond.expressions.expression(result)
                    if type(result) is ExprID
                    else None
                )
                if (
                    type(request) is not ResolveExpr
                    or type(result) is not ExprID
                    or not diamond.valid(request)
                    or first is None
                    or second is None
                    or first.sort != second.sort
                    or not first.free_ports
                    or not second.free_ports
                    or not diamond.expressions.universal_program(request.expression)
                    or not diamond.expressions.universal_program(result)
                    or request.expression.owner is not scope.higher.expressions.token
                    or result.owner is not scope.higher.expressions.token
                ):
                    forbidden.update(((owner, id(request)), (owner, id(result))))
        if roles[owner] in ("exact_source", "exact_endpoint"):
            forbidden.update(
                (owner, identity) for identity in _proof_objects(container)
            )
        if (
            id(container) not in field_images.approved
            and id(container) not in radix_providers.approved
            and id(container) not in support_payloads.approved
            and id(container) not in reverse_source.approved
            and owner not in finite_index_owners
            and owner not in cache_event_owners
            and roles[owner]
            not in (
                "exact_source",
                "exact_endpoint",
                "explicit_lowering",
                "lowering",
                "exact_microblock",
                "radix_image_binding",
                "image_input_reference",
                "image_input_reference_interner",
                "image_input_reference_binding",
                "future_behavior_admission",
                "future_behavior_publication_snapshot",
            )
        ):
            aggregate = numeric_aggregate_audit(container, semantic=semantic_component)
            forbidden.update(
                (owner, identity) for identity in aggregate.forbidden_objects
            )
    payload_source: Iterator[tuple[int, object]] | None = iter(ledger.iter_payloads())
    stack: list[tuple[int, object, str]] = []
    while stack or payload_source is not None:
        if stack:
            owner, value, field_name = stack.pop()
        else:
            assert payload_source is not None
            try:
                owner, value = next(payload_source)
            except StopIteration:
                payload_source = None
                continue
            field_name = ""
        identity = (owner, id(value))
        role = roles[owner]
        if physical_four(value):
            if not semantic_component(value):
                forbidden.add(identity)
            continue
        if any(
            id(value) in audit.approved
            for audit in (
                field_actions,
                field_images,
                radix_providers,
                higher_payloads,
                support_payloads,
                reverse_source,
            )
        ):
            continue
        recognizing = next(
            (
                audit
                for audit in (source_bound, reverse_source, associated, behaviors)
                if audit.recognizes(value)
            ),
            None,
        )
        if recognizing is not None:
            if not recognizing.valid(value):
                forbidden.add(identity)
            continue
        if type(value) in (BehaviorBindingKey, CompletedBehaviorClassification):
            if not semantic_component(value):
                forbidden.add(identity)
            continue
        if type(value) is LocalInterfaceID:
            quotient_scope = quotient_scopes.get(value.owner)
            try:
                valid_local_interface = (
                    quotient_scope is not None
                    and quotient_scope.resolve(value) is not None
                )
            except (TypeError, ValueError, IndexError, AttributeError):
                valid_local_interface = False
            if not valid_local_interface:
                forbidden.add(identity)
            continue
        if type(value) is PointResponse and response_records.get(id(value)) != owner:
            forbidden.add(identity)
            continue
        if semantic.recognizes(value):
            if not semantic.valid(value):
                forbidden.add(identity)
            continue
        if diamond.recognizes(value):
            if not diamond.valid(value):
                forbidden.add(identity)
            continue
        if role in ("exact_source", "exact_endpoint", "explicit_lowering", "lowering"):
            continue
        if type(value).__module__.startswith("devtools.verification."):
            if type(value) in geometry_fields and semantic_component(value):
                continue
            if type(value) in record_opaque:
                continue
            forbidden.add(identity)
            continue
        if field_name in _HISTORY_FIELDS:
            forbidden.add(identity)
        if (
            role
            in (
                "transfer_summary",
                "carry_range_transfer",
                "canonical_transfer",
                "spatial_binding",
                "temporal_action",
                "image_action",
                "diamond_cell",
                "context_program",
                "macro_transfer_program",
                "boundary_expression_program",
            )
            and not field_name
            and isinstance(value, (int, WordLimb, CarryBit))
            and owner not in concrete_private_index_owners
        ):
            forbidden.add(identity)
        if approved_key(value):
            continue
        if value is None or isinstance(value, (str, bool)):
            continue
        if isinstance(value, int):
            if value.bit_length() > 64 and not field_name.startswith("geometry:"):
                huge.add(identity)
            continue
        if identity in seen:
            continue
        seen.add(identity)
        if type(value) in geometry_fields and not semantic_component(value):
            forbidden.add(identity)
        if type(value) is MicroblockCache:
            actual = actual_containers.get(value.owner)
            actual_bytes = sum(item.payload_bytes for item in value.blocks.values())
            if (
                value.ledger is not ledger
                or roles.get(value.owner) != "exact_microblock"
                or actual is not value.blocks
                or len(value.blocks) > value.MAX_ENTRIES
                or actual_bytes > value.MAX_PAYLOAD_BYTES
                or actual_bytes != value.payload_bytes
            ):
                forbidden.add(identity)
            continue
        if isinstance(value, ExactSource):
            if role != "exact_source":
                forbidden.add(identity)
            continue
        if isinstance(value, ExactEndpoint):
            if role not in ("exact_endpoint", "explicit_lowering", "lowering"):
                forbidden.add(identity)
            continue
        if type(value) is ExactMicroblock:
            if role != "exact_microblock":
                forbidden.add(identity)
                continue
            try:
                value.__post_init__()
            except (TypeError, ValueError):
                forbidden.add(identity)
            continue
        if isinstance(
            value,
            (
                ArenaHandle,
                ArenaToken,
                FrameTransform,
                LoweringCapability,
                WordLimb,
                CarryBit,
                CarryFn,
            ),
        ):
            continue
        if type(value) is RadixProjection:
            metadata = frozenset(("width",))
            for name, child in vars(value).items():
                if (
                    name == "_bound_source"
                    and id(value) in semantic.auxiliary.projection_sources
                ):
                    continue  # Same original source is independently audited under its exact-source owner.
                if name == "_fused" and child in semantic.auxiliary.fused:
                    continue  # Its actual registered stores are audited separately.
                if name == "_native_source" and child in semantic.auxiliary.originals:
                    continue
                if name == "ledger" and child is ledger:
                    continue
                if name == "_fused_actions" and isinstance(child, OwnedMemo):
                    stack.extend((owner, item, "") for item in child.items())
                    continue
                stack.append(
                    (owner, child, "geometry:" + name if name in metadata else name)
                )
            continue
        if type(value) is ProgramComposition:
            metadata = frozenset(
                (
                    "exponent",
                    "base",
                    "blank",
                    "node_id",
                    "blank_left_tail",
                    "blank_right_tail",
                    "depth",
                )
            )
            members = (
                vars(value).items()
                if hasattr(value, "__dict__")
                else (
                    (name, getattr(value, name))
                    for name in getattr(type(value), "__slots__", ())
                    if name != "__weakref__"
                )
            )
            stack.extend(
                (owner, child, "geometry:" + name if name in metadata else name)
                for name, child in members
            )
            continue
        if type(value) in literal_types:
            for slot in getattr(type(value), "__slots__", ()):
                child = getattr(value, slot)
                if isinstance(value, FiniteBlockEffect) and slot in (
                    "left_transitions",
                    "right_transitions",
                    "outputs",
                ):
                    continue
                if slot in ("_left_cache", "_right_cache", "_out_cache") and child:
                    unknown.add((owner, id(child)))
                stack.append((owner, child, slot))
            continue
        if isinstance(value, (DyadicSpan, DyadicTile, bytes, bytearray)):
            if role not in (
                "exact_source",
                "exact_endpoint",
                "explicit_lowering",
                "lowering",
            ):
                forbidden.add(identity)
            continue
        if field_name in _DIGIT_FIELDS:
            forbidden.add(identity)
        if isinstance(value, Mapping):
            for key, item in audit_mapping_items(value):
                stack.append((owner, key, ""))
                stack.append(
                    (
                        owner,
                        item,
                        field_name,
                    )
                )
        elif isinstance(value, (Sequence, set, frozenset)):
            stack.extend((owner, item, field_name) for item in value)
        elif is_dataclass(value) and not isinstance(value, type):
            node_metadata = geometry_fields.get(type(value))
            recognized = node_metadata is not None
            if node_metadata is None:
                unknown.add(identity)
                node_metadata = frozenset()
            stack.extend(
                (
                    owner,
                    getattr(value, item.name),
                    "geometry:" + item.name
                    if item.name in node_metadata
                    else item.name
                    if recognized or item.name in _DIGIT_FIELDS | _HISTORY_FIELDS
                    else "",
                )
                for item in fields(value)
            )
        else:
            unknown.add(identity)
    behaviors.finish()
    result = PayloadAudit(len(forbidden), len(huge), len(unknown))
    if not fresh or not execution_roots:
        ledger.cache_payload_audit(audit_version, result, root_signature)
    return result
