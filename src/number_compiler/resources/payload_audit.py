"""Payload audit with one canonical implementation owner."""

from __future__ import annotations

from collections.abc import Iterator, Sequence
from dataclasses import fields, is_dataclass
from functools import partial
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.block_effect import BlockEffect, _effect_key
from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
    object_mapping,
)
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
from number_compiler.arithmetic.fields.dyadic_tile import DyadicSpan, DyadicTile
from number_compiler.resources.approved_effect_keys import (
    approved_effect_key_checker,
)
from number_compiler.resources.cache_gc_metrics import cache_event_owner_audit
from number_compiler.resources.callback_payload_audit import (
    audit_callback_future_payloads,
)
from number_compiler.resources.ledger import LedgerSnapshot, OwnedMemo, ResourceLedger
from number_compiler.resources.numeric_payload import numeric_aggregate_audit
from number_compiler.resources.payload_containers import audit_mapping_items
from number_compiler.resources.payload_contracts import (
    SemanticComponentAuditMemo,
    contract_semantic_component,
)
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
        AGGREGATE_EXEMPT_PAYLOAD_ROLES,
        DIGIT_FIELDS,
        HISTORY_FIELDS,
        PayloadAudit,
        normalize_payload_role,
    )

    execution_roots = tuple(ledger.iter_execution_roots())
    root_signature = ledger.audit_root_signature()
    if not fresh:
        cached = ledger.cached_payload_audit(root_signature)
        if type(cached) is PayloadAudit:
            return cached
    contract_audit = ledger.audit_payload_contracts()
    audit_version = ledger.mutation_version
    from number_compiler.arithmetic.contracts.block_kernel import (
        BaseBlockEffect,
        BaseLeftState,
        BaseRightState,
        FiniteBlockEffect,
    )
    from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
    from number_compiler.arithmetic.functions.finite_port_action import (
        ChoiceIndexKey,
        PortComponent,
        PortVariable,
    )
    from number_compiler.arithmetic.functions.finite_port_substitution import (
        PortIndexComponent,
        SubstitutionIndexKey,
        SubstitutionKey,
    )
    from number_compiler.arithmetic.radix_division import SymbolicBinaryDivisionEffect
    from number_compiler.hashlife.actions.lazy_compiler import ProgramComposition
    from number_compiler.hashlife.execution.continuations.concrete_port_records import (
        VirtualInterface,
    )
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
    )
    from number_compiler.hashlife.interfaces.semantic_structures import LocalInterfaceID
    from number_compiler.hashlife.observation.diamond_observers import (
        NonblankBlockEffect,
    )
    from number_compiler.hashlife.tiles.tile_behavior_memo import (
        validate_published_behavior,
    )
    from number_compiler.hashlife.tiles.tile_result_records import (
        BehaviorBindingKey,
        CompletedBehaviorClassification,
    )
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
    from number_compiler.projection.digit_terminal import (
        DigitLeftState,
        DigitNormalizeBlockEffect,
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
    from number_compiler.resources.family_effect_payload import FamilyEffectPayloadAudit
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
    from number_compiler.resources.payload_effect_metadata import (
        audit_effect_key_metadata,
    )
    from number_compiler.resources.radix_provider_payload_audit import (
        audit_radix_provider_payloads,
    )
    from number_compiler.resources.semantic_payload import SemanticPayloadRegistry
    from number_compiler.resources.slp_payload_audit import audit_ledger_slp_payloads
    from number_compiler.resources.source_bound_payload_audit import (
        audit_source_bound_payloads,
    )
    from number_compiler.resources.support_payload_audit import (
        audit_support_payloads,
    )
    from number_compiler.resources.tile_dependency_leases import (
        audit_tile_dependency_leases,
    )

    family_effects = FamilyEffectPayloadAudit(execution_roots)
    diamond = DiamondPayloadRegistry(ledger)
    from number_compiler.resources.payload_geometry import geometry_field_policy

    geometry_fields = geometry_field_policy()
    geometry_fields.update(proof_geometry_fields())
    literal_types = (
        BaseBlockEffect,
        FiniteBlockEffect,
        DigitNormalizeBlockEffect,
        NonblankBlockEffect,
        SymbolicBinaryDivisionEffect,
        *sorted(
            family_effects.effect_types,
            key=lambda effect_type: (effect_type.__module__, effect_type.__qualname__),
        ),
    )
    roles = {
        item.owner: normalize_payload_role(item.role) for item in ledger.inventory()
    }
    seen: set[tuple[int, int]] = set()
    forbidden: set[tuple[int, int]] = set()
    forbidden.update(contract_audit.invalid)
    cache_event_owners, cache_event_invalid = cache_event_owner_audit(
        execution_roots,
        ledger,
    )
    forbidden.update(cache_event_invalid)
    field_actions = audit_field_action_payloads(ledger, contract_audit)
    field_images = audit_field_image_payloads(ledger, contract_audit)
    radix_providers = audit_radix_provider_payloads(ledger)
    higher_payloads = audit_higher_payloads(ledger, contract_audit)
    from number_compiler.resources.payload_owner_scopes import field_owner_scopes

    support_payloads = audit_support_payloads(ledger, contract_audit)
    forbidden.update(field_actions.invalid)
    forbidden.update(field_images.invalid)
    forbidden.update(radix_providers.invalid)
    forbidden.update(higher_payloads.invalid)
    forbidden.update(support_payloads.invalid)
    approved_payload_members = (
        higher_payloads.approved
        | support_payloads.approved
        | field_actions.approved
        | field_images.approved
        | radix_providers.approved
    )
    approved_container_members = (
        field_images.approved | radix_providers.approved | support_payloads.approved
    )
    forbidden.update(audit_registered_proof_payloads(ledger))
    forbidden.update(audit_callback_future_payloads(ledger))
    concrete_private_index_owners = {
        owner
        for root in execution_roots
        if type(root) is ConcretePortScheduler and root.ledger is ledger
        for owner in (
            ConcretePortScheduler.audit_snapshot(root).virtual_owner,
            ConcretePortScheduler.audit_snapshot(root).virtual_key_owner,
        )
    }
    quotient_scopes = {
        root.owner: root
        for root in execution_roots
        if type(root) is DiamondQuotientArena and root.ledger is ledger
    }
    action_owners, output_owners = field_owner_scopes(
        execution_roots, contract_audit, ledger
    )
    for root in execution_roots:
        if type(root) is RecursiveFieldImageArena:
            image_carrier = root
            action_owner = image_carrier.action_owner
            output_owner = image_carrier.output_owner
            node_owner = RecursiveFieldImageArena.audit_snapshot(
                image_carrier
            ).node_owner
        elif type(root) is FieldTransferArena:
            transfer_carrier = root
            action_owner = transfer_carrier.action_owner
            output_owner = transfer_carrier.output_owner
            node_owner = FieldTransferArena.audit_snapshot(transfer_carrier).node_owner
        else:
            continue
        if action_owner not in action_owners or output_owner not in output_owners:
            forbidden.add((node_owner, id(root)))
    huge: set[tuple[int, int]] = set()
    unknown: set[tuple[int, int]] = set()
    approved_key_fingerprints: set[tuple[tuple[object, ...], ...]] = set()
    approved_key_identity_ids: set[int] = set()
    approved_key_roots: list[object] = []
    approved_metadata: set[int] = set()
    definition_source: Iterator[tuple[int, object]] | None = iter(
        ledger.iter_payloads()
    )
    definitions: list[tuple[int, object]] = []
    definition_seen: set[int] = set()
    state_bound, pair_bound, radix_bound = 6, 1, 2
    response_records: dict[int, int] = {}
    actual_containers = dict(ledger.iter_containers())
    slp_payloads = audit_ledger_slp_payloads(ledger, execution_roots, actual_containers)
    forbidden.update(slp_payloads.invalid)
    source_bound = audit_source_bound_payloads(
        ledger, execution_roots, actual_containers
    )
    forbidden.update(source_bound.invalid)
    associated = audit_associated_action_payloads(
        ledger, execution_roots, actual_containers
    )
    forbidden.update(associated.invalid)
    behaviors = BehaviorPayloadValidator(ledger)
    valid_behavior_records: set[int] = set()
    for root in execution_roots:
        if type(root) is not CompletedResultArena or root.ledger is not ledger:
            continue
        result_snapshot = CompletedResultArena.audit_snapshot(root)
        for behavior_key, behavior_value in result_snapshot.memo.items():
            if type(behavior_key) is not BehaviorBindingKey:
                continue
            try:
                if type(behavior_value) is not CompletedBehaviorClassification:
                    raise TypeError("behavior binding contains another result sort")
                validate_published_behavior(root, behavior_key, behavior_value)
            except (TypeError, ValueError, AttributeError):
                forbidden.update(
                    (
                        (result_snapshot.memo_owner, id(behavior_key)),
                        (result_snapshot.memo_owner, id(behavior_value)),
                    )
                )
            else:
                valid_behavior_records.update((id(behavior_key), id(behavior_value)))
    for root in execution_roots:
        if type(root) is not TileScheduler or root.ledger is not ledger:
            continue
        if root.is_source_only:
            continue
        approved, invalid = audit_tile_dependency_leases(
            root.dependency_leases,
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
    finite_substitution_components = finite_audit.substitution_components
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
            primitive_snapshot = HigherPrimitiveTables.audit_snapshot(root)
            if primitive_snapshot.ledger is ledger:
                for owner, store_identity, operation in (
                    (
                        primitive_snapshot.interface_owner,
                        primitive_snapshot.interface_store_identity,
                        "interface",
                    ),
                    (
                        primitive_snapshot.step_owner,
                        primitive_snapshot.step_store_identity,
                        "step",
                    ),
                    (
                        primitive_snapshot.emit_owner,
                        primitive_snapshot.emit_store_identity,
                        "emit",
                    ),
                ):
                    container = actual_containers.get(owner)
                    if container is not None and id(container) == store_identity:
                        primitive_table_roots[owner] = (root, operation)
        if (
            type(root) is SourceGeometry
            and root.ledger is ledger
            and actual_containers.get(root.owner) is root.nodes
        ):
            source_tiles[root.token] = {node.node_id for node in root.nodes.values()}
        elif type(root) is RadixProjection:
            radix_bound = max(radix_bound, root.radix)
        elif type(root) is PointResponseRegister:
            response_snapshot = PointResponseRegister.audit_snapshot(root)
            response_container = actual_containers.get(response_snapshot.owner)
            if (
                response_snapshot.ledger is not ledger
                or root.compiler.ledger is not ledger
                or roles.get(response_snapshot.owner) != "observation_memo"
                or response_container is None
                or id(response_container) != response_snapshot.store_identity
                or len(response_snapshot.responses) > 1
            ):
                forbidden.add(
                    (response_snapshot.owner, response_snapshot.store_identity)
                )
                continue
            for response in response_snapshot.responses:
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
                    response_records[id(response)] = response_snapshot.owner
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
        proof_c4 = family_effects.valid_compatibility(definition)
        if type(definition) in family_effects.compatibility_types and not proof_c4:
            continue
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
            approved_key_roots.append(key)
            if not audit_effect_key_metadata(
                key,
                definition_owner,
                definition,
                behaviors=behaviors,
                approved_metadata=approved_metadata,
                approved_key_identity_ids=approved_key_identity_ids,
                approved_key_fingerprints=approved_key_fingerprints,
                forbidden=forbidden,
            ):
                continue
            if type(definition) is ProgramComposition:
                definitions.extend(
                    (
                        (definition_owner, definition.first),
                        (definition_owner, definition.second),
                    )
                )
        elif type(definition) is PrimitiveKernel:
            definitions.append((definition_owner, definition.effect))
        elif (mapping := object_mapping(definition)) is not None:
            definitions.extend((definition_owner, item) for item in mapping.values())
        elif isinstance(definition, Sequence) and not isinstance(
            definition, (str, bytes)
        ):
            sequence = cast(Sequence[object], definition)
            definitions.extend((definition_owner, item) for item in sequence)

    approved_key = approved_effect_key_checker(
        approved_metadata, approved_key_identity_ids, approved_key_fingerprints
    )
    semantic = SemanticPayloadRegistry(
        ledger,
        approved_key,
        diamond.valid_handle,
        diamond.valid,
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
    state_records = (BaseLeftState, BaseRightState, DigitLeftState)
    radix_fields: frozenset[str] = frozenset(
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

    def semantic_component_uncached(value: object, *, owner: int | None = None) -> bool:
        if type(value) is VirtualInterface:
            return (
                owner is not None
                and (
                    owner,
                    id(value),
                )
                in field_images.virtual_interfaces
            )
        if owner is not None and slp_payloads.approves(owner, value):
            return True
        if type(value) in family_effects.compatibility_types:
            return family_effects.valid_compatibility(value)
        if source_bound.recognizes(value):
            return source_bound.valid(value)
        if associated.recognizes(value):
            return associated.valid(value)
        if type(value) in (BehaviorBindingKey, CompletedBehaviorClassification):
            return id(value) in valid_behavior_records
        if behaviors.recognizes(value):
            return behaviors.valid(value)
        if type(value) is ChoiceIndexKey:
            return id(value) in finite_choice_records
        if type(value) is SubstitutionIndexKey:
            return id(value) in finite_substitution_records
        if type(value) is PortIndexComponent:
            return id(value) in finite_substitution_components
        if is_exact_object_tuple(value) and id(value) in finite_support_records:
            return True
        if contract_audit.approves_member(approved_payload_members, value, owner):
            return True
        if id(value) in semantic.auxiliary.projection_maps:
            return True  # Actual radix parameter -> owned execution context, not digit storage.
        if semantic.recognizes(value):
            return semantic.valid(value)
        if type(value) is SubstitutionKey:
            if type(
                value.function
            ) is not TransferSummaryID or not is_exact_object_tuple(value.components):
                return False
            arena = finite_arenas.get(value.function.owner)
            if arena is None:
                return False
            try:
                arena.resolve_index(value.function)
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
                    arena.resolve_index(component.function)
                    previous = component.variable
            except (TypeError, ValueError, AttributeError):
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
            return frozenset(vars(value)) == radix_fields
        return type(value) in record_opaque or value is ledger

    semantic_component = SemanticComponentAuditMemo(semantic_component_uncached)

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
            container_mapping = object_mapping(container)
            if (
                cache is None
                or container is not cache.blocks
                or container_mapping is None
                or len(container_mapping) > cache.MAX_ENTRIES
            ):
                forbidden.add((owner, id(container)))
            else:
                payload_bytes = 0
                for key, value in audit_mapping_items(container_mapping):
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
        container_mapping = object_mapping(container)
        if scope is not None and container_mapping is not None:
            for request, result in audit_mapping_items(container_mapping):
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
            not contract_audit.approves_member(
                approved_container_members, container, owner
            )
            and not slp_payloads.approves(owner, container)
            and owner not in finite_index_owners
            and owner not in cache_event_owners
            and roles[owner] not in AGGREGATE_EXEMPT_PAYLOAD_ROLES
        ):
            aggregate = numeric_aggregate_audit(
                container,
                semantic=partial(
                    contract_semantic_component,
                    owner=owner,
                    approved=contract_audit.approved,
                    owned_semantic_members=source_bound.payload_members_by_owner,
                    semantic=semantic_component,
                ),
            )
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
        if identity in contract_audit.approved:
            continue
        if type(value) is VirtualInterface:
            if identity not in field_images.virtual_interfaces:
                forbidden.add(identity)
            continue
        if type(value) in family_effects.compatibility_types:
            if not family_effects.valid_compatibility(value):
                forbidden.add(identity)
            continue
        if contract_audit.approves_member(approved_payload_members, value, owner):
            continue
        if slp_payloads.approves(owner, value):
            continue
        if source_bound.owns_payload_member(owner, value):
            # This exact frozen value was approved as a direct member of a
            # sealed source-image payload. Stop traversal here so its occurrence
            # coordinates are not reclassified as an untyped numeric aggregate.
            continue
        recognizing = next(
            (
                audit
                for audit in (source_bound, associated, behaviors)
                if audit.recognizes(value)
            ),
            None,
        )
        if recognizing is not None:
            if not recognizing.valid(value):
                forbidden.add(identity)
            continue
        if type(value) in (BehaviorBindingKey, CompletedBehaviorClassification):
            if not semantic_component(value, owner=owner):
                forbidden.add(identity)
            continue
        if type(value) is LocalInterfaceID:
            quotient_scope = quotient_scopes.get(value.owner)
            try:
                valid_local_interface = quotient_scope is not None
                if quotient_scope is not None:
                    quotient_scope.resolve(value)
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
            if type(value) in geometry_fields and semantic_component(
                value, owner=owner
            ):
                continue
            if type(value) in record_opaque:
                continue
            forbidden.add(identity)
            continue
        if field_name in HISTORY_FIELDS:
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
        if type(value) in geometry_fields and not semantic_component(
            value, owner=owner
        ):
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
                    memo = cast(OwnedMemo[object, object], child)
                    stack.extend(
                        (owner, entry, "")
                        for entry in memo.audit_payload_view().items()
                    )
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
        if field_name in DIGIT_FIELDS:
            forbidden.add(identity)
        mapping = object_mapping(value)
        if mapping is not None:
            for key, item in audit_mapping_items(mapping):
                stack.append((owner, key, ""))
                stack.append(
                    (
                        owner,
                        item,
                        field_name,
                    )
                )
        elif isinstance(value, (Sequence, set, frozenset)):
            items = cast(Sequence[object] | set[object] | frozenset[object], value)
            stack.extend((owner, item, field_name) for item in items)
        elif is_dataclass(value) and not isinstance(value, type):
            node_metadata: frozenset[str] | None = geometry_fields.get(type(value))
            recognized = node_metadata is not None
            if node_metadata is None:
                unknown.add(identity)
                node_metadata = frozenset[str]()
            stack.extend(
                (
                    owner,
                    getattr(value, item.name),
                    "geometry:" + item.name
                    if item.name in node_metadata
                    else item.name
                    if recognized or item.name in DIGIT_FIELDS | HISTORY_FIELDS
                    else "",
                )
                for item in fields(value)
            )
        else:
            unknown.add(identity)
    behaviors.finish()
    result = PayloadAudit(len(forbidden), len(huge), len(unknown))
    # A fresh audit always walks nested records, even when a previous snapshot
    # matches the shallow root signature. Keep its result for ordinary metric
    # snapshots; their contract is the most recent deep audit plus tracked
    # ledger/root changes, while explicit audits always recheck nested fields.
    if ledger.audit_root_signature() == root_signature:
        ledger.cache_payload_audit(audit_version, result, root_signature)
    return result
