"""Read-only validators for one ledger-owned comma term's retained payloads."""

from __future__ import annotations

from collections.abc import Hashable, Mapping
from typing import TYPE_CHECKING, cast

from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageBinding,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import comma as _comma_keys
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
)

if TYPE_CHECKING:
    from number_compiler.sequences.comma.image_adapter import CommaImageAdapter
    from number_compiler.sequences.comma.power import CommaTerm


def audit_comma_term(ledger: object, root: object) -> PayloadAuditContribution:
    """Validate a term's action and occurrence stores without opening image records.

    Scheduler image seals and source/action provenance belong to the shared
    source-image auditor.  This owner checks the family-specific records and
    leaves per-image arithmetic binding to ``audit_image_binding``.
    """
    from number_compiler.hashlife.execution.source_image_inventory import SourceImageID
    from number_compiler.sequences.comma.action_arena import (
        CommaActionID,
        CommaActionRecord,
        action_snapshot,
    )
    from number_compiler.sequences.comma.boundary_quotient import (
        PERIOD,
        AffineWeight,
        BoundaryState,
        MacroTemplate,
        boundary_state_signature,
        macro_template_retained_components,
        validate_macro_component_header,
        validate_macro_component_read,
    )
    from number_compiler.sequences.comma.boundary_receipt import (
        SOURCE,
        BoundaryPrefixCursor,
        BoundarySelectionReceipt,
        BoundarySelectionReceiptID,
        CommaOccurrenceRecord,
    )
    from number_compiler.sequences.comma.power import CommaTerm

    if type(ledger) is not ResourceLedger or type(root) is not CommaTerm:
        raise TypeError("comma payload audit requires its exact term root")
    term = root
    term_snapshot = term.audit_snapshot()
    arena = term_snapshot.arena
    invalid: list[PayloadAuditEntry] = []

    def reject(owner: int, value: object) -> None:
        invalid.append(PayloadAuditEntry(owner, value))

    def charge_boundary_audit_component() -> None:
        ledger.bump(_comma_keys.COMMA_BOUNDARY_EXPLICIT_AUDIT_COMPONENT_CHECKS)

    def charge_boundary_audit_bits(bits: int) -> None:
        ledger.bump(_comma_keys.COMMA_BOUNDARY_EXPLICIT_AUDIT_OPERAND_BITS, bits)

    if (
        term.ledger is not ledger
        or term.adapter.ledger is not ledger
        or term.adapter.arena is not term.arena
        or term.adapter.bound_term is not term
        or term.scheduler.ledger is not ledger
        or term.scheduler.is_source_only is not True
        or not term_snapshot.stores_owned
    ):
        reject(arena.owner, term)
        return PayloadAuditContribution((), tuple(invalid))

    nodes = arena.nodes
    snapshots = arena.snapshots
    keys = arena.keys
    aliases = (
        (arena.owner, arena.nodes),
        (arena.key_owner, arena.keys),
        (arena.snapshot_owner, arena.snapshots),
        (arena.boundary_owner, arena.boundary_templates),
        (arena.boundary_seal_owner, arena.boundary_seals),
        (arena.boundary_seal_node_owner, arena.boundary_seal_nodes),
        (arena.boundary_node_owner, arena.boundary_nodes),
        (term_snapshot.occurrence_owner, term_snapshot.occurrences),
        (term_snapshot.occurrence_seal_owner, term_snapshot.occurrence_seals),
        (term_snapshot.boundary_receipt_owner, term_snapshot.boundary_receipts),
        (
            term_snapshot.boundary_receipt_seal_owner,
            term_snapshot.boundary_receipt_seals,
        ),
    )
    canonical: dict[int, CommaActionID] = {}
    action_valid = len(nodes) == len(snapshots)
    for action_key, identifier in keys.items():
        try:
            if type(action_key) is not tuple or type(identifier) is not CommaActionID:
                raise TypeError("comma action index has another record sort")
            identifier.validate(arena.token, arena.kind, size=len(nodes))
            local_id = identifier.local_id
            node = nodes[local_id]
            if local_id in canonical:
                raise ValueError("comma action has multiple canonical keys")
            if type(node) is not CommaActionRecord:
                raise TypeError("comma action has another node sort")
            if node.kind == "identity":
                expected_key: tuple[object, ...] = ("identity",)
                valid_node = node.steps == 0
            elif node.kind == "step":
                expected_key = ("step", node.child_digit)
                valid_node = node.steps == 1 and 1 <= node.child_digit <= 9
            elif node.kind == "cycle":
                from math import gcd

                expected_key = (
                    "cycle",
                    node.leading,
                    node.entering_digit % gcd(node.leading, 10),
                    node.cycles,
                )
                valid_node = (
                    1 <= node.leading <= 9
                    and 0 <= node.entering_digit <= 9
                    and node.cycles >= 1
                    and node.steps >= 1
                    and type(node.displacement) is int
                    and type(node.maximum_guard) is int
                )
            elif node.kind == "phase-prefix":
                expected_key = (
                    "phase-prefix",
                    node.leading,
                    node.entering_digit,
                    node.steps,
                )
                valid_node = (
                    type(node.steps) is int
                    and 0 < node.steps < 10
                    and 1 <= node.leading <= 9
                    and 0 <= node.entering_digit <= 9
                )
            elif node.kind == "sequence":
                expected_key = ("sequence", node.before, node.after)
                valid_node = node.before is not None and node.after is not None
            elif node.kind == "boundary-prefix-occurrence":
                state = node.boundary_source
                if type(state) is not BoundaryState:
                    raise ValueError("receiver-bound action has another source sort")
                boundary_state_signature(state)
                valid_node = (
                    type(node.steps) is int
                    and node.steps >= 0
                    and node.future_digest == ""
                )
                expected_key = ("boundary-prefix-occurrence", state, node.steps)
            elif node.kind == "global-boundary-return":
                from number_compiler.sequences.comma.future_authority import (
                    valid_artifact_digest,
                )

                state = node.boundary_source
                if type(state) is not BoundaryState or node.boundary_target is not None:
                    raise ValueError("global return has another boundary state sort")
                boundary_state_signature(state)
                valid_node = node.steps == 0 and valid_artifact_digest(
                    node.future_digest
                )
                expected_key = (
                    "global-boundary-return",
                    state,
                    node.future_digest,
                )
            elif node.kind == "source20-first-child":
                from number_compiler.sequences.comma.future_authority import (
                    valid_artifact_digest,
                )

                valid_node = (
                    node.steps == 1
                    and node.boundary_source is None
                    and node.boundary_target is None
                    and valid_artifact_digest(node.future_digest)
                )
                expected_key = ("source20-first-child", node.future_digest)
            else:
                raise ValueError("comma action has an unknown semantic kind")
            if not valid_node or action_key != expected_key:
                raise ValueError("comma action key and node disagree")
            canonical[local_id] = identifier
        except (AttributeError, IndexError, TypeError, ValueError):
            action_valid = False
            reject(arena.key_owner, action_key)
            reject(arena.key_owner, identifier)

    for local_id, node in enumerate(nodes):
        try:
            if (
                type(node) is not CommaActionRecord
                or local_id not in canonical
                or action_snapshot(node) != snapshots[local_id]
            ):
                raise ValueError("comma action differs from its publication seal")
            if node.kind == "sequence":
                before, after = node.before, node.after
                if (
                    before is None
                    or after is None
                    or before.local_id >= local_id
                    or after.local_id >= local_id
                    or before is not canonical.get(before.local_id)
                    or after is not canonical.get(after.local_id)
                    or node.steps
                    != nodes[before.local_id].steps + nodes[after.local_id].steps
                ):
                    raise ValueError(
                        "comma composition has invalid chronological children"
                    )
            elif node.kind == "boundary-prefix-occurrence":
                state = node.boundary_source
                if state is None or state not in arena.boundary_templates:
                    raise ValueError(
                        "comma receiver-bound action lost its admitted template"
                    )
            elif node.kind == "global-boundary-return":
                state = node.boundary_source
                template = (
                    None if state is None else arena.boundary_templates.get(state)
                )
                if (
                    state is None
                    or node.boundary_target is not None
                    or template is None
                    or template.outcome != "fork"
                ):
                    raise ValueError("comma global return lost its guarded source")
            elif node.kind == "source20-first-child":
                if node.future_digest == "":
                    raise ValueError("source-20 action lost global artifact binding")
        except (AttributeError, IndexError, TypeError, ValueError):
            action_valid = False
            reject(arena.owner, node)
            if local_id < len(snapshots):
                reject(arena.snapshot_owner, snapshots[local_id])
    if len(canonical) != len(nodes):
        action_valid = False
        reject(arena.owner, arena.nodes)

    boundary_valid = True
    expected_nodes: list[object] = []
    expected_seal_nodes: list[object] = []
    templates = arena.boundary_templates
    seals = arena.boundary_seals
    if len(seals) != len(templates):
        boundary_valid = False
        reject(arena.boundary_seal_owner, arena.boundary_seals)
    for template_state, template in templates.items():
        template_seal: object | None = None
        try:
            if (
                type(template_state) is not BoundaryState
                or type(template) is not MacroTemplate
                or template.source is not template_state
            ):
                raise ValueError("comma boundary template has another shape")
            boundary_state_signature(template_state)
            template_seal = seals[template_state]
            charge_boundary_audit_component()
            if type(template_seal) is not tuple or not template.owns_component_seal(
                template_seal
            ):
                raise ValueError("comma boundary template differs from its seal")
            validate_macro_component_header(
                template,
                template_seal,
                charge_bits=charge_boundary_audit_bits,
            )
            for kind, components in (
                ("fragment", template.sector_fragments),
                ("weight", template.prefix_weights),
                ("displacement", template.prefix_displacements),
                ("chart_segment", template.chart_segments),
            ):
                for index in range(len(components)):
                    charge_boundary_audit_component()
                    validate_macro_component_read(
                        template,
                        template_seal,
                        kind,
                        index,
                        charge_bits=charge_boundary_audit_bits,
                    )
            if (
                template.prefix_weights[0] != AffineWeight(0, 0, 1)
                or template.prefix_displacements[0] != AffineWeight(0, 0, 1)
                or template.prefix_weights[-1] != template.weight
            ):
                raise ValueError("comma boundary template has another prefix law")
            if template.outcome == "fork":
                if (
                    template.destination_a is None
                    or len(template.ordered_children) != 2
                    or template.ordered_children[0]
                    != BoundaryState(
                        "N",
                        template.destination_a,
                        (template_state.exponent_residue + template.exponent_delta)
                        % PERIOD,
                    )
                    or template.ordered_children[1]
                    != BoundaryState(
                        "Z",
                        template.destination_a,
                        (template_state.exponent_residue + template.exponent_delta)
                        % PERIOD,
                    )
                ):
                    raise ValueError("comma fork template has wrong ordered children")
            elif template.destination_a is not None or template.ordered_children:
                raise ValueError("comma landmine template has fabricated children")
            expected_nodes.extend(macro_template_retained_components(template))
            expected_seal_nodes.extend(cast(tuple[object, ...], template_seal[1]))
            expected_seal_nodes.extend(cast(tuple[object, ...], template_seal[2]))
            expected_seal_nodes.extend(cast(tuple[object, ...], template_seal[3]))
            expected_seal_nodes.extend(cast(tuple[object, ...], template_seal[4]))
        except (AttributeError, IndexError, KeyError, TypeError, ValueError):
            boundary_valid = False
            reject(arena.boundary_owner, template)
            if template_seal is not None:
                reject(arena.boundary_seal_owner, template_seal)
    if (
        len(expected_nodes) != len(arena.boundary_nodes)
        or any(
            actual is not expected
            for actual, expected in zip(
                arena.boundary_nodes, expected_nodes, strict=True
            )
        )
        or len(expected_seal_nodes) != len(arena.boundary_seal_nodes)
        or any(
            actual is not expected
            for actual, expected in zip(
                arena.boundary_seal_nodes, expected_seal_nodes, strict=True
            )
        )
    ):
        boundary_valid = False
        reject(arena.boundary_node_owner, arena.boundary_nodes)
        reject(arena.boundary_seal_node_owner, arena.boundary_seal_nodes)

    occurrence_valid = len(term_snapshot.occurrences) == len(
        term_snapshot.occurrence_seals
    )
    for occurrence, occurrence_seal in zip(
        term_snapshot.occurrences, term_snapshot.occurrence_seals, strict=False
    ):
        if (
            type(occurrence) is not CommaOccurrenceRecord
            or occurrence is not occurrence_seal
            or type(occurrence.image) is not SourceImageID
            or type(occurrence.value) is not int
            or occurrence.value < SOURCE
        ):
            occurrence_valid = False
            reject(term_snapshot.occurrence_owner, occurrence)
            reject(term_snapshot.occurrence_seal_owner, occurrence_seal)
        elif (
            type(occurrence.absolute_index) is not int
            or occurrence.absolute_index < 1
            or occurrence.certificate_version != term.certificate_version
            or (
                occurrence.boundary_cursor is not None
                and type(occurrence.boundary_cursor) is not BoundaryPrefixCursor
            )
        ):
            occurrence_valid = False
            reject(term_snapshot.occurrence_owner, occurrence)
        elif occurrence.boundary_cursor is not None:
            cursor = occurrence.boundary_cursor
            try:
                if (
                    type(cursor.state) is not BoundaryState
                    or type(cursor.exponent) is not int
                    or cursor.exponent < 5
                    or cursor.exponent % PERIOD != cursor.state.exponent_residue
                    or type(cursor.transitions) is not int
                    or cursor.transitions < 0
                    or occurrence.absolute_index - cursor.transitions < 1
                ):
                    raise ValueError("invalid occurrence cursor")
                boundary_state_signature(cursor.state)
                if cursor.selection_receipt is not None:
                    term.resolve_boundary_selection_receipt(cursor.selection_receipt)
            except (AttributeError, TypeError, ValueError):
                occurrence_valid = False
                reject(term_snapshot.occurrence_owner, occurrence)
    if not action_valid or not boundary_valid or not occurrence_valid:
        return PayloadAuditContribution((), tuple(invalid))

    receipt_valid = len(term_snapshot.boundary_receipts) == len(
        term_snapshot.boundary_receipt_seals
    )
    for receipt_id, receipt in term_snapshot.boundary_receipts.items():
        try:
            if (
                type(receipt_id) is not BoundarySelectionReceiptID
                or type(receipt) is not BoundarySelectionReceipt
                or term_snapshot.boundary_receipt_seals.get(receipt_id) is not receipt
            ):
                raise ValueError("comma receipt store lost its paired seal")
            receipt_id.validate(
                term_snapshot.boundary_receipt_token,
                term_snapshot.boundary_receipt_kind,
            )
            receipt.validate_shape()
        except (AttributeError, TypeError, ValueError):
            receipt_valid = False
            reject(term_snapshot.boundary_receipt_owner, receipt_id)
            reject(term_snapshot.boundary_receipt_owner, receipt)
    if not receipt_valid:
        for receipt_id, seal in term_snapshot.boundary_receipt_seals.items():
            if term_snapshot.boundary_receipts.get(receipt_id) is not seal:
                reject(term_snapshot.boundary_receipt_seal_owner, receipt_id)
                reject(term_snapshot.boundary_receipt_seal_owner, seal)

    approved: list[PayloadAuditEntry] = []
    for owner, store in aliases:
        if isinstance(store, Mapping):
            for map_key, value in store.items():
                approved.append(PayloadAuditEntry(owner, map_key))
                approved.append(PayloadAuditEntry(owner, value))
        else:
            approved.extend(PayloadAuditEntry(owner, item) for item in store)
    return PayloadAuditContribution(tuple(approved), tuple(invalid))


__all__ = ["audit_comma_term"]


def audit_comma_image_binding(
    adapter: CommaImageAdapter,
    binding: SourceImageBinding,
    payload: object,
    failure_prefix: Hashable | None,
) -> tuple[Hashable, ...] | None:
    """Validate one image's family binding without querying or charging it."""
    from number_compiler.hashlife.execution.source_bound_images import SourceImageRecord
    from number_compiler.hashlife.execution.source_image_inventory import SourceImageID
    from number_compiler.sequences.comma.action_arena import (
        CommaActionID,
        CommaActionRecord,
    )
    from number_compiler.sequences.comma.boundary_quotient import (
        BoundaryState,
        MacroTemplate,
        validate_macro_component_header,
    )
    from number_compiler.sequences.comma.boundary_receipt import (
        SOURCE,
        BoundaryPrefixCursor,
        BoundarySelectionReceiptID,
        CommaImagePayload,
        CommaOccurrenceRecord,
    )
    from number_compiler.sequences.comma.image_adapter import (
        CommaOccurrenceID,
        CommaSource,
    )

    if failure_prefix is not None:
        raise ValueError("comma images cannot publish a failure prefix")

    term = adapter.bound_term
    if (
        type(binding) is not SourceImageBinding
        or type(payload) is not CommaImagePayload
        or term is None
        or adapter.ledger is not term.ledger
        or adapter.arena is not term.arena
        or binding.family != adapter.family
        or binding.semantic_version != adapter.semantic_version
        or type(binding.action) is not CommaActionID
        or type(binding.extent) is not int
        or binding.extent < 0
        or binding.orientation != 1
        or binding.radix != 10
        or binding.precision is not None
        or type(binding.boundary_ports) is not tuple
        or len(binding.boundary_ports) != 3
        or any(type(value) is not int for value in binding.boundary_ports)
        or type(payload.value) is not int
        or payload.value < SOURCE
        or type(payload.absolute_index) is not int
        or payload.absolute_index < 1
        or type(payload.certificate_version) is not str
        or payload.certificate_version != term.certificate_version
        or (
            payload.boundary_cursor is not None
            and type(payload.boundary_cursor) is not BoundaryPrefixCursor
        )
    ):
        raise ValueError("comma image has invalid family binding fields")

    term_snapshot = term.audit_snapshot()

    output_ports = cast(tuple[int, int, int], binding.boundary_ports)
    if not (
        1 <= output_ports[0] <= 9 and 0 <= output_ports[1] <= 9 and output_ports[2] >= 1
    ):
        raise ValueError("comma image has invalid boundary ports")
    if payload.boundary_cursor is not None:
        from number_compiler.sequences.comma.boundary_quotient import (
            PERIOD,
            BoundaryState,
            boundary_state_signature,
        )

        cursor = payload.boundary_cursor
        if (
            type(cursor.state) is not BoundaryState
            or type(cursor.exponent) is not int
            or cursor.exponent < 5
            or cursor.exponent % PERIOD != cursor.state.exponent_residue
            or type(cursor.transitions) is not int
            or cursor.transitions < 0
            or payload.absolute_index - cursor.transitions < 1
        ):
            raise ValueError("comma image has an invalid boundary cursor shape")
        boundary_state_signature(cursor.state)

    action = binding.action
    action_arena = adapter.arena.audit_snapshot()
    action.validate(action_arena.token, action_arena.kind, size=len(action_arena.nodes))
    node = action_arena.nodes[action.local_id]
    if type(node) is not CommaActionRecord:
        raise ValueError("comma image action has another node sort")

    def require_audited_template(state: BoundaryState) -> MacroTemplate:
        template = action_arena.boundary_templates.get(state)
        seal = action_arena.boundary_seals.get(state)
        if (
            type(template) is not MacroTemplate
            or template.source != state
            or type(seal) is not tuple
            or not template.owns_component_seal(seal)
        ):
            raise ValueError("comma image lost its sealed boundary template")
        validate_macro_component_header(template, seal)
        return template

    source_value: int
    source_index: int
    source_payload: CommaImagePayload
    source_ports: tuple[int, int, int] | None = None
    source = binding.source
    if type(source) is CommaSource:
        if (
            source.value != SOURCE
            or source.certificate_version != term.certificate_version
        ):
            raise ValueError("comma image has a foreign literal source")
        source_value, source_index = SOURCE, 1
        source_extent = 0
        source_payload = CommaImagePayload(SOURCE, 1, term.certificate_version)
    elif type(source) is CommaOccurrenceID:
        source.validate(
            term_snapshot.occurrence_token,
            term_snapshot.occurrence_kind,
            size=len(term_snapshot.occurrences),
        )
        if source.local_id >= len(term_snapshot.occurrence_seals):
            raise ValueError("comma image source occurrence has no seal")
        source_occurrence_record = term_snapshot.occurrences[source.local_id]
        if (
            type(source_occurrence_record) is not CommaOccurrenceRecord
            or source_occurrence_record
            is not term_snapshot.occurrence_seals[source.local_id]
            or source_occurrence_record.certificate_version != term.certificate_version
        ):
            raise ValueError("comma image source occurrence is unauthenticated")
        source_core = adapter.scheduler.published_source_image_core
        if source_core is None:
            raise ValueError(
                "comma image audit requires an existing source-image owner"
            )
        source_image = source_core.resolve_readonly(source_occurrence_record.image)
        if (
            source_image.binding.family != adapter.family
            or source_image.binding.semantic_version != adapter.semantic_version
            or type(source_image.binding.extent) is not int
            or source_image.binding.extent < 0
            or type(source_image.payload) is not CommaImagePayload
            or source_image.payload.value != source_occurrence_record.value
            or source_image.payload.absolute_index
            != source_occurrence_record.absolute_index
            or source_image.payload.certificate_version
            != source_occurrence_record.certificate_version
            or source_image.payload.boundary_cursor
            != source_occurrence_record.boundary_cursor
        ):
            raise ValueError("comma occurrence source image has another binding")
        source_value = source_occurrence_record.value
        source_index = source_occurrence_record.absolute_index
        # Every external source is admitted as a fresh image origin with
        # extent zero.  The occurrence's backing image authenticates its
        # payload and cursor, while its historical action extent belongs to a
        # prior publication and is not the base of this cumulative action.
        source_extent = 0
        source_payload = CommaImagePayload(
            source_occurrence_record.value,
            source_occurrence_record.absolute_index,
            source_occurrence_record.certificate_version,
            source_occurrence_record.boundary_cursor,
        )
    elif type(source) is SourceImageID:
        core = adapter.scheduler.published_source_image_core
        if core is None:
            raise ValueError(
                "comma image audit requires an existing source-image owner"
            )
        core_snapshot = core.audit_snapshot()
        source.validate(
            core_snapshot.owner, core_snapshot.kind, size=len(core_snapshot.nodes)
        )
        parent = core_snapshot.nodes[source.local_id]
        if (
            type(parent) is not SourceImageRecord
            or parent.binding.family != adapter.family
            or parent.binding.semantic_version != adapter.semantic_version
            or type(parent.binding.extent) is not int
            or parent.binding.extent < 0
            or type(parent.payload) is not CommaImagePayload
            or parent.payload.certificate_version != term.certificate_version
        ):
            raise ValueError("comma image source belongs to another family")
        source_value = parent.payload.value
        source_index = parent.payload.absolute_index
        # SourceImageID is also re-admitted as a fresh origin before an action
        # is applied.  Keep validating the parent binding and payload above;
        # only the new origin's extent starts at zero.
        source_extent = 0
        source_payload = parent.payload
        source_ports = cast(tuple[int, int, int], parent.binding.boundary_ports)
    else:
        raise ValueError("comma image has an unsupported source authority")

    source_cursor = source_payload.boundary_cursor
    if source_cursor is not None and type(source_cursor) is not BoundaryPrefixCursor:
        raise ValueError("comma source has another boundary cursor sort")
    if source_cursor is not None:
        source_receipt = source_cursor.selection_receipt
        if source_receipt is not None:
            if type(source_receipt) is not BoundarySelectionReceiptID:
                raise ValueError("comma source cursor has another receipt handle")
            resolved_source_receipt = term.resolve_boundary_selection_receipt(
                source_receipt
            )
            source_provider = term.require_global_future_provider(
                resolved_source_receipt.artifact_sha256
            )
            resolved_source_receipt.validate_provider(source_provider)
            resolved_source_receipt.validate_output(
                value=source_payload.value,
                absolute_index=source_payload.absolute_index,
                cursor=source_cursor,
                receipt_id=source_receipt,
            )

    expected_transitions = node.steps
    global_provider: object | None = None
    if node.kind == "source20-first-child":
        from number_compiler.sequences.comma.future_authority import (
            SOURCE20_FIRST_FORK_INDEX,
            SOURCE20_FIRST_FORK_VALUE,
        )

        if (
            source_index != SOURCE20_FIRST_FORK_INDEX
            or source_value != SOURCE20_FIRST_FORK_VALUE
            or source_payload.boundary_cursor is not None
        ):
            raise ValueError("comma source-20 action has another exact source")
        term.require_global_future_provider(node.future_digest)
        expected_transitions = 1
    elif node.kind == "global-boundary-return":
        from number_compiler.sequences.comma.arithmetic import decimal_sector
        from number_compiler.sequences.comma.occurrence import BoundaryOccurrence

        state = node.boundary_source
        global_provider = term.require_global_future_provider(node.future_digest)
        if (
            type(state) is not BoundaryState
            or type(source_cursor) is not BoundaryPrefixCursor
            or source_cursor.state != state
            or source_cursor.transitions != 0
        ):
            raise ValueError("comma global return lost its source cursor")
        exponent = decimal_sector(source_value).exponent
        source_boundary_occurrence = BoundaryOccurrence(state, exponent)
        if (
            source_cursor.exponent != exponent
            or source_boundary_occurrence.value() != source_value
        ):
            raise ValueError("comma global return has another exact source occurrence")
        template = require_audited_template(state)
        if template.outcome != "fork":
            raise ValueError("comma global return source is not a fork")
        expected_transitions = template.weight.evaluate(exponent) + 1

    if node.kind == "boundary-prefix-occurrence":
        from number_compiler.sequences.comma.boundary_quotient import (
            PERIOD,
            BoundaryState,
            boundary_state_signature,
        )

        state = node.boundary_source
        current_cursor = payload.boundary_cursor
        prior = source_payload.boundary_cursor
        if (
            type(state) is not BoundaryState
            or type(current_cursor) is not BoundaryPrefixCursor
            or current_cursor.state != state
        ):
            raise ValueError("comma receiver prefix lost its cursor authority")
        boundary_state_signature(state)
        if prior is None:
            if (
                current_cursor.exponent % PERIOD != state.exponent_residue
                or current_cursor.transitions != node.steps
            ):
                raise ValueError("comma receiver prefix has an invalid initial cursor")
        else:
            if (
                type(prior) is not BoundaryPrefixCursor
                or prior.state != state
                or current_cursor.exponent != prior.exponent
                or current_cursor.transitions != prior.transitions + node.steps
            ):
                raise ValueError("comma receiver prefix changed its cursor chart")
            if source_index - prior.transitions < 1:
                raise ValueError("comma receiver prefix has an invalid cursor origin")
        if payload.absolute_index != source_index + node.steps:
            raise ValueError("comma receiver prefix has an invalid cursor transport")

    # Extent is cumulative along the action chain from its freshly admitted
    # origin, whose extent is zero regardless of the source's prior history.
    if (
        binding.extent != source_extent + expected_transitions
        or payload.absolute_index != source_index + expected_transitions
    ):
        raise ValueError("comma image extent differs from its admitted action")
    if source_ports is not None and node.kind in ("cycle", "phase-prefix"):
        leading, digit, headroom = source_ports
        if (
            output_ports != (leading, digit, headroom - node.displacement)
            or payload.value != source_value + node.displacement
        ):
            raise ValueError("comma image lost its powered port transport")
    elif node.kind == "identity":
        if (
            payload.value != source_value
            or payload.boundary_cursor is not source_payload.boundary_cursor
        ):
            raise ValueError("comma identity changed its source payload")
    elif node.kind == "step" and payload.value != (
        source_value + 10 * (source_value % 10) + node.child_digit
    ):
        raise ValueError("comma primitive image changed its selected child")
    elif node.kind == "source20-first-child":
        from number_compiler.sequences.comma.future_authority import (
            SOURCE20_SELECTED_CHILD,
        )

        result_cursor = payload.boundary_cursor
        expected_state = BoundaryState("N", 2, 10)
        if (
            type(result_cursor) is not BoundaryPrefixCursor
            or result_cursor.selection_receipt is not None
            or result_cursor.state != expected_state
            or result_cursor.exponent != 10
            or result_cursor.transitions != 0
            or payload.value != SOURCE20_SELECTED_CHILD
            or payload.value != result_cursor.state.value(result_cursor.exponent)
        ):
            raise ValueError("comma source-20 action changed its issued child")
    elif node.kind == "global-boundary-return":
        from number_compiler.sequences.comma.arithmetic import decimal_sector

        state = node.boundary_source
        result_cursor = payload.boundary_cursor
        if type(state) is not BoundaryState:
            raise ValueError("comma global return has another boundary source sort")
        template = require_audited_template(state)
        source_exponent = decimal_sector(source_value).exponent
        output_sector = decimal_sector(payload.value)
        if (
            type(result_cursor) is not BoundaryPrefixCursor
            or type(result_cursor.selection_receipt) is not BoundarySelectionReceiptID
        ):
            raise ValueError("comma global return omitted its issued selection handle")
        result_receipt_id = result_cursor.selection_receipt
        result_receipt = term.resolve_boundary_selection_receipt(result_receipt_id)
        if global_provider is None:
            raise ValueError("comma global return lost its checked provider")
        result_receipt.validate_provider(global_provider)
        result_receipt.validate_source(
            source_state=state,
            source_exponent=source_exponent,
            source_value=source_value,
            source_index=source_index,
            source_extent=source_extent,
        )
        selected_slot = result_receipt.selection.selected_slot
        if (
            result_receipt.selection.fork_coefficient != template.destination_a
            or selected_slot not in (0, 1)
            or result_receipt.target_state != template.ordered_children[selected_slot]
            or result_receipt.target_exponent
            != source_exponent + template.exponent_delta
            or result_receipt.transitions != expected_transitions
            or result_cursor.transitions != 0
            or result_cursor.state != result_receipt.target_state
            or result_cursor.exponent != result_receipt.target_exponent
            or payload.value != result_receipt.target_value
            or payload.value != result_cursor.state.value(result_cursor.exponent)
            or output_ports
            != (
                output_sector.leading,
                output_sector.digit,
                output_sector.headroom,
            )
        ):
            raise ValueError("comma global return changed its issued child cursor")
        result_receipt.validate_output(
            value=payload.value,
            absolute_index=payload.absolute_index,
            cursor=result_cursor,
            receipt_id=result_receipt_id,
        )
    elif (
        node.kind != "boundary-prefix-occurrence"
        and payload.boundary_cursor is not None
    ):
        raise ValueError("comma non-boundary action retained a stale cursor")
    if payload.boundary_cursor is not None:
        return (payload.boundary_cursor,)
    return None


def register_comma_term_audit(term: CommaTerm) -> None:
    from number_compiler.resources.payload_contracts import (
        PayloadAuditStoreBinding,
    )

    term.ledger.register_execution_root(term)
    term_snapshot = term.audit_snapshot()
    arena = term_snapshot.arena
    term.ledger.register_payload_audit_contract(
        term,
        "comma",
        (
            PayloadAuditStoreBinding(
                arena.owner,
                "_audit_action_nodes",
                "temporal_action",
            ),
            PayloadAuditStoreBinding(
                arena.key_owner,
                "_audit_action_keys",
                "action_interning",
            ),
            PayloadAuditStoreBinding(
                arena.snapshot_owner,
                "_audit_action_snapshots",
                "action_publication_seal",
            ),
            PayloadAuditStoreBinding(
                arena.boundary_owner,
                "_audit_boundary_templates",
                "boundary_template",
            ),
            PayloadAuditStoreBinding(
                arena.boundary_seal_owner,
                "_audit_boundary_seals",
                "boundary_publication_seal",
            ),
            PayloadAuditStoreBinding(
                arena.boundary_seal_node_owner,
                "_audit_boundary_seal_nodes",
                "boundary_publication_seal_component",
            ),
            PayloadAuditStoreBinding(
                arena.boundary_node_owner,
                "_audit_boundary_nodes",
                "boundary_template_node",
            ),
            PayloadAuditStoreBinding(
                term_snapshot.occurrence_owner,
                "_audit_occurrences",
                "source_occurrence",
            ),
            PayloadAuditStoreBinding(
                term_snapshot.occurrence_seal_owner,
                "_audit_occurrence_seals",
                "source_occurrence_seal",
            ),
            PayloadAuditStoreBinding(
                term_snapshot.boundary_receipt_owner,
                "_audit_boundary_receipts",
                "boundary_selection_receipt",
            ),
            PayloadAuditStoreBinding(
                term_snapshot.boundary_receipt_seal_owner,
                "_audit_boundary_receipt_seals",
                "boundary_selection_receipt_seal",
            ),
        ),
        audit_comma_term,
    )
