"""Read-only authority audit for retained comma actions and boundary templates."""

from __future__ import annotations

from collections.abc import Mapping
from typing import cast

from number_compiler.resources.ledger import ResourceLedger


def audit_comma_source_adapter(
    adapter: object,
    ledger: ResourceLedger,
    containers: Mapping[int, object],
    image_owner: int,
) -> tuple[frozenset[int], frozenset[int], frozenset[tuple[int, int]]]:
    """Approve only objects in this adapter's authenticated retained stores.

    A well-shaped template remains an arithmetic descriptor.  This audit does
    not assert the periodic lifting theorem or authorize a fork child.
    """
    from number_compiler.resources.source_bound_payload_audit import _resolve_readonly
    from number_compiler.sequences.comma.action_arena import (
        CommaActionArena,
        CommaActionID,
        _Action,
        _action_snapshot,
        _template_seal,
    )
    from number_compiler.sequences.comma.boundary_quotient import (
        PERIOD,
        AffineWeight,
        BoundaryState,
        MacroTemplate,
        SectorFragment,
    )
    from number_compiler.sequences.comma.power import (
        CommaImagePayload,
        _CommaImageAdapter,
        _Occurrence,
    )

    if type(adapter) is not _CommaImageAdapter:
        return frozenset(), frozenset(), frozenset()
    approved: set[int] = set()
    recognized: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    arena = adapter.arena
    if type(arena) is not CommaActionArena or adapter.ledger is not ledger:
        return frozenset(), frozenset(), frozenset({(image_owner, id(adapter))})
    stores = (
        (arena._owner, arena._nodes),
        (arena._key_owner, arena._keys),
        (arena._snapshot_owner, arena._snapshots),
        (arena._boundary_owner, arena._boundary_templates),
        (arena._boundary_seal_owner, arena._boundary_seals),
        (arena._boundary_seal_node_owner, arena._boundary_seal_nodes),
        (arena._boundary_node_owner, arena._boundary_nodes),
    )
    if any(containers.get(owner) is not store for owner, store in stores):
        return frozenset(), frozenset(), frozenset({(arena._owner, id(arena))})

    if len(arena._nodes) != len(arena._snapshots):
        invalid.add((arena._owner, id(arena)))
    canonical: dict[int, CommaActionID] = {}
    for key, identifier in arena._keys.items():
        recognized.update((id(key), id(identifier)))
        try:
            if type(key) is not tuple or type(identifier) is not CommaActionID:
                raise TypeError("comma action interning has another key or ID")
            identifier.validate(arena.token, arena.kind, size=len(arena._nodes))
            node = arena.node(identifier)
            if identifier.local_id in canonical:
                raise ValueError("comma action has multiple canonical keys")
            expected_key: tuple[object, ...]
            if node.kind == "identity":
                if node.steps != 0:
                    raise ValueError("comma identity has duration")
                expected_key = ("identity",)
            elif node.kind == "step":
                if node.steps != 1 or not 1 <= node.child_digit <= 9:
                    raise ValueError("comma step has another child")
                expected_key = ("step", node.child_digit)
            elif node.kind == "cycle":
                if node.cycles < 1 or node.steps < 1:
                    raise ValueError("comma cycle has invalid duration")
                expected_key = (
                    "cycle",
                    node.leading,
                    node.entering_digit,
                    node.cycles,
                )
            elif node.kind == "phase-prefix":
                if (
                    type(node.steps) is not int
                    or not 0 < node.steps < 10
                    or not 1 <= node.leading <= 9
                    or not 0 <= node.entering_digit <= 9
                ):
                    raise ValueError("comma phase prefix has invalid coordinates")
                expected_key = (
                    "phase-prefix",
                    node.leading,
                    node.entering_digit,
                    node.steps,
                )
            elif node.kind == "sequence":
                if node.before is None or node.after is None:
                    raise ValueError("comma sequence lost a chronological child")
                expected_key = ("sequence", node.before, node.after)
            elif node.kind == "boundary-prefix":
                state = node.boundary_source
                if (
                    type(state) is not BoundaryState
                    or node.steps < 0
                    or node.boundary_exponent < 5
                    or node.boundary_exponent % PERIOD != state.exponent_residue
                ):
                    raise ValueError("comma prefix lost its boundary binding")
                expected_key = (
                    "boundary-prefix",
                    state,
                    node.boundary_exponent,
                    node.steps,
                )
            else:
                raise ValueError("comma action has an unknown kind")
            if key != expected_key:
                raise ValueError("comma action key differs from its semantics")
        except (TypeError, ValueError, IndexError, AttributeError):
            invalid.add((arena._key_owner, id(key)))
        else:
            canonical[identifier.local_id] = identifier
            approved.update((id(key), id(identifier)))
    for local_id, node in enumerate(arena._nodes):
        recognized.add(id(node))
        if local_id < len(arena._snapshots):
            recognized.add(id(arena._snapshots[local_id]))
        try:
            if (
                type(node) is not _Action
                or local_id not in canonical
                or _action_snapshot(node) != arena._snapshots[local_id]
            ):
                raise ValueError("comma action publication differs from its seal")
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
                    != arena._nodes[before.local_id].steps
                    + arena._nodes[after.local_id].steps
                ):
                    raise ValueError("comma action has an invalid composition")
            elif node.kind == "boundary-prefix":
                state = node.boundary_source
                if state is None or state not in arena._boundary_templates:
                    raise ValueError("comma prefix has no retained template")
                if node.boundary_exponent != (
                    state.exponent_residue
                    if state.exponent_residue >= 5
                    else state.exponent_residue + PERIOD
                ):
                    raise ValueError("comma prefix used an unproved exponent lift")
            approved.update((id(node), id(arena._snapshots[local_id])))
        except (TypeError, ValueError, IndexError, AttributeError):
            invalid.add((arena._owner, id(node)))
    if len(canonical) != len(arena._nodes):
        invalid.add((arena._owner, id(arena)))

    expected_nodes: list[object] = []
    expected_seal_nodes: list[object] = []
    if len(arena._boundary_seals) != len(arena._boundary_templates):
        invalid.add((arena._boundary_seal_owner, id(arena._boundary_seals)))
    for state, template in arena._boundary_templates.items():
        recognized.update((id(state), id(template)))
        try:
            template_seal = arena._boundary_seals[state]
            recognized.add(id(template_seal))
            if type(template_seal) is not tuple or template_seal != _template_seal(
                template
            ):
                raise ValueError("comma boundary template differs from its seal")
            if (
                type(state) is not BoundaryState
                or type(template) is not MacroTemplate
                or template.source is not state
                or template.outcome not in ("fork", "landmine")
                or type(template.exponent_delta) is not int
                or template.exponent_delta < 0
                or type(template.weight) is not AffineWeight
                or type(template.endpoint) is not AffineWeight
                or type(template.sector_fragments) is not tuple
                or type(template.prefix_weights) is not tuple
                or type(template.prefix_displacements) is not tuple
                or len(template.prefix_weights) != len(template.sector_fragments) + 1
                or len(template.prefix_displacements)
                != len(template.sector_fragments) + 1
                or template.prefix_weights[0] != AffineWeight(0, 0, 1)
                or template.prefix_displacements[0] != AffineWeight(0, 0, 1)
                or template.prefix_weights[-1] != template.weight
                or any(
                    type(item) is not SectorFragment
                    for item in template.sector_fragments
                )
                or any(
                    type(item) is not AffineWeight for item in template.prefix_weights
                )
                or any(
                    type(item) is not AffineWeight
                    for item in template.prefix_displacements
                )
            ):
                raise ValueError("comma boundary template has another shape")
            if template.outcome == "fork":
                if (
                    template.destination_a is None
                    or len(template.ordered_children) != 2
                    or template.ordered_children[0]
                    != BoundaryState(
                        "N",
                        template.destination_a,
                        (state.exponent_residue + template.exponent_delta) % PERIOD,
                    )
                    or template.ordered_children[1]
                    != BoundaryState(
                        "Z",
                        template.destination_a,
                        (state.exponent_residue + template.exponent_delta) % PERIOD,
                    )
                ):
                    raise ValueError("comma fork template lost its ordered children")
            elif template.destination_a is not None or template.ordered_children:
                raise ValueError("comma landmine template fabricated children")
            components: tuple[object, ...] = (
                template,
                *template.sector_fragments,
                *template.prefix_weights,
                *template.prefix_displacements,
            )
            expected_nodes.extend(components)
            expected_seal_nodes.extend(cast(tuple[object, ...], template_seal[1]))
            expected_seal_nodes.extend(cast(tuple[object, ...], template_seal[2]))
            expected_seal_nodes.extend(cast(tuple[object, ...], template_seal[3]))
            approved.update(map(id, components))
            approved.add(id(template_seal))
            approved.update(
                map(
                    id,
                    (
                        state,
                        template.sector_fragments,
                        template.prefix_weights,
                        template.prefix_displacements,
                        template.ordered_children,
                        template.weight,
                        template.endpoint,
                    ),
                )
            )
            for child in template.ordered_children:
                approved.add(id(child))
            for fragment in template.sector_fragments:
                approved.add(id(fragment.complete_cycles))
        except (TypeError, ValueError, KeyError, IndexError, AttributeError):
            invalid.add((arena._boundary_owner, id(template)))
    if len(expected_nodes) != len(arena._boundary_nodes) or any(
        actual is not expected
        for actual, expected in zip(arena._boundary_nodes, expected_nodes, strict=True)
    ):
        invalid.add((arena._boundary_node_owner, id(arena._boundary_nodes)))
    else:
        approved.update(map(id, arena._boundary_nodes))
    recognized.update(map(id, arena._boundary_nodes))
    if len(expected_seal_nodes) != len(arena._boundary_seal_nodes) or any(
        actual is not expected
        for actual, expected in zip(
            arena._boundary_seal_nodes, expected_seal_nodes, strict=True
        )
    ):
        invalid.add((arena._boundary_seal_node_owner, id(arena._boundary_seal_nodes)))
    else:
        approved.update(map(id, arena._boundary_seal_nodes))
    recognized.update(map(id, arena._boundary_seal_nodes))
    term = adapter._term
    if term is not None:
        if (
            term.adapter is not adapter
            or term.arena is not arena
            or term.ledger is not ledger
            or containers.get(term._occurrence_owner) is not term._occurrences
            or containers.get(term._occurrence_seal_owner) is not term._occurrence_seals
            or len(term._occurrences) != len(term._occurrence_seals)
        ):
            invalid.add((image_owner, id(term)))
        else:
            core = term.scheduler._source_image_core()
            for occurrence, seal in zip(
                term._occurrences, term._occurrence_seals, strict=True
            ):
                recognized.add(id(occurrence))
                try:
                    if (
                        type(occurrence) is not _Occurrence
                        or occurrence is not seal
                        or occurrence.certificate_version != term.certificate_version
                    ):
                        raise ValueError("comma occurrence lost its publication")
                    record = _resolve_readonly(core, occurrence.image)
                    if record.adapter_key != (
                        adapter.family,
                        adapter.semantic_version,
                    ) or record.payload != CommaImagePayload(
                        occurrence.value,
                        occurrence.absolute_index,
                        occurrence.certificate_version,
                    ):
                        raise ValueError("comma occurrence has another source image")
                except (TypeError, ValueError, IndexError, AttributeError):
                    invalid.add((term._occurrence_owner, id(occurrence)))
                else:
                    approved.add(id(occurrence))
    return frozenset(approved), frozenset(recognized), frozenset(invalid)


__all__ = ["audit_comma_source_adapter"]
