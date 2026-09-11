"""Atomic publication of normalized parent identities and their image cells."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.actions.diamond_actions import (
    CellNode,
    ImageCellArena,
    TemporalActionArena,
)
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    MacroTransferKey,
)
from number_compiler.resources.ledger import OwnedMemo


def publish_parent_identity(
    actions: TemporalActionArena,
    cells: ImageCellArena,
    bindings: OwnedMemo[MacroTransferKey, ActionProgramID],
    key: MacroTransferKey,
) -> ActionProgramID:
    """Reserve the action, image, interners and parent binding together.

    This cache names a program, not an extensional transfer equivalence class.
    Its publication precedes any descendant work. The executable transfer is
    obtained separately by the scheduler using that canonical identity.
    """
    if cells.actions is not actions or bindings.ledger is not actions.ledger:
        raise ValueError("parent publication requires one owning index")
    if (
        type(key) is not MacroTransferKey
        or type(key.side) is not int
        or key.side not in (0, 1)
    ):
        raise ValueError("invalid parent identity")
    before, after, cell = (
        actions.resolve(key.before),
        actions.resolve(key.after),
        cells.resolve(key.cell),
    )
    source = cells.source_geometry._construction.source
    for action in (before, after):
        if action.kind != "identity" and (action.base, action.blank) != (
            source.base,
            source.blank,
        ):
            raise ValueError("parent and source alphabets disagree")
    cells.require_original(key.cell)
    found = bindings.get(key)
    if found is not None:
        actions.resolve(found)
        actions.ledger.bump("image_program_requests")
        actions.ledger.bump("image_program_cache_hits")
        actions.ledger.bump("image_program_admission_visits", 1)
        return found
    result, temporal = actions._plan_compose(key.before, key.after)
    # A staged action is a composition; existing identity actions have no image.
    identity = temporal is None and actions.node(result).kind == "identity"
    image = (
        None
        if identity
        else CellNode(
            "image", cell.level, left=key.cell.local_id, action=result.local_id
        )
    )
    image_key = None if image is None else cells._key(image)
    existing_image = None if image_key is None else cells._ids.get(image_key)
    reservations = [(bindings.owner, 1, bindings.nodes_per_entry)]
    if temporal is not None:
        reservations.extend(((actions._node_owner, 1, 1), (actions._index_owner, 1, 0)))
    if image is not None and existing_image is None:
        reservations.extend(((cells._node_owner, 1, 1), (cells._index_owner, 1, 0)))
    ledger = actions.ledger
    ledger.reserve_many(reservations)
    if temporal is not None:
        actions._ids[temporal] = result.local_id
        actions._nodes.append(temporal)
    if image is not None and existing_image is None:
        assert image_key is not None
        cells._ids[image_key] = len(cells._nodes)
        cells._nodes.append(image)
    # OwnedMemo.__setitem__ would reserve a second time. This store has already
    # received its share of the same atomic reservation as both canonical nodes.
    bindings._data[key] = result
    ledger.bump("image_program_requests")
    ledger.bump("image_program_evaluations")
    ledger.bump("image_program_admission_visits", 1)
    ledger.bump("diamond_temporal_composition_requests")
    ledger.bump(
        "diamond_temporal_composition_hits"
        if temporal is None
        else "diamond_temporal_composition_evaluations"
    )
    if image is not None:
        ledger.bump(
            "diamond_cell_interner_hits"
            if existing_image is not None
            else "diamond_cell_interner_evaluations"
        )
        ledger.bump("diamond_image_normalized_requests")
    return result
