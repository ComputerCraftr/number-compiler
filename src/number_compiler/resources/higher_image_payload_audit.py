"""Independent ownership checks for retained temporal source images."""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.hashlife.execution.continuations.higher_temporal_image import (
    HigherTemporalImage,
    HigherTemporalImageArena,
)
from number_compiler.resources.ledger import ResourceLedger


def audit_temporal_image_owner(
    root: HigherTemporalImageArena,
    ledger: ResourceLedger,
    containers: Mapping[int, object],
) -> tuple[frozenset[int], frozenset[tuple[int, int]]]:
    """Admit issued image records, never caller-supplied macro summaries."""
    snapshot = root.audit_snapshot()
    stores = (
        (snapshot.node_owner, snapshot.node_store),
        (snapshot.key_owner, snapshot.key_store),
        (snapshot.seal_owner, snapshot.seal_store),
        (snapshot.frame_owner, snapshot.frame_store),
        (snapshot.built_owner, snapshot.built_store),
        (snapshot.source_frame_owner, snapshot.source_frame_store),
        (snapshot.source_summary_owner, snapshot.source_summary_store),
    )
    valid_root = (
        snapshot.ledger is ledger
        and root.spatial.ledger is ledger
        and root.semantics is root.spatial.semantics
        and root.interfaces is root.spatial.interfaces
        and root.outputs is root.spatial.outputs
        and root.sources is root.spatial.sources
        and snapshot.running is False
        and snapshot.frame_count == 0
        and snapshot.built_count == 0
        and snapshot.source_frame_count == 0
        and snapshot.source_summary_count == 0
        and len(snapshot.nodes) == len(snapshot.keys) == len(snapshot.seals)
        and all(
            containers.get(owner) is store and ledger.is_factory_container(store)
            for owner, store in stores
        )
    )
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    try:
        root.validate_authority()
    except (TypeError, ValueError, AttributeError):
        valid_root = False
    if not valid_root:
        invalid.update((owner, id(store)) for owner, store in stores)
        return frozenset(), frozenset(invalid)
    for index, record in enumerate(snapshot.nodes):
        valid = type(record) is HigherTemporalImage
        try:
            valid &= root.resolve(root.handle_for_local_id(index)) is record
            key_index = snapshot.keys.get(record)
            valid &= type(key_index) is int and key_index == index
            valid &= root.seal_matches(record, snapshot.seals[index])
            valid &= record.predecessor is None or record.predecessor.local_id < index
        except (TypeError, ValueError, KeyError, IndexError, AttributeError):
            valid = False
        if valid:
            seal = root._seals[index]
            approved.update((id(record), id(record.macro), id(seal)))
            approved.update(id(field) for field in seal)
        else:
            invalid.add((snapshot.node_owner, id(record)))
    if not invalid:
        approved.update(id(store) for _owner, store in stores)
    return frozenset(approved), frozenset(invalid)
