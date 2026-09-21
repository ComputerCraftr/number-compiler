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
    stores = (
        (root._node_owner, root._nodes),
        (root._key_owner, root._keys),
        (root._seal_owner, root._seals),
        (root._frame_owner, root._frames),
        (root._built_owner, root._built),
        (root._source_frame_owner, root._source_frames),
        (root._source_summary_owner, root._source_summaries),
    )
    valid_root = (
        root.ledger is ledger
        and root.spatial.ledger is ledger
        and root.semantics is root.spatial.semantics
        and root.interfaces is root.spatial.interfaces
        and root.outputs is root.spatial.outputs
        and root.sources is root.spatial.sources
        and root._running is False
        and not root._frames
        and not root._built
        and not root._source_frames
        and not root._source_summaries
        and len(root._nodes) == len(root._keys) == len(root._seals)
        and all(
            containers.get(owner) is store and ledger.is_factory_container(store)
            for owner, store in stores
        )
    )
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    if not valid_root:
        invalid.update((owner, id(store)) for owner, store in stores)
        return frozenset(), frozenset(invalid)
    for index, record in enumerate(root._nodes):
        valid = type(record) is HigherTemporalImage
        try:
            valid &= root.resolve(root._handle(index)) is record
            key_index = root._keys.get(record)
            valid &= type(key_index) is int and key_index == index
            valid &= type(root._seals[index]) is tuple
            valid &= root._seals[index] == root._seal(record)
            valid &= record.predecessor is None or record.predecessor.local_id < index
        except (TypeError, ValueError, KeyError, IndexError, AttributeError):
            valid = False
        if valid:
            seal = root._seals[index]
            approved.update((id(record), id(record.macro), id(seal)))
            approved.update(id(field) for field in seal)
        else:
            invalid.add((root._node_owner, id(record)))
    if not invalid:
        approved.update(id(store) for _owner, store in stores)
    return frozenset(approved), frozenset(invalid)
