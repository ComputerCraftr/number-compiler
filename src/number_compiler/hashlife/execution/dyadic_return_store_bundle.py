"""Ledger registration for a dyadic return image workspace."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnActionID,
    DyadicReturnActionRecord,
    DyadicReturnImageID,
    DyadicReturnImageRecord,
    DyadicReturnSourceRecord,
    DyadicReturnSupportID,
    DyadicReturnSupportRecord,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList


@dataclass(frozen=True, slots=True)
class DyadicReturnStoreBundle:
    action_owner: int
    source_owner: int
    support_owner: int
    image_owner: int
    width_owner: int
    construction_owner: int
    action_snapshot_owner: int
    source_snapshot_owner: int
    support_snapshot_owner: int
    image_snapshot_owner: int
    macro_owner: int
    macro_stack_owner: int
    balanced_stack_owner: int
    demanded_support_owner: int
    demanded_support: LedgerDict[DyadicReturnImageID, DyadicReturnSupportID]
    macros: LedgerDict[tuple[object, ...], DyadicReturnSupportRecord]
    macro_stack: LedgerList[tuple[int, int, DyadicReturnSupportRecord | None]]
    balanced_stack: LedgerList[
        tuple[
            int,
            int,
            tuple[DyadicReturnSupportRecord, DyadicReturnSupportID | None] | None,
        ]
    ]
    actions: LedgerList[DyadicReturnActionRecord]
    sources: LedgerList[DyadicReturnSourceRecord]
    support: LedgerList[DyadicReturnSupportRecord]
    images: LedgerList[DyadicReturnImageRecord]
    by_width: LedgerDict[int, DyadicReturnActionID]
    construction_stack: LedgerList[int]
    action_snapshots: LedgerDict[int, object]
    source_snapshots: LedgerDict[int, object]
    support_snapshots: LedgerDict[int, object]
    image_snapshots: LedgerDict[int, object]


def create_dyadic_return_store_bundle(
    ledger: ResourceLedger,
    prefix: str,
    *,
    action_role: str,
    source_role: str,
    support_role: str,
    image_role: str,
) -> DyadicReturnStoreBundle:
    """Register one complete action/source/support/image owner graph."""
    action_owner = ledger.register(prefix + "-actions", action_role)
    source_owner = ledger.register(prefix + "-sources", source_role)
    support_owner = ledger.register(prefix + "-support", support_role)
    image_owner = ledger.register(prefix + "-images", image_role)
    width_owner = ledger.register(prefix + "-widths", "dyadic_return_action_index")
    construction_owner = ledger.register(prefix + "-construction", "workspace")
    action_snapshot_owner = ledger.register(prefix + "-action-snapshots", "workspace")
    source_snapshot_owner = ledger.register(prefix + "-source-snapshots", "workspace")
    support_snapshot_owner = ledger.register(prefix + "-support-snapshots", "workspace")
    image_snapshot_owner = ledger.register(prefix + "-image-snapshots", "workspace")
    macro_owner = ledger.register(prefix + "-macros", "dyadic_return_macro_index")
    macro_stack_owner = ledger.register(prefix + "-macro-stack", "workspace")
    balanced_stack_owner = ledger.register(prefix + "-balanced-stack", "workspace")
    demanded_support_owner = ledger.register(
        prefix + "-demanded-support", "dyadic_return_support_demand_index"
    )
    return DyadicReturnStoreBundle(
        action_owner=action_owner,
        source_owner=source_owner,
        support_owner=support_owner,
        image_owner=image_owner,
        width_owner=width_owner,
        construction_owner=construction_owner,
        action_snapshot_owner=action_snapshot_owner,
        source_snapshot_owner=source_snapshot_owner,
        support_snapshot_owner=support_snapshot_owner,
        image_snapshot_owner=image_snapshot_owner,
        macro_owner=macro_owner,
        macro_stack_owner=macro_stack_owner,
        balanced_stack_owner=balanced_stack_owner,
        demanded_support_owner=demanded_support_owner,
        demanded_support=ledger.make_dict(demanded_support_owner, nodes_per_entry=0),
        macros=ledger.make_dict(macro_owner, nodes_per_entry=1),
        macro_stack=ledger.make_list(
            macro_stack_owner, nodes_per_entry=1, append_only=False
        ),
        balanced_stack=ledger.make_list(
            balanced_stack_owner, nodes_per_entry=1, append_only=False
        ),
        actions=ledger.make_list(action_owner, nodes_per_entry=1, append_only=False),
        sources=ledger.make_list(source_owner, nodes_per_entry=1, append_only=False),
        support=ledger.make_list(support_owner, nodes_per_entry=1, append_only=False),
        images=ledger.make_list(image_owner, nodes_per_entry=1, append_only=False),
        by_width=ledger.make_dict(width_owner, nodes_per_entry=0),
        construction_stack=ledger.make_list(
            construction_owner, nodes_per_entry=1, append_only=False
        ),
        action_snapshots=ledger.make_dict(action_snapshot_owner, nodes_per_entry=1),
        source_snapshots=ledger.make_dict(source_snapshot_owner, nodes_per_entry=1),
        support_snapshots=ledger.make_dict(support_snapshot_owner, nodes_per_entry=1),
        image_snapshots=ledger.make_dict(image_snapshot_owner, nodes_per_entry=1),
    )


__all__ = ["DyadicReturnStoreBundle", "create_dyadic_return_store_bundle"]
