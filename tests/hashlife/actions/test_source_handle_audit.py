"""Source tile identities use actual arena membership, not local node-count bounds."""

from typing import cast

import pytest

from devtools.proofs.lazy_collatz_range import _SourceTileKey
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.fields.dyadic_tile import leaf
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    FieldCellActionID,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.field_images import SourceBindingID
from number_compiler.hashlife.execution.field_transfers import FieldTransferRequestKey
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def test_late_global_source_ids_remain_valid_in_a_small_index() -> None:
    # Push the process-global, monotonic exact-source namespace well beyond
    # this index's independent ledger population.  The test must not rely on
    # an old fixed gap: newly registered semantic arenas legitimately add
    # index-owned entries without changing source-handle validity.
    retained = [leaf(symbol) for symbol in range(100_000, 102_000)]
    term = ReverseAddPoweredTerm(100, 1, base=101)
    assert term.digit(0) == 99
    index = term._point_index()
    source_ids = {tile.node_id for tile in index._source_geometry.nodes.values()}
    metrics = term.metrics()
    assert (
        max(source_ids)
        > metrics.resource_ledger_nodes + metrics.resource_ledger_entries
    )
    assert retained
    assert metrics.representation_boundary_complete == 1
    assert metrics.retained_point_response_scalars == 1


@pytest.mark.parametrize("foreign", (False, True))
@pytest.mark.parametrize("wrapped", ("direct", "collatz", "field-transfer"))
def test_unowned_source_handles_are_rejected_even_inside_known_records(
    foreign: bool, wrapped: str
) -> None:
    term = ReverseAddPoweredTerm(18, 1)
    term.digit(0)
    index = term._point_index()
    geometry = index._source_geometry
    node_id = next(iter(geometry.nodes.values())).node_id
    owner = ArenaToken("foreign-source") if foreign else geometry.token
    if not foreign:
        node_id = max(tile.node_id for tile in geometry.nodes.values()) + 10_000_000
    handle = ArenaHandle(owner, "source-tile", node_id)
    record = (
        handle
        if wrapped == "direct"
        else (
            _SourceTileKey(handle, 8)
            if wrapped == "collatz"
            else FieldTransferRequestKey(
                FieldCellActionID(ArenaToken("action"), "field-cell-action", 0),
                cast("SourceBindingID", handle),
                FieldGeometryID(ArenaToken("geometry"), "field-geometry", 0),
                PortSignatureID(ArenaToken("signature"), "port-signature", 0),
            )
        )
    )
    account = term._ledger.register("forged-source-handle", "spatial_binding")
    records: LedgerList[object]
    records = term._ledger.make_list(account)
    term._ledger.reserve(account, entries=1, nodes=1)
    records.append(record)
    report = collect_ledger_metrics(term._ledger)
    assert report.resource_accounting_mismatch == 0
    assert report.forbidden_future_payloads > 0
    assert report.representation_boundary_complete == 0
