"""Demand certificates are scoped finite-interface records, not scalar caches."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.hashlife.execution.diamond_primitive_demand import (
    PrimitiveDemandCertificate,
    PrimitiveDemandOracle,
)
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.observation.diamond_observers import NonblankBlockEffect
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerList


def populated() -> tuple[DiamondKernelArena, PrimitiveDemandOracle]:
    kernels = DiamondKernelArena()
    kernel = kernels.intern(NonblankBlockEffect(2, 2))
    demand = PrimitiveDemandOracle(kernels)
    assert demand.constant(kernel, "advance", 0, (1, None)) == 1
    return kernels, demand


def test_demand_inventory_is_read_only_and_reports_actual_work_and_slots() -> None:
    kernels, demand = populated()
    before = kernels.ledger.snapshot()
    report = collect_ledger_metrics(kernels.ledger)
    assert kernels.ledger.snapshot() == before
    assert report.representation_boundary_complete == 1
    assert report.resource_work_counters["primitive_demand_completion_tests"] == 3
    assert report.resource_workspace_peaks["primitive_demand_cursor_peak"] == 2
    inventory = next(
        row for row in kernels.ledger.inventory() if row.owner == demand.owner
    )
    assert inventory.observed_entries == len(demand.memo) == 1
    assert inventory.accounting_delta == 0


@pytest.mark.parametrize(
    "failure",
    (
        "foreign-kernel",
        "wrong-argument-domain",
        "wrong-result-domain",
        "unowned-certificate",
        "fully-known",
    ),
)
def test_demand_records_cannot_bypass_actual_memo_scope_and_port_domains(
    failure: str,
) -> None:
    kernels, demand = populated()
    key, certificate = next(iter(demand.memo.items()))
    if failure == "foreign-kernel":
        other = DiamondKernelArena(kernels.ledger)
        foreign = other.intern(NonblankBlockEffect(2, 2))
        demand.memo[replace(key, kernel=foreign)] = certificate
    elif failure == "wrong-argument-domain":
        demand.memo[replace(key, values=(2, None))] = certificate
    elif failure == "wrong-result-domain":
        demand.memo[key] = PrimitiveDemandCertificate(2)
    elif failure == "fully-known":
        demand.memo[replace(key, values=(1, 0))] = certificate
    else:
        owner = kernels.ledger.register("unowned-demand-record", "query_memo")
        store: LedgerList[object]
        store = kernels.ledger.make_list(owner)
        kernels.ledger.reserve(owner, entries=1, nodes=1)
        store.append(PrimitiveDemandCertificate(1))
    assert collect_ledger_metrics(kernels.ledger).forbidden_future_payloads > 0
