"""Cold M(N, X) probes remain order-independent and index-isolated."""

from __future__ import annotations

from types import SimpleNamespace
from typing import TYPE_CHECKING

import pytest

from devtools.benchmarks.field_image_growth_probe import (
    cold_measurement,
    cold_rows,
    ordered_horizons,
)
from number_compiler.resources.temporal_diagnostics import METRICS_SCHEMA_VERSION
from tests.support.report_values import object_record, text_values

if TYPE_CHECKING:
    import types


class _Term:
    def __init__(self, horizon: int, ledger: object | None = None) -> None:
        self.horizon = horizon
        self._ledger = object() if ledger is None else ledger

    def digit(self, position: int) -> int:
        assert position == 0
        return self.horizon & 1

    def metrics(self) -> types.SimpleNamespace:
        return SimpleNamespace(
            metrics_schema_version=METRICS_SCHEMA_VERSION,
            new_canonical_field_images_published=self.horizon.bit_length(),
            field_image_nodes=self.horizon.bit_length(),
            field_interface_nodes=1,
            total_internal_action_work=2 * self.horizon.bit_length(),
            temporal_parent_compositions=self.horizon.bit_length(),
            spatial_parent_evaluations=self.horizon.bit_length(),
            resource_ledger_entries=3,
            resource_ledger_nodes=2,
            forbidden_future_payloads=0,
            sequential_generation_advances=0,
            whole_word_sweeps=0,
            whole_word_symbol_visits=0,
            proof_machine_applications=0,
            resource_accounting_mismatch=0,
        )


def test_horizon_orders_are_explicit_and_exact() -> None:
    assert ordered_horizons((32, 16, 64), "ascending") == (16, 32, 64)
    assert ordered_horizons((32, 16, 64), "descending") == (64, 32, 16)
    with pytest.raises(ValueError):
        ordered_horizons((16, 16), "ascending")
    with pytest.raises(ValueError):
        ordered_horizons((16, True), "descending")


def test_reverse_order_uses_fresh_indexes_and_keeps_m_bound_to_each_horizon() -> None:
    rows = cold_rows("test", _Term, (16, 32, 64), order="descending")
    assert [row.horizon for row in rows] == [64, 32, 16]
    assert [row.order_index for row in rows] == [0, 1, 2]
    assert all(
        row.new_canonical_field_images_published == row.index_bits for row in rows
    )


def test_reused_ledger_is_rejected_instead_of_reported_as_cold() -> None:
    shared = object()
    with pytest.raises(AssertionError, match="reused an index ledger"):
        cold_rows("test", lambda n: _Term(n, shared), (16, 32), order="ascending")


def test_unsupported_execution_is_not_reported_as_zero_growth() -> None:
    from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError

    class _RejectedTerm(_Term):
        def digit(self, position: int) -> int:
            del position
            raise UnsupportedInterfaceError("certified bridge unavailable")

    result = cold_measurement("test", _RejectedTerm, (16, 32), order="ascending")
    assert result["status"] == "unavailable"
    assert result["measurements_complete"] is False
    assert result["rows"] == []
    assert result["rejection_type"] == "UnsupportedInterfaceError"


@pytest.mark.validation  # Real reverse/Collatz N=16,32 scaling workloads.
def test_public_probe_reports_available_execution_but_keeps_scaling_red() -> None:
    from devtools.benchmarks.field_image_growth_probe import run_probe

    result = run_probe("ascending", horizons=(16, 32))
    assert result["status"] == "RED"
    assert result["measurements_complete"] is True
    assert result["logarithmic_execution_claim"] is False
    assert result["successor_closure_proved"] is False
    families = object_record(object_record(result["orders"])["ascending"])
    for value in (families["reverse"], families["collatz"]):
        family = object_record(value)
        assert family["status"] == "RED"
        assert family["measurements_complete"] is True
        assert family["rows"]
        assert "higher_interface_work_exceeds_doubling_envelope" in text_values(
            family["release_blockers"]
        )
        assert family["successor_closure_proved"] is False
