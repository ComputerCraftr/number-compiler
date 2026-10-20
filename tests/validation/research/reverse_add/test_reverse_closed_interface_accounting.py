"""Closed reverse interfaces retain bounded records with read-only accounting."""

from __future__ import annotations

from dataclasses import replace
from typing import Never

import pytest

from devtools.experiments.reverse_add.tile_sector_observation import (
    observe_reverse_sector_product,
)
from number_compiler.arithmetic.carry.reverse_port_functions import ReversePortFunction
from number_compiler.arithmetic.carry.reverse_sector_transfer import (
    ReverseCarrySectorTransfer,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.interfaces.diamond_quotient import (
    DiamondQuotientArena,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    QuotientRecord,
)
from number_compiler.hashlife.observation.tile_projection import build_tile_projection
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.payload_audit import audit_registered_payloads


def forbidden(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("reporting evaluated a closed reverse interface")


def test_reverse_closed_interface_slots_are_actual_and_reporting_is_read_only(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=8, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as projection:
        projection.validated_application().interface()
        product = observe_reverse_sector_product(projection.validated_application())
        assert product.steps == 1
        roots = tuple(ledger.iter_execution_roots())
        arenas = tuple(root for root in roots if type(root) is DiamondQuotientArena)
        shared_fixture = False
        for arena in arenas:
            for record in tuple(arena.audit_snapshot().nodes.values()):
                if record.components.reverse_sectors is None:
                    continue
                stripped = QuotientRecord(
                    record.signature,
                    replace(record.components, reverse_sectors=None),
                )
                if stripped not in arena.audit_snapshot().keys:
                    arena.intern(stripped.signature, stripped.components)
                    shared_fixture = True
                    break
            if shared_fixture:
                break
        assert shared_fixture
        functions: list[ReversePortFunction] = []
        for arena in arenas:
            for record in arena.audit_snapshot().nodes.values():
                seen: set[int] = set()
                for component in record.components.functions():
                    if (
                        type(component) is ReversePortFunction
                        and id(component) not in seen
                    ):
                        seen.add(id(component))
                        functions.append(component)
        sectors = tuple(
            record.components.reverse_sectors
            for arena in arenas
            for record in arena.audit_snapshot().nodes.values()
            if type(record.components.reverse_sectors) is ReverseCarrySectorTransfer
        )
        assert functions and sectors
        expected_coefficients = sum(
            component.retained_coefficient_slots for component in functions
        )
        expected_limbs = sum(component.retained_limb_slots for component in functions)
        expected_sectors = sum(summary.retained_slots() for summary in sectors)
        unique_functions = {id(component): component for component in functions}
        unique_sectors = {id(summary): summary for summary in sectors}
        before = ledger.snapshot()
        monkeypatch.setattr(ReversePortFunction, "evaluate", forbidden)
        monkeypatch.setattr(ReverseCarrySectorTransfer, "forcing", forbidden)
        report = collect_ledger_metrics(ledger)
        assert ledger.snapshot() == before
        assert report.reverse_port_retained_coefficient_slots == expected_coefficients
        assert report.reverse_port_retained_limb_slots == expected_limbs
        assert report.reverse_sector_retained_slots == expected_sectors
        assert report.reverse_sector_retained_slots % 76 == 0
        assert report.reverse_port_unique_live_function_objects == len(unique_functions)
        assert report.reverse_port_unique_live_coefficient_slots == sum(
            component.retained_coefficient_slots
            for component in unique_functions.values()
        )
        assert report.reverse_port_unique_live_limb_slots == sum(
            component.retained_limb_slots for component in unique_functions.values()
        )
        assert report.reverse_sector_unique_live_objects == len(unique_sectors)
        assert report.reverse_sector_unique_live_slots == sum(
            summary.retained_slots() for summary in unique_sectors.values()
        )
        assert len(unique_functions) < len(functions)
        assert report.reverse_port_unique_live_coefficient_slots < (
            report.reverse_port_retained_coefficient_slots
        )
        assert report.reverse_sector_compose_evaluations > 0
        assert (
            report.reverse_sector_compose_requests
            == report.reverse_sector_compose_evaluations
            + report.reverse_sector_compose_failures
        )
        assert (
            report.reverse_sector_component_outputs
            == 75 * report.reverse_sector_compose_evaluations
        )
        assert (
            report.reverse_sector_ring_scalar_operations
            == 150 * report.reverse_sector_compose_evaluations
        )
        assert (
            report.reverse_sector_carry_input_evaluations
            == 2 * report.reverse_sector_compose_evaluations
        )
        assert report.reverse_sector_product_observation_requests == 1
        assert report.reverse_sector_product_observation_evaluations == 1
        assert report.reverse_sector_product_observation_failures == 0
        assert report.reverse_sector_product_sector_evaluations == 4
        assert report.reverse_sector_product_source_elisions == 0
        audit = audit_registered_payloads(ledger)
        assert (
            audit.forbidden_future_payloads,
            audit.unbounded_future_integers,
            audit.unknown_payloads,
        ) == (0, 0, 0)
