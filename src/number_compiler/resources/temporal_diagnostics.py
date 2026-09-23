"""Schema-eight observations of temporal construction and demand work.

Every nullable count has one meaning: ``None`` means its instrumented owner was
not observed.  A measured zero is an integer zero.  The lanes deliberately do
not add counters with different meanings or use cache hits as construction.
"""

from __future__ import annotations

import sys
from collections.abc import Mapping
from dataclasses import dataclass, replace

from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class TemporalReuseLane:
    """One owner's requests, reuse and publications in their original units."""

    requests: int | None = None
    attempts: int | None = None
    exact_hits: int | None = None
    transported_hits: int | None = None
    misses: int | None = None
    publications: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalConstruction:
    """Scheduler work; composite application is not source-discovery work."""

    postorder_frames: int | None = None
    primitive_applications: int | None = None
    chronological_compositions: int | None = None
    composite_applications: int | None = None
    demanded_composite_applications: int | None = None
    source_image_publications: int | None = None
    source_image_adapter_registrations: int | None = None
    arithmetic_result_publications: int | None = None
    bootstrap_admission_steps: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalStreamDemand:
    """Output emission measurements, kept distinct from jump construction."""

    requests: int | None = None
    node_visits: int | None = None
    emitted: int | None = None
    boundary_evaluations: int | None = None
    frame_peak: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalDemand:
    """Term query counts; absent exact counters are not inferred from output."""

    point_requests: int | None = None
    length_requests: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalObservations:
    """Family observation and forbidden replay work, in original units."""

    arithmetic_returns: int | None = None
    arithmetic_result_validation_blocks: int | None = None
    arithmetic_result_validation_reconstructions: int | None = None
    arithmetic_result_validation_operand_bits: int | None = None
    mahler_source_composed_image_reads: int | None = None
    mahler_associated_action_demands: int | None = None
    physical_roof_evaluations: int | None = None
    query_observer_reuses: int | None = None
    higher_concrete_operation_evaluations: int | None = None
    higher_action_continuation_requests: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalFamilyWork:
    """One pinned dyadic law's finite source-discovery measurements."""

    counter_prefix: str
    action_requests: int | None
    action_hits: int | None
    action_misses: int | None
    action_publications: int
    macro_requests: int | None
    bounded_base_steps: int | None
    macro_compositions: int | None
    operand_bits: tuple[tuple[str, int], ...]


@dataclass(frozen=True, slots=True)
class TemporalResources:
    """Whole-ledger retention; these counts are never attributed to one lane."""

    entries: int | None = None
    nodes: int | None = None
    peak_entries: int | None = None
    peak_nodes: int | None = None
    audit_complete: bool | None = None
    accounting_mismatch: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalReportingWork:
    """Measured reporting traversal, separate from computational work."""

    captured_counter_items: int | None = None
    captured_mapping_bytes: int | None = None
    projected_counter_items: int | None = None
    inspected_inventory_rows: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalExecutionDiagnostics:
    """Compact schema-eight view beside the preserved raw work counters."""

    schema_version: int = 8
    action: TemporalReuseLane = TemporalReuseLane()
    application: TemporalReuseLane = TemporalReuseLane()
    projection: TemporalReuseLane = TemporalReuseLane()
    construction: TemporalConstruction = TemporalConstruction()
    demand: TemporalDemand = TemporalDemand()
    stream: TemporalStreamDemand = TemporalStreamDemand()
    observations: TemporalObservations = TemporalObservations()
    family_work: tuple[TemporalFamilyWork, ...] = ()
    resources: TemporalResources = TemporalResources()
    reporting: TemporalReportingWork = TemporalReportingWork()


_DYADIC_PREFIXES = (
    "antihydra_arithmetic",
    "collatz_physical",
    "dyadic_return",
)


def _count(counters: Mapping[str, int], key: str) -> int | None:
    value = counters.get(key)
    if value is None:
        return None
    if type(value) is not int or value < 0:
        raise ValueError(f"temporal counter {key} is not a nonnegative integer")
    return value


def collect_temporal_diagnostics(
    counters: Mapping[str, int],
    *,
    entries: int,
    nodes: int,
    peak_entries: int,
    peak_nodes: int,
    audit_complete: bool,
    accounting_mismatch: int | None,
) -> TemporalExecutionDiagnostics:
    """Project exactly one immutable ledger snapshot without evaluating actions."""
    operand_bits: dict[str, list[tuple[str, int]]] = {
        prefix: [] for prefix in _DYADIC_PREFIXES
    }
    for name, value in counters.items():
        if type(value) is not int or value < 0:
            raise ValueError("temporal diagnostics require exact nonnegative counters")
        if name.endswith("operand_bits"):
            for prefix in _DYADIC_PREFIXES:
                if name.startswith(f"{prefix}_"):
                    operand_bits[prefix].append((name, value))
                    break
    if any(
        type(value) is not int or value < 0
        for value in (entries, nodes, peak_entries, peak_nodes)
    ):
        raise ValueError("temporal diagnostics require exact resource counts")
    if accounting_mismatch is not None and (
        type(accounting_mismatch) is not int or accounting_mismatch < 0
    ):
        raise ValueError("temporal diagnostics require exact accounting counts")
    if type(audit_complete) is not bool:
        raise TypeError("temporal audit status must be Boolean")
    if audit_complete and accounting_mismatch is None:
        raise ValueError("completed audit requires an accounting measurement")

    # Source-image publication includes origins and applications.  They are
    # disjoint, so subtraction is exact; projection publication has its own
    # owner and is never included here.
    source_publications = _count(counters, "source_image_publications")
    origin_publications = _count(counters, "source_image_origin_publications")
    application_publications = _count(counters, "source_image_application_publications")
    if (
        source_publications is not None
        and origin_publications is not None
        and application_publications is not None
        and application_publications + origin_publications != source_publications
    ):
        raise ValueError("source-image publication categories do not reconcile")

    families: list[TemporalFamilyWork] = []
    for prefix in _DYADIC_PREFIXES:
        enabled = f"{prefix}_action_publications" in counters
        if not enabled:
            continue

        family_bits = tuple(sorted(operand_bits[prefix]))
        families.append(
            TemporalFamilyWork(
                prefix,
                _count(counters, f"{prefix}_action_requests"),
                _count(counters, f"{prefix}_action_hits"),
                _count(counters, f"{prefix}_action_misses"),
                counters[f"{prefix}_action_publications"],
                _count(counters, f"{prefix}_macro_requests"),
                _count(counters, f"{prefix}_macro_bounded_base_steps"),
                _count(counters, f"{prefix}_macro_compositions"),
                family_bits,
            )
        )

    sole_family = families[0] if len(families) == 1 else None
    # Until the executable bootstrap checker emits this count, its scope is
    # unavailable.  Existing bounded-base steps do not imply admissibility.
    bootstrap = counters.get("temporal_bootstrap_admission_steps")
    if bootstrap is not None and (type(bootstrap) is not int or bootstrap < 0):
        raise ValueError("temporal bootstrap scope is invalid")
    return TemporalExecutionDiagnostics(
        action=TemporalReuseLane(
            requests=None if sole_family is None else sole_family.action_requests,
            exact_hits=None if sole_family is None else sole_family.action_hits,
            misses=None if sole_family is None else sole_family.action_misses,
            publications=(
                None if sole_family is None else sole_family.action_publications
            ),
        ),
        application=TemporalReuseLane(
            requests=_count(counters, "source_image_application_requests"),
            attempts=_count(counters, "source_image_application_attempts"),
            exact_hits=_count(counters, "source_image_application_hits"),
            transported_hits=_count(counters, "source_image_relative_transfer_hits"),
            misses=_count(counters, "source_image_application_misses"),
            publications=application_publications,
        ),
        projection=TemporalReuseLane(
            requests=_count(counters, "source_image_projection_requests"),
            exact_hits=_count(counters, "source_image_projection_hits"),
            misses=_count(counters, "source_image_projection_misses"),
            publications=_count(counters, "source_image_projection_publications"),
        ),
        construction=TemporalConstruction(
            postorder_frames=_count(counters, "source_image_postorder_frames"),
            primitive_applications=_count(
                counters, "source_image_primitive_applications"
            ),
            chronological_compositions=_count(
                counters, "source_image_chronological_compositions"
            ),
            composite_applications=_count(
                counters, "source_image_composite_applications"
            ),
            demanded_composite_applications=_count(
                counters, "source_image_demanded_composite_applications"
            ),
            source_image_publications=source_publications,
            source_image_adapter_registrations=_count(
                counters, "source_image_adapter_registrations"
            ),
            arithmetic_result_publications=_count(
                counters, "arithmetic_result_publications"
            ),
            bootstrap_admission_steps=bootstrap,
        ),
        demand=TemporalDemand(
            point_requests=_count(counters, "temporal_point_requests"),
            length_requests=_count(counters, "temporal_length_requests"),
        ),
        stream=TemporalStreamDemand(
            requests=_count(counters, "recursive_output_stream_requests"),
            node_visits=_count(counters, "recursive_output_stream_node_visits"),
            emitted=_count(counters, "recursive_output_stream_emitted_digits"),
            boundary_evaluations=_count(
                counters, "recursive_output_stream_boundary_evaluations"
            ),
            frame_peak=_count(counters, "recursive_output_stream_frame_peak"),
        ),
        observations=TemporalObservations(
            arithmetic_returns=_count(counters, "arithmetic_returns"),
            arithmetic_result_validation_blocks=_count(
                counters, "arithmetic_result_validation_blocks"
            ),
            arithmetic_result_validation_reconstructions=_count(
                counters, "arithmetic_result_validation_reconstructions"
            ),
            arithmetic_result_validation_operand_bits=_count(
                counters, "arithmetic_result_validation_operand_bits"
            ),
            mahler_source_composed_image_reads=_count(
                counters, "mahler_source_composed_image_reads"
            ),
            mahler_associated_action_demands=_count(
                counters, "mahler_associated_action_demands"
            ),
            physical_roof_evaluations=_count(counters, "physical_roof_evaluations"),
            query_observer_reuses=_count(counters, "query_observer_reuses"),
            higher_concrete_operation_evaluations=_count(
                counters, "higher_concrete_operation_evaluations"
            ),
            higher_action_continuation_requests=_count(
                counters, "higher_action_continuation_requests"
            ),
        ),
        family_work=tuple(families),
        resources=TemporalResources(
            entries,
            nodes,
            peak_entries,
            peak_nodes,
            audit_complete,
            accounting_mismatch,
        ),
        reporting=TemporalReportingWork(projected_counter_items=len(counters)),
    )


def collect_temporal_diagnostics_snapshot(
    ledger: ResourceLedger,
) -> TemporalExecutionDiagnostics:
    """Capture CLI diagnostics without a semantic audit or endpoint demand.

    The term/query owner is serial. Copying the scalar work counters detaches
    them from later demands; retained resources come from the ledger's scalar
    totals. Inventory callbacks and their potentially expensive payload walks
    are intentionally reserved for the explicit full-audit collector.
    """
    if type(ledger) is not ResourceLedger:
        raise TypeError("temporal diagnostics require one resource ledger")
    counters = dict(ledger.counters)
    report = collect_temporal_diagnostics(
        counters,
        entries=ledger.entries,
        nodes=ledger.nodes,
        peak_entries=ledger.peak_entries,
        peak_nodes=ledger.peak_nodes,
        audit_complete=False,
        accounting_mismatch=None,
    )
    return replace(
        report,
        reporting=TemporalReportingWork(
            captured_counter_items=len(counters),
            captured_mapping_bytes=sys.getsizeof(counters),
            projected_counter_items=len(counters),
            inspected_inventory_rows=0,
        ),
    )
