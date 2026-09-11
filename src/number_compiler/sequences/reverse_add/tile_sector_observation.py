"""Authenticated decimal reverse/add sector observations from tile execution."""

from __future__ import annotations

from number_compiler.arithmetic.carry.reverse_sector_transfer import (
    ReverseCarrySectorTransfer,
    ReverseForcingResidues,
)
from number_compiler.arithmetic.carry.carry_monoid import apply_carry_fn
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_application_authority import (
    application_source,
)
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
    primitive_interface_payload,
)
from number_compiler.hashlife.execution.tile_causal_results import PrimitiveCausalPorts
from number_compiler.hashlife.execution.tile_scheduler import TileApplication
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.hashlife.interfaces.tile_reverse_sector_functions import (
    _aligned_reverse_interval_forcing,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_region_memo import normalize_cached_region
from number_compiler.hashlife.tiles.reverse_threshold_summary import (
    reverse_current_growth,
)
from number_compiler.hashlife.tiles.tiles import TileID, TileLease
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.sequences.reverse_add.frobenius_sectors import (
    ReverseFrobeniusSectorProduct,
)


def _primitive_branch(
    adapter: PrimitiveTileKernelAdapter,
    action: FieldCellActionID,
) -> tuple[FieldCellActionID, int]:
    """Return one primitive witness while visiting at most a logarithmic spine."""
    record = adapter._action(action)
    repetitions = record.repetitions
    if not record.homogeneous:
        raise ValueError("reverse sector observation requires a homogeneous action")
    kernel, signature = record.kernel, record.signature
    current = action
    visits = 1
    while record.children is not None:
        left, right = record.children
        left_record, right_record = adapter._action(left), adapter._action(right)
        if (
            not left_record.homogeneous
            or not right_record.homogeneous
            or left_record.kernel != kernel
            or right_record.kernel != kernel
            or left_record.signature != signature
            or right_record.signature != signature
        ):
            raise ValueError("reverse sector action contains another temporal family")
        current, record = (
            (left, left_record)
            if left_record.repetitions <= right_record.repetitions
            else (right, right_record)
        )
        visits += 1
    if record.repetitions != 1 or record.kernel != kernel:
        raise ValueError("reverse sector action has no primitive branch witness")
    if visits > repetitions.bit_length() + 1:
        raise ValueError("reverse sector action has an unbalanced primitive spine")
    adapter.ledger.bump("reverse_sector_product_action_spine_visits", visits)
    return current, repetitions


def _sector_summary(
    adapter: PrimitiveTileKernelAdapter,
    interface: LocalInterfaceID,
) -> ReverseCarrySectorTransfer:
    if type(interface) is not LocalInterfaceID:
        raise TypeError("reverse sector observation requires a local interface ID")
    sectors = adapter.quotients.resolve(interface).components.reverse_sectors
    if type(sectors) is not ReverseCarrySectorTransfer:
        raise ValueError("reverse interface has no certified carry-sector product")
    sectors.__post_init__()
    return sectors


def _source_is_symmetric(
    application: TileApplication,
    source: TileID,
    active_width: int,
) -> bool:
    if type(source) is not TileID:
        raise TypeError("reverse sector source requires a canonical tile ID")
    scheduler = application.scheduler
    forward, forward_lease = normalize_cached_region(
        scheduler.results,
        BoundaryTileView(source, 0, active_width),
        dependencies=scheduler._causal_dependencies,
        application=application.identity,
    )
    try:
        reflected, reflected_lease = normalize_cached_region(
            scheduler.results,
            BoundaryTileView(source, 0, active_width, 1),
            dependencies=scheduler._causal_dependencies,
            application=application.identity,
        )
        try:
            return forward.tile == reflected.tile
        finally:
            reflected_lease.close()
    finally:
        forward_lease.close()


def observe_reverse_sector_product(
    application: TileApplication,
) -> ReverseFrobeniusSectorProduct:
    """Observe the executed decimal affine sector product without an endpoint.

    The issued application supplies both the exact original pair field and the
    final primitive input interface.  Mirror symmetry is proved from canonical
    clipped source tiles; no caller flag, future endpoint, or event itinerary is
    accepted as evidence.
    """
    if type(application) is not TileApplication:
        raise TypeError("reverse sector observation requires a tile application")
    source = application_source(application)
    scheduler = application.scheduler
    adapter = scheduler.adapter
    if type(adapter) is not PrimitiveTileKernelAdapter:
        raise TypeError(
            "reverse sector observation requires the primitive tile runtime"
        )
    if scheduler.results.action_authority is not adapter:
        raise ValueError("reverse sector application has another action authority")
    adapter.validate_action(application.action)
    adapter.validate_input(application.action, source)
    adapter.validate_wiring(application.action, application.wiring)
    if application.ports != adapter.initial_ports(application.action):
        raise ValueError("reverse sector observation requires initial boundary ports")
    record = adapter._action(application.action)
    kernel = adapter.kernels.kernel(record.kernel)
    if (
        not record.homogeneous
        or type(kernel.effect) is not BaseBlockEffect
        or kernel.base != 10
        or kernel.effect.base != 10
    ):
        raise ValueError("reverse sector observation requires the decimal pair kernel")

    ledger = scheduler.ledger
    ledger.bump("reverse_sector_product_observation_requests")
    try:
        primitive, steps = _primitive_branch(adapter, application.action)
        plan = record.reverse_frobenius
        source_dead = plan is not None and plan.all_source_sectors_annihilated
        initial = None
        if source_dead:
            # Validate the contiguous active prefix through the existing carry
            # monoid.  First/last-active metadata alone cannot exclude blank gaps.
            active_width = scheduler.results.reverse_threshold_summary(
                source, 10
            ).length
        else:
            initial_interface = adapter._compile_interface(
                primitive,
                source,
                adapter.wiring(primitive),
            )
            initial = _sector_summary(adapter, initial_interface)
            active_width = initial.active_width
        source_record = scheduler.tiles.resolve(source)
        if (
            not active_width
            or (initial is not None and initial.width != source_record.width)
            or active_width + steps > source_record.width
            or source_record.first_active != 0
            or source_record.last_active != active_width - 1
            or source_record.extent != active_width
        ):
            raise ValueError(
                "reverse sector observation requires one full active prefix and padding"
            )
        if not _source_is_symmetric(application, source, active_width):
            raise ValueError(
                "reverse sector observation requires a symmetric pair field"
            )

        with adapter.quotients.closed_workspace.scope("parent"):
            if steps == 1:
                if initial is None:
                    raise ValueError("primitive source omitted its sector observation")
                # A primitive pair transition's complete bounded affine product
                # is already determined by the authenticated source transfer.
                # Avoid constructing the successor interface merely to recover
                # the same carry forcing at the temporal endpoint.
                product = ReverseFrobeniusSectorProduct.from_carry_transfer(initial)
            else:
                final_payload = application.interface()
                if (
                    final_payload.incoming_ports != application.ports
                    or final_payload.level != source_record.level
                ):
                    raise ValueError(
                        "reverse sector interface changed its occurrence binding"
                    )
                final_input = _sector_summary(adapter, final_payload.interface)
                if final_input.width != source_record.width:
                    raise ValueError(
                        "reverse sector interface changed its padded field width"
                    )
                if source_dead and plan is not None:
                    product = ReverseFrobeniusSectorProduct.from_annihilated_source(
                        active_width, final_input, plan
                    )
                    ledger.bump("reverse_sector_product_source_elisions")
                else:
                    if initial is None:
                        raise ValueError("live source omitted its sector observation")
                    product = ReverseFrobeniusSectorProduct.from_endpoint_sectors(
                        initial,
                        final_input,
                        steps,
                    )
    except BaseException:
        ledger.bump("reverse_sector_product_observation_failures")
        raise
    ledger.bump("reverse_sector_product_observation_evaluations")
    ledger.bump("reverse_sector_product_arithmetic_evaluations")
    ledger.bump("reverse_sector_product_sector_evaluations", len(product.sectors))
    return product


def _observe_reverse_interval_forcing(
    application: TileApplication,
    origin: int,
    extent: int,
) -> ReverseForcingResidues:
    """Observe one aligned primitive decimal successor interval without output.

    The interval is dyadic and lies in the active source field.  Growth and all
    carry inputs are derived from canonical source regions.  The growth branch
    excludes its two special endpoint cells, whose distinct law is not hidden
    behind this bounded observation.
    """
    if type(application) is not TileApplication:
        raise TypeError("reverse interval forcing requires a tile application")
    if type(origin) is not int or type(extent) is not int:
        raise TypeError("reverse interval forcing geometry requires exact integers")
    if extent < 1 or extent & (extent - 1):
        raise ValueError("reverse interval forcing requires a positive dyadic extent")
    source = application_source(application)
    scheduler = application.scheduler
    adapter = scheduler.adapter
    if type(adapter) is not PrimitiveTileKernelAdapter:
        raise TypeError("reverse interval forcing requires the primitive tile runtime")
    if scheduler.results.action_authority is not adapter:
        raise ValueError("reverse interval application has another action authority")
    adapter.validate_action(application.action)
    adapter.validate_input(application.action, source)
    adapter.validate_wiring(application.action, application.wiring)
    record = adapter._action(application.action)
    kernel = adapter.kernels.kernel(record.kernel)
    if (
        record.children is not None
        or not record.homogeneous
        or type(kernel.effect) is not BaseBlockEffect
        or kernel.base != 10
        or application.ports != adapter.initial_ports(application.action)
    ):
        raise ValueError("reverse interval forcing requires one decimal pair action")
    source_node = scheduler.tiles.resolve(source)
    active_width = scheduler.results.reverse_threshold_summary(source, 10).length
    if (
        source_node.first_active != 0
        or source_node.last_active != active_width - 1
        or source_node.extent != active_width
        or not _source_is_symmetric(application, source, active_width)
    ):
        raise ValueError("reverse interval forcing requires a symmetric active prefix")
    growth = reverse_current_growth(scheduler.results, source, 10)
    if origin < growth or origin + extent > active_width:
        raise ValueError("reverse interval includes a special endpoint or padding")

    def region(start: int) -> tuple[BoundaryTileView, TileLease]:
        return normalize_cached_region(
            scheduler.results,
            BoundaryTileView(
                source,
                start,
                extent,
                source_offset=start,
            ),
            dependencies=scheduler._causal_dependencies,
            application=application.identity,
        )

    def payload(start: int) -> tuple[CausalInterfacePayload, TileLease]:
        view, lease = region(start)
        try:
            if scheduler.tiles.resolve(view.tile).width != extent:
                raise ValueError(
                    "reverse interval did not normalize to one dyadic tile"
                )
            ports = adapter.initial_ports(application.action)
            observed = primitive_interface_payload(
                scheduler.results,
                application.action,
                view.tile,
                PrimitiveCausalPorts(*ports),
                application.wiring,
                TemporalCocycle(),
            )
            return observed, lease
        except BaseException:
            lease.close()
            raise

    def carry_at(boundary: int) -> int:
        if boundary == 0:
            return 0
        prefix, lease = normalize_cached_region(
            scheduler.results,
            BoundaryTileView(source, 0, boundary),
            dependencies=scheduler._causal_dependencies,
            application=application.identity,
        )
        try:
            interface = adapter._compile_interface(
                application.action,
                prefix.tile,
                application.wiring,
            )
            return apply_carry_fn(_sector_summary(adapter, interface).carry, 0)
        finally:
            lease.close()

    reflected_origin = active_width - origin - extent + growth
    primary, primary_lease = payload(origin)
    try:
        reflected, reflected_lease = payload(reflected_origin)
        try:
            predecessor: CausalInterfacePayload | None = None
            predecessor_lease: TileLease | None = None
            if growth:
                predecessor, predecessor_lease = payload(origin - 1)
            try:
                return _aligned_reverse_interval_forcing(
                    adapter,
                    primary,
                    reflected,
                    incoming=carry_at(origin),
                    reflected_incoming=carry_at(reflected_origin),
                    growth=growth,
                    predecessor=predecessor,
                )
            finally:
                if predecessor_lease is not None:
                    predecessor_lease.close()
        finally:
            reflected_lease.close()
    finally:
        primary_lease.close()


def observe_reverse_interval_forcing(
    application: TileApplication,
    origin: int,
    extent: int,
) -> ReverseForcingResidues:
    """Observe and account for one authenticated local forcing interval."""
    if type(application) is not TileApplication:
        raise TypeError("reverse interval forcing requires a tile application")
    ledger = application.scheduler.ledger
    ledger.bump("reverse_interval_observation_requests")
    try:
        observed = _observe_reverse_interval_forcing(application, origin, extent)
    except BaseException:
        ledger.bump("reverse_interval_observation_failures")
        raise
    ledger.bump("reverse_interval_observation_evaluations")
    return observed


__all__ = [
    "observe_reverse_interval_forcing",
    "observe_reverse_sector_product",
]
