"""Point-lazy execution of output-complete programs over immutable source geometry."""

from __future__ import annotations

from collections.abc import Iterator, Mapping, Sequence
from dataclasses import dataclass
from types import MappingProxyType
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockEffect
from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
    source_reads_only,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaToken,
    ExactSource,
    LoweringCapability,
)
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.contracts.temporal_family import (
    TemporalFamilyCertificate,
    issue_certificate,
)
from number_compiler.arithmetic.fields.dyadic_tile import DyadicTile
from number_compiler.hashlife.actions.lazy_compiler import (
    LazyCompiler,
    UnsupportedInterfaceError,
)
from number_compiler.hashlife.execution.bounded_application import (
    build_bounded_application,
)
from number_compiler.hashlife.execution.tile_execution_adapter import FamilyTileHooks
from number_compiler.hashlife.observation.tile_projection import (
    LazyProjection,
    build_tile_projection,
    lower_fixed_tile_compatibility,
    validate_fixed_tile_compatibility,
)
from number_compiler.projection.microblock_cache import (
    ExactMicroblock,
    MicroblockCache,
    MicroblockKey,
)
from number_compiler.projection.point_response import PointResponseRegister
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.arithmetic.polynomials.twisted_observer import (
        TwistedCylinderProjection,
    )
    from number_compiler.hashlife.tiles.ordered_boolean_support import (
        OrderedBooleanSupport,
    )
    from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
    from number_compiler.resources.hashlife_behavior_metrics import (
        HashLifeBehaviorMetrics,
    )
    from number_compiler.resources.metric_records import (
        HashLifeProjectionMetrics,
    )


@dataclass(frozen=True, slots=True)
class HashLifeBlockIndexAuditSnapshot:
    """Detached metric inputs captured by the index that owns them."""

    effect_metric_baseline: Mapping[str, int]
    certificate: TemporalFamilyCertificate | None
    lazy_application: LazyProjection
    point_queries: int
    direct_powered_point_queries: int
    canonical_tiles_at_build: int
    canonical_tile_roots: int
    seed_payload_tile_nodes: int
    padded_root_tile_nodes: int
    retained_spatial_tile_nodes: int
    application_spatial_tile_nodes: int
    powered_operator_nodes: int


class HashLifeBlockIndex:
    """One compiler, source, lazy application and resource ownership scope."""

    _lazy_application: LazyProjection

    def __init__(
        self,
        effect: BlockEffect,
        source: Sequence[int],
        *,
        logical_length: int,
        max_tile_nodes: int | None = None,
        max_cache_entries: int | None = None,
        certificate: TemporalFamilyCertificate | None = None,
        ledger: ResourceLedger | None = None,
        compiler: LazyCompiler | None = None,
        source_construction: OriginalSourceConstruction | None = None,
        microblocks: MicroblockCache | None = None,
        family_hooks: FamilyTileHooks | None = None,
    ) -> None:
        logical_length = require_integer(logical_length, "logical source length", 0)
        values = tuple(source)
        if any(type(value) is not int for value in values):
            raise TypeError("original source symbols must be integers")
        if not values or any(value < 0 or value >= effect.blank for value in values):
            raise ValueError("invalid source alphabet")
        if logical_length < len(values):
            raise ValueError("source exceeds logical extent")
        original = ExactSource(
            values,
            effect.base,
            blank=effect.blank,
            extent=logical_length,
            alphabet_size=effect.blank,
        )
        if source_construction is not None:
            OriginalSourceConstruction.validate_source(source_construction, original)
        self._certificate = certificate
        if family_hooks is not None and type(family_hooks) is not FamilyTileHooks:
            raise TypeError("HashLife index requires canonical family hooks")
        if compiler is not None:
            compiler_hooks = compiler.family_hooks
            if family_hooks is None:
                family_hooks = compiler_hooks
            elif compiler_hooks is not None and compiler_hooks is not family_hooks:
                raise ValueError("compiler is already bound to another family adapter")
        self._family_hooks = family_hooks
        # Authenticate a recognized compatibility artifact before this index
        # creates or registers any ledger-owned runtime object.
        validate_fixed_tile_compatibility(effect, family_hooks)
        if certificate is not None:
            certificate.validate(effect)
        self._ledger = (
            ResourceLedger(max_tile_nodes, max_cache_entries)
            if ledger is None
            else ledger
        )
        if compiler is not None and compiler.ledger is not self._ledger:
            raise ValueError("compiler belongs to a different index ledger")
        if ledger is not None:
            ledger.tighten_limits(max_tile_nodes, max_cache_entries)
        # Every nonempty index needs a source node as well as an entry.
        # Reject an impossible index before an entry-only compiler cache fills.
        self._ledger.check_capacity(entries=1, nodes=1)
        self._ledger.register_execution_root(self)
        self._compiler = (
            LazyCompiler(self._ledger, family_hooks=family_hooks)
            if compiler is None
            else compiler
        )
        if compiler is not None and family_hooks is not None:
            self._compiler.bind_family_hooks(family_hooks)
        effect = lower_fixed_tile_compatibility(
            effect,
            self._compiler,
            family_hooks=family_hooks,
        )
        self._microblocks = (
            MicroblockCache.shared(
                self._ledger,
                self._compiler.token,
                self._compiler.resolve,
            )
            if microblocks is None
            else microblocks
        )
        if self._microblocks.ledger is not self._ledger:
            raise ValueError("microblock cache belongs to a different index ledger")
        if compiler is None:
            effect = self._compiler.import_effect(effect)
            if certificate is not None:
                certificate = issue_certificate(
                    effect,
                    certificate.family,
                    certificate.steps,
                    ledger=self._ledger,
                    family_leaf_counts=(
                        None
                        if family_hooks is None
                        else family_hooks.program_leaf_counts
                    ),
                )
                self._certificate = certificate
        else:
            effect = self._compiler.atom(effect)
        self.effect, self.source, self.logical_length = effect, values, logical_length
        self.program = self._compiler.reference(effect)
        self._effect_metric_baseline = tuple(effect.runtime_stats().items())
        self._source_geometry = SourceGeometry(
            self._ledger,
            original,
            source_construction,
        )
        self.seed_root = self._source_geometry.span(values, effect.blank, len(values))
        self.evaluation_root = self._source_geometry.span(
            values, effect.blank, self.logical_length
        )
        self.root = self.evaluation_root
        bounded = build_bounded_application(
            effect,
            values,
            logical_length=self.logical_length,
            certificate=certificate,
            ledger=self._ledger,
            compiler=self._compiler,
            source_geometry=self._source_geometry,
            microblocks=self._microblocks,
            family_hooks=family_hooks,
        )
        self._bounded_application: LazyProjection | None
        if bounded is None:
            self._bounded_application = None
            self._lazy_application = build_tile_projection(
                effect, self._source_geometry, family_hooks=family_hooks
            )
        elif type(bounded) is LazyProjection:
            self._bounded_application = self._lazy_application = bounded
        else:
            raise UnsupportedInterfaceError(
                "public projection requires the canonical tile executor"
            )
        self._point_response = PointResponseRegister(self._compiler)
        self._point_queries = self._direct_powered_point_queries = 0
        self._lowering_owner = ArenaToken("endpoint-lowering")
        from number_compiler.hashlife.execution.tile_kernel import (
            PrimitiveTileKernelAdapter,
        )

        self._output_symbol_count: int
        self._canonical_tiles_at_build: int
        application = self._lazy_application.validated_application()
        adapter = application.scheduler.adapter
        if type(adapter) is not PrimitiveTileKernelAdapter:
            raise ValueError("point observation requires an admitted output alphabet")
        self._output_symbol_count = application.scheduler.tiles.alphabet(
            adapter.alphabet(application.action)
        ).symbol_count
        self._canonical_tiles_at_build = len(
            self._lazy_application.scheduler.tiles.audit_snapshot().nodes
        )

    @property
    def resource_ledger(self) -> ResourceLedger:
        """Return this index's exact shared resource owner."""
        return self._ledger

    @property
    def _tile_roots(self) -> set[DyadicTile]:
        return {chunk.tile for chunk in self.evaluation_root.chunks}

    @staticmethod
    def _collect_tile_nodes(roots: set[DyadicTile]) -> set[DyadicTile]:
        nodes: set[DyadicTile] = set()
        stack = list(roots)
        while stack:
            node = stack.pop()
            if node in nodes:
                continue
            nodes.add(node)
            if node.left is not None:
                stack.append(node.left)
            if node.right is not None:
                stack.append(node.right)
        return nodes

    def _retained_tile_nodes(self) -> set[DyadicTile]:
        return set(self._source_geometry.nodes.values())

    def _retained_tile_node_count(self) -> int:
        return len(self._source_geometry.nodes)

    def audit_snapshot(self) -> HashLifeBlockIndexAuditSnapshot:
        """Return read-only state needed by resource and behavior reports."""
        seed_nodes = self._collect_tile_nodes(
            {chunk.tile for chunk in self.seed_root.chunks}
        )
        root_nodes = self._collect_tile_nodes(
            {chunk.tile for chunk in self.evaluation_root.chunks}
        )
        retained_nodes = set(self._source_geometry.nodes.values())
        seen: set[int] = set()
        stack: list[object] = [self.effect]
        while stack:
            node = stack.pop()
            if id(node) in seen:
                continue
            seen.add(id(node))
            for name in ("first", "second"):
                child = getattr(node, name, None)
                if child is not None:
                    stack.append(child)
        return HashLifeBlockIndexAuditSnapshot(
            effect_metric_baseline=MappingProxyType(dict(self._effect_metric_baseline)),
            certificate=self._certificate,
            lazy_application=self._lazy_application,
            point_queries=self._point_queries,
            direct_powered_point_queries=self._direct_powered_point_queries,
            canonical_tiles_at_build=self._canonical_tiles_at_build,
            canonical_tile_roots=len(self._tile_roots),
            seed_payload_tile_nodes=len(seed_nodes),
            padded_root_tile_nodes=len(root_nodes),
            retained_spatial_tile_nodes=len(retained_nodes),
            application_spatial_tile_nodes=len(retained_nodes - root_nodes),
            powered_operator_nodes=len(seen),
        )

    @source_reads_only
    def direct_powered_point(self, position: int) -> int:
        """Project one exact scalar through source/program/transfer summaries."""
        position = require_integer(position, "digit coordinate")
        if not 0 <= position < self.logical_length:
            raise IndexError(position)
        # Authenticate the issued application before either scalar cache can
        # answer.  Program ownership alone does not confer source authority.
        self._lazy_application.validated_application().validate_execution()
        self._point_queries += 1
        self._direct_powered_point_queries += 1
        return self._point_response.query(self.program, position, self._point)

    @source_reads_only
    def direct_temporal_cocycle(self) -> TemporalCocycle:
        if type(self._lazy_application) is not LazyProjection:
            raise ValueError("cocycle observation requires its tile application")
        return self._lazy_application.temporal_cocycle()

    @source_reads_only
    def direct_physical_support(self) -> OrderedBooleanSupport:
        if type(self._lazy_application) is not LazyProjection:
            raise ValueError("support observation requires its tile application")
        return self._lazy_application.physical_support()

    @source_reads_only
    def direct_mirror_obstruction(
        self, *, first_width: int = 1
    ) -> TwistedCylinderProjection | None:
        if type(self._lazy_application) is not LazyProjection:
            raise ValueError("mirror observation requires its published application")
        return self._lazy_application.mirror_obstruction(first_width=first_width)

    def _point(self, position: int) -> int:
        """Read or publish one bounded exact point after program authentication."""
        self._lazy_application.validated_application()
        key = MicroblockKey(
            self.program,
            self.effect.base,
            0,
            position,
            "output",
            source_scope=self._source_geometry.token,
        )
        cached = self._microblocks.get(key)
        if cached is not None:
            value = cached.encoded
            if not 0 <= value < self._output_symbol_count:
                raise ValueError("cached point belongs to another alphabet")
            return value
        value = self._lazy_application.point(position)
        if not 0 <= value < self._output_symbol_count:
            raise ValueError("tile point belongs to another alphabet")
        self._microblocks.put(
            key,
            ExactMicroblock(value, max(1, self.effect.blank.bit_length())),
        )
        return value

    @source_reads_only
    def direct_active_width(self) -> int:
        """Find the output extent without constructing an endpoint tape."""
        return self._lazy_application.active_width()

    def iter_direct_points(self, *, reflect_output: bool = False) -> Iterator[int]:
        """Lower requested final points with an explicitly certified mirror policy."""
        from number_compiler.projection.endpoint_lowering import iter_endpoint_digits

        yield from iter_endpoint_digits(
            owner=self._lowering_owner,
            capability=LoweringCapability(self._lowering_owner),
            width=self.direct_active_width(),
            blank=self.effect.blank,
            point=self.direct_powered_point,
            ledger=self._ledger,
            reflect_output=reflect_output,
        )

    def iter_direct_active(self) -> Iterator[int]:
        """Explicit output lowering, separated from the scalar query path."""
        from number_compiler.projection.endpoint_lowering import (
            iter_canonical_endpoint_digits,
        )

        yield from iter_canonical_endpoint_digits(
            self._lazy_application,
            owner=self._lowering_owner,
            capability=LoweringCapability(self._lowering_owner),
        )

    def behavior_metrics(self) -> HashLifeBehaviorMetrics:
        from number_compiler.resources.behavior_metrics import collect_behavior_metrics

        return collect_behavior_metrics(self)

    def metrics(self) -> HashLifeProjectionMetrics:
        from number_compiler.resources.projection_metrics import (
            collect_projection_metrics,
        )

        return collect_projection_metrics(self)


__all__ = ["HashLifeBlockIndex"]
