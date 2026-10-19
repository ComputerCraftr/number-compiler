"""Public lazy projection over canonical source and completed future tiles."""

from __future__ import annotations

from collections.abc import Generator
from typing import TYPE_CHECKING, Self

from number_compiler.arithmetic.contracts.block_effect import BlockEffect
from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
    source_reads_only,
)
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_execution_adapter import (
    FamilyTileHooks,
    FinitePairTransfer,
    FinitePairTransferFactory,
    is_finite_pair_transfer,
    is_finite_pair_transfer_factory,
)
from number_compiler.hashlife.execution.tile_scheduler import (
    TileApplication,
    TileScheduler,
)
from number_compiler.hashlife.tiles.tile_ports import ResultWiring
from number_compiler.hashlife.tiles.tiles import (
    TileAlphabetID,
    TileArena,
    TileID,
    TileLease,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_observation as _observation_keys,
)
from number_compiler.resources.stores import LedgerDict, LedgerList

if TYPE_CHECKING:
    from number_compiler.arithmetic.polynomials.twisted_observer import (
        TwistedCylinderProjection,
    )
    from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
    from number_compiler.hashlife.observation.tile_cylinder import TileCylinderWorkspace
    from number_compiler.hashlife.tiles.ordered_boolean_support import (
        OrderedBooleanSupport,
    )
    from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
    from number_compiler.resources.tile_runtime_audit_contracts import (
        LazyProjectionAuditSnapshot,
    )


def _close_all(values: list[tuple[int, TileLease]]) -> None:
    while values:
        values.pop()[1].close()


def _append_block(
    tiles: TileArena,
    blocks: list[tuple[int, TileLease]],
    start: int,
    block: TileLease,
) -> None:
    """Append and iteratively merge one aligned dyadic source block."""
    current_start, current = start, block
    try:
        while blocks:
            previous_start, previous = blocks[-1]
            previous_record = tiles.resolve(previous.tile)
            current_record = tiles.resolve(current.tile)
            if (
                previous_start + previous_record.width != current_start
                or previous_record.level != current_record.level
                or previous_start % (previous_record.width * 2)
            ):
                break
            parent = tiles.join(previous.tile, current.tile)
            blocks.pop()
            previous.close()
            current.close()
            current_start, current = previous_start, parent
        blocks.append((current_start, current))
    except BaseException:
        current.close()
        raise


def import_exact_source(
    source: ExactSource,
    geometry: SourceGeometry,
    tiles: TileArena,
    alphabet: TileAlphabetID,
) -> TileLease:
    """Import one immutable source and compact blank padding into TileArena."""
    if type(source) is not ExactSource:
        raise TypeError("tile source import requires an immutable exact source")
    source.__post_init__()
    if type(geometry) is not SourceGeometry or type(tiles) is not TileArena:
        raise TypeError("tile source import requires source and tile arenas")
    if geometry.ledger is not tiles.ledger:
        raise ValueError("tile source import requires one index ledger")
    OriginalSourceConstruction.validate_source(geometry.construction, source)
    logical_extent = len(source.digits) if source.extent is None else source.extent
    if not source.digits:
        raise ValueError("tile source import requires at least one original symbol")
    tile_alphabet = tiles.alphabet(alphabet)
    active_symbols = (
        source.base if source.alphabet_size is None else source.alphabet_size
    )
    symbol_count = max(active_symbols, source.blank + 1)
    if (
        tile_alphabet.radix != source.base
        or tile_alphabet.blank != source.blank
        or tile_alphabet.symbol_count != symbol_count
    ):
        raise ValueError("tile alphabet does not describe the exact source")
    if not geometry.has_materialized_source:
        # The source geometry authenticates original symbols.  Blank extension
        # belongs to the tile arena and is built below as a logarithmic tower.
        geometry.span(source.digits, source.blank, len(source.digits))
    else:
        geometry.require_source(source.digits, source.blank)

    padded_width = 1 << max(0, logical_extent - 1).bit_length()
    blocks: list[tuple[int, TileLease]] = []
    blank_power: TileLease | None = None
    blank_level = -1
    try:
        for position in range(len(source.digits)):
            _append_block(
                tiles,
                blocks,
                position,
                tiles.leaf(alphabet, geometry.read(position)),
            )
        position = len(source.digits)
        while position < padded_width:
            remaining = padded_width - position
            level = remaining.bit_length() - 1
            if position:
                level = min(level, (position & -position).bit_length() - 1)
            if blank_power is None:
                blank_power = tiles.leaf(alphabet, source.blank)
                blank_level = 0
            if level < blank_level:
                raise AssertionError("blank padding levels must be nondecreasing")
            while blank_level < level:
                parent = tiles.join(blank_power.tile, blank_power.tile)
                blank_power.close()
                blank_power = parent
                blank_level += 1
            block = tiles.retain(blank_power.tile)
            _append_block(tiles, blocks, position, block)
            position += 1 << level
        if len(blocks) != 1 or blocks[0][0] != 0:
            raise AssertionError("source import did not produce one dyadic root")
        root = blocks.pop()[1]
        if tiles.resolve(root.tile).width != padded_width:
            root.close()
            raise AssertionError("source import produced another padded extent")
        tiles.ledger.bump(_observation_keys.TILE_SOURCE_IMPORTS)
        return root
    except BaseException:
        _close_all(blocks)
        raise
    finally:
        if blank_power is not None:
            blank_power.close()


class LazyProjection:
    """Point-lazy public facade over one canonical tile application."""

    __slots__ = (
        "__weakref__",
        "_application",
        "_closed",
        "_cylinder_workspace",
        "_logical_extent",
        "ledger",
        "scheduler",
    )
    ledger: ResourceLedger

    def __init__(
        self,
        scheduler: TileScheduler,
        action: FieldCellActionID,
        source: ExactSource,
        geometry: SourceGeometry,
        alphabet: TileAlphabetID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> None:
        if type(scheduler) is not TileScheduler:
            raise TypeError("lazy tile projection requires the shared scheduler")
        scheduler.results.validate_shape(action, ports, wiring)
        root = import_exact_source(source, geometry, scheduler.tiles, alphabet)
        try:
            application = scheduler.application(action, root.tile, ports, wiring)
        finally:
            root.close()
        self.scheduler, self.ledger = scheduler, scheduler.ledger
        self._application = application
        self._logical_extent = (
            len(source.digits) if source.extent is None else source.extent
        )
        self._closed = False
        self._cylinder_workspace: TileCylinderWorkspace | None = None
        self.ledger.register_execution_root(self)

    def _open(self) -> TileApplication:
        issued = self.ledger.owns_execution_root(self)
        if not issued:
            raise ValueError("tile projection was not issued by its ledger")
        if type(self._closed) is not bool or self._closed:
            raise ValueError("closed lazy tile projection")
        if type(self._application) is not TileApplication:
            raise ValueError("malformed lazy tile projection")
        if (
            type(self.scheduler) is not TileScheduler
            or self._application.scheduler is not self.scheduler
            or self.scheduler.ledger is not self.ledger
        ):
            raise ValueError("tile projection belongs to another scheduler")
        _ = self._application.source
        return self._application

    def audit_snapshot(self) -> LazyProjectionAuditSnapshot:
        """Expose the retained application relationship to resource auditors."""
        from number_compiler.resources.tile_runtime_audit_contracts import (
            LazyProjectionAuditSnapshot,
        )

        return LazyProjectionAuditSnapshot(
            self.ledger,
            self.scheduler,
            self._application,
            self._logical_extent,
            self._closed,
        )

    @source_reads_only
    def point(self, position: int) -> int:
        if type(position) is not int:
            raise TypeError("tile projection coordinate requires an exact integer")
        if not 0 <= position < self._logical_extent:
            raise IndexError(position)
        return self._open().point(position)

    @source_reads_only
    def active_width(self) -> int:
        width = self._open().width(self._logical_extent)
        self.ledger.bump(_observation_keys.TILE_PROJECTION_WIDTH_OBSERVATIONS)
        return width

    @source_reads_only
    def temporal_cocycle(self) -> TemporalCocycle:
        """Demand authenticated bound weights through the existing interface."""
        from number_compiler.hashlife.tiles.tile_context import TemporalCocycle

        application = self._open()
        application.validate_execution()
        result = application.interface()
        self.ledger.bump(_observation_keys.TILE_PROJECTION_COCYCLE_OBSERVATIONS)
        return TemporalCocycle(
            result.physical_ticks, result.event_weight, result.frame_shift
        )

    @source_reads_only
    def physical_support(self) -> OrderedBooleanSupport:
        """Demand the source-bound ordered support from the normal interface path."""
        application = self._open()
        application.validate_execution()
        result = application.interface()
        support = result.physical_support
        if support is None:
            raise ValueError("bound application has no physical support")
        if support.owner is not self.scheduler.physical_supports:
            raise ValueError("bound support belongs to another scheduler")
        support.owner.validate(support)
        if (
            support.ticks != result.physical_ticks
            or support.true_count != result.event_weight
        ):
            raise ValueError("bound support disagrees with interface weights")
        self.ledger.bump(
            _observation_keys.TILE_PROJECTION_PHYSICAL_SUPPORT_OBSERVATIONS
        )
        return support

    @source_reads_only
    def mirror_obstruction(
        self, *, first_width: int = 1
    ) -> TwistedCylinderProjection | None:
        from number_compiler.hashlife.observation.tile_cylinder import (
            TileCylinderWorkspace,
            tile_mirror_obstruction,
        )

        application = self._open()
        if self._cylinder_workspace is None:
            self._cylinder_workspace = TileCylinderWorkspace(self.ledger)
        return tile_mirror_obstruction(
            application,
            self._logical_extent,
            self._cylinder_workspace,
            first_width=first_width,
        )

    def retained_entries(self) -> int:
        self._open()
        return self.ledger.entries

    def iter_endpoint_tiles(self) -> Generator[TileID, None, None]:
        """Explicitly lower the complete endpoint as a stream of leaf TileIDs."""
        application = self._open()
        completed = application.complete()
        lease = self.scheduler.tiles.retain(completed.output)
        try:
            extent = self.scheduler.tiles.active_width(
                completed.output,
                self._logical_extent,
            )
            pending = [(lease.tile, 0)]
            while pending:
                tile, start = pending.pop()
                if start >= extent:
                    continue
                record = self.scheduler.tiles.resolve(tile)
                if not record.level:
                    self.ledger.bump(_observation_keys.TILE_ENDPOINT_EMISSIONS)
                    yield tile
                    continue
                if record.left is None or record.right is None:
                    raise ValueError("malformed endpoint tile")
                half = 1 << (record.level - 1)
                pending.extend(((record.right, start + half), (record.left, start)))
                self.ledger.bump(_observation_keys.TILE_ENDPOINT_PROJECTION_DESCENTS)
        finally:
            lease.close()

    def close(self) -> None:
        if type(self._closed) is not bool:
            raise ValueError("malformed lazy tile projection")
        if not self._closed:
            try:
                self._application.close()
            finally:
                if self._cylinder_workspace is not None:
                    self._cylinder_workspace.dispose()
            self._closed = True

    def __enter__(self) -> Self:
        self._open()
        return self

    def __exit__(self, *_exception: object) -> None:
        self.close()


def primitive_tile_power(
    effect: BlockEffect,
    *,
    family_hooks: FamilyTileHooks | None = None,
) -> tuple[BlockEffect, ...] | None:
    """Recognize admitted primitive syntax without inferring an arithmetic family."""
    from number_compiler.arithmetic.contracts.block_effect import _effect_key
    from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
    from number_compiler.hashlife.actions.lazy_compiler import ProgramComposition
    from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect

    primitives = (BaseBlockEffect, DigitNormalizeBlockEffect)
    is_primitive = type(effect) in primitives or (
        family_hooks is not None and family_hooks.owns_effect(effect)
    )
    if is_primitive:
        return (effect,)
    if type(effect) is not ProgramComposition:
        return None
    first_is_primitive = type(effect.first) in primitives or (
        family_hooks is not None and family_hooks.owns_effect(effect.first)
    )
    second_is_primitive = type(effect.second) in primitives or (
        family_hooks is not None and family_hooks.owns_effect(effect.second)
    )
    if (
        first_is_primitive
        and second_is_primitive
        and (
            _effect_key(effect.first) == _effect_key(effect.second)
            or (
                type(effect.first) is BaseBlockEffect
                and type(effect.second) is DigitNormalizeBlockEffect
                and effect.first.base == effect.second.base
            )
        )
    ):
        return effect.first, effect.second
    return None


def build_primitive_projection(
    effect: BlockEffect,
    geometry: SourceGeometry,
    *,
    family_hooks: FamilyTileHooks | None = None,
    pair_transfer_factory: FinitePairTransferFactory | None = None,
) -> LazyProjection:
    """Admit a supported primitive action into the shared tile execution path."""
    if primitive_tile_power(effect, family_hooks=family_hooks) is None:
        raise TypeError("unsupported canonical tile primitive composition")
    return build_tile_projection(
        effect,
        geometry,
        family_hooks=family_hooks,
        pair_transfer_factory=pair_transfer_factory,
    )


def lower_fixed_tile_compatibility(
    effect: BlockEffect,
    compiler: LazyCompiler,
    family_hooks: FamilyTileHooks | None = None,
) -> BlockEffect:
    """Lower a family's checked compatibility artifact at its runtime boundary."""
    if family_hooks is None or not family_hooks.owns_compatibility(effect):
        return effect
    from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler

    if type(compiler) is not LazyCompiler:
        raise TypeError("compatibility lowering requires the canonical compiler")
    family_hooks.validate_compatibility(effect)
    return family_hooks.lower_compatibility(effect, compiler)


def validate_fixed_tile_compatibility(
    effect: BlockEffect,
    family_hooks: FamilyTileHooks | None = None,
) -> None:
    """Validate a recognized compatibility artifact before runtime allocation."""
    if family_hooks is None or not family_hooks.owns_compatibility(effect):
        return
    try:
        family_hooks.validate_compatibility(effect)
    except (TypeError, ValueError) as error:
        raise ValueError(
            "compatibility lowering requires its immutable certificate"
        ) from error


def build_tile_projection(
    effect: BlockEffect,
    geometry: SourceGeometry,
    *,
    family_hooks: FamilyTileHooks | None = None,
    pair_transfer_factory: FinitePairTransferFactory | None = None,
) -> LazyProjection:
    """Publish one tile runtime, retiring unissued arenas if construction fails."""
    from number_compiler.resources.construction_scope import RuntimeConstruction

    if type(geometry) is not SourceGeometry:
        raise TypeError("tile projection requires authenticated source geometry")
    with RuntimeConstruction(geometry.ledger):
        return _build_tile_projection(
            effect,
            geometry,
            family_hooks=family_hooks,
            pair_transfer_factory=pair_transfer_factory,
        )


def _build_tile_projection(
    effect: BlockEffect,
    geometry: SourceGeometry,
    *,
    family_hooks: FamilyTileHooks | None = None,
    pair_transfer_factory: FinitePairTransferFactory | None = None,
) -> LazyProjection:
    """Compile a binary operator DAG into one canonical tile application.

    The work stack follows existing temporal edges; shared children are admitted
    once. It never expands a power into a primitive itinerary or executes output
    during compilation.
    """
    if type(geometry) is not SourceGeometry:
        raise TypeError("tile projection requires authenticated source geometry")
    if type(geometry.ledger) is not ResourceLedger:
        raise TypeError("tile projection requires its index resource ledger")
    OriginalSourceConstruction.validate_source(
        geometry.construction, geometry.construction.source
    )
    from number_compiler.arithmetic.contracts.block_kernel import (
        BaseBlockEffect,
        FiniteBlockEffect,
    )
    from number_compiler.arithmetic.functions.semantic_functions import (
        SemanticFunctionArena,
    )
    from number_compiler.hashlife.actions.lazy_compiler import ProgramComposition
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondQuotientArena,
    )
    from number_compiler.hashlife.observation.diamond_observers import (
        NonblankBlockEffect,
    )
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
    from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect

    if family_hooks is not None and type(family_hooks) is not FamilyTileHooks:
        raise TypeError("tile projection requires canonical family hooks")
    if pair_transfer_factory is not None and not is_finite_pair_transfer_factory(
        pair_transfer_factory
    ):
        raise TypeError(type(pair_transfer_factory))

    supported = type(effect) in (
        ProgramComposition,
        BaseBlockEffect,
        FiniteBlockEffect,
        DigitNormalizeBlockEffect,
        NonblankBlockEffect,
    ) or (family_hooks is not None and family_hooks.owns_effect(effect))
    if not supported:
        from number_compiler.hashlife.actions.lazy_compiler import (
            UnsupportedInterfaceError,
        )

        raise UnsupportedInterfaceError(
            "tile projection requires a supported finite interface"
        )

    ledger = geometry.ledger
    tiles = TileArena(ledger)
    interfaces = DiamondQuotientArena(
        SemanticFunctionArena(ledger, cache_construction_reductions=True)
    )
    pair_transfer: FinitePairTransfer | None = None
    if pair_transfer_factory is not None:
        created_transfer = pair_transfer_factory.create(ledger)
        if not is_finite_pair_transfer(created_transfer):
            raise TypeError(type(created_transfer))
        pair_transfer = created_transfer
    if pair_transfer is not None and pair_transfer.ledger is not ledger:
        raise ValueError("tile pair-transfer factory returned a foreign strategy")
    adapter = PrimitiveTileKernelAdapter(
        tiles,
        DiamondKernelArena(ledger),
        interfaces,
        family_hooks=family_hooks,
        pair_transfer=pair_transfer,
    )
    prefix = f"tile-program-import-{len(ledger.inventory())}"
    built_owner = ledger.register(prefix + "-completed", "query_memo")
    active_owner = ledger.register(prefix + "-pending", "query_memo")
    stack_owner = ledger.register(prefix + "-stack", "query_memo")
    built: LedgerDict[int, FieldCellActionID] = ledger.make_dict(built_owner)
    active: LedgerDict[int, bool] = ledger.make_dict(active_owner)
    pending: LedgerList[tuple[BlockEffect, bool]] = ledger.make_list(
        stack_owner, nodes_per_entry=0, append_only=False
    )
    built_credit = active_credit = stack_credit = 0
    try:
        ledger.reserve(stack_owner, entries=1)
        stack_credit += 1
        pending.append((effect, False))
        while pending:
            current, ready = pending.pop()
            ledger.release(stack_owner, entries=1)
            stack_credit -= 1
            identity = id(current)
            if identity in built:
                continue
            if type(current) is not ProgramComposition:
                admitted = adapter.admit(current)
            elif ready:
                admitted = adapter.compose(
                    built[id(current.first)], built[id(current.second)]
                )
                del active[identity]
                ledger.release(active_owner, entries=1)
                active_credit -= 1
            else:
                if identity in active:
                    raise ValueError("temporal composition contains a dependency cycle")
                ledger.reserve_many(((active_owner, 1, 0), (stack_owner, 3, 0)))
                active_credit += 1
                stack_credit += 3
                active[identity] = True
                pending.extend(
                    ((current, True), (current.second, False), (current.first, False))
                )
                ledger.bump(_observation_keys.TILE_PROJECTION_COMPILATION_FRAMES)
                continue
            ledger.reserve(built_owner, entries=1)
            built_credit += 1
            built[identity] = admitted
            ledger.bump(_observation_keys.TILE_PROJECTION_COMPILATION_FRAMES)
        action = built[id(effect)]
    finally:
        for owner, store, credit in (
            (built_owner, built, built_credit),
            (active_owner, active, active_credit),
            (stack_owner, pending, stack_credit),
        ):
            store.clear()
            ledger.release(owner, entries=credit)
    results = CompletedResultArena(
        tiles,
        interfaces,
        action_authority=adapter,
        validate_action=adapter.validate_action,
        signature_for=adapter.signature_for,
    )
    adapter.attach_results(results)
    scheduler = TileScheduler(tiles, results, adapter)
    return LazyProjection(
        scheduler,
        action,
        geometry.construction.source,
        geometry,
        adapter.alphabet(action),
        adapter.initial_ports(action),
        adapter.wiring(action),
    )


__all__ = [
    "LazyProjection",
    "build_primitive_projection",
    "build_tile_projection",
    "import_exact_source",
    "lower_fixed_tile_compatibility",
    "primitive_tile_power",
    "validate_fixed_tile_compatibility",
]
