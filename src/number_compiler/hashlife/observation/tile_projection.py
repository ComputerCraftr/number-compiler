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
from number_compiler.resources.stores import LedgerDict, LedgerList

if TYPE_CHECKING:
    from number_compiler.arithmetic.polynomials.twisted_observer import (
        TwistedCylinderProjection,
    )
    from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
    from number_compiler.hashlife.observation.tile_cylinder import TileCylinderWorkspace
    from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
    from number_compiler.sequences.collatz.physical_support import PhysicalSupport


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
    OriginalSourceConstruction.validate_source(geometry._construction, source)
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
    if geometry._read_root is None:
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
        tiles.ledger.bump("tile_source_imports")
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
        issued = self.ledger._execution_roots.get(id(self))
        if issued is None or issued() is not self:
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
        self.ledger.bump("tile_projection_width_observations")
        return width

    @source_reads_only
    def temporal_cocycle(self) -> TemporalCocycle:
        """Demand authenticated bound weights through the existing interface."""
        from number_compiler.hashlife.tiles.tile_context import TemporalCocycle

        application = self._open()
        application.validate_execution()
        result = application.interface()
        self.ledger.bump("tile_projection_cocycle_observations")
        return TemporalCocycle(
            result.physical_ticks, result.event_weight, result.frame_shift
        )

    @source_reads_only
    def physical_support(self) -> PhysicalSupport:
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
            or support.odd_ticks != result.event_weight
        ):
            raise ValueError("bound support disagrees with interface weights")
        self.ledger.bump("tile_projection_physical_support_observations")
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
                    self.ledger.bump("tile_endpoint_emissions")
                    yield tile
                    continue
                if record.left is None or record.right is None:
                    raise ValueError("malformed endpoint tile")
                half = 1 << (record.level - 1)
                pending.extend(((record.right, start + half), (record.left, start)))
                self.ledger.bump("tile_endpoint_projection_descents")
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


def primitive_tile_power(effect: BlockEffect) -> tuple[BlockEffect, ...] | None:
    """Recognize admitted primitive syntax without inferring an arithmetic family."""
    from number_compiler.arithmetic.contracts.block_effect import _effect_key
    from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
    from number_compiler.hashlife.actions.lazy_compiler import ProgramComposition
    from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
    from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect

    primitives = (
        BaseBlockEffect,
        CollatzPhysicalBlockEffect,
        DigitNormalizeBlockEffect,
    )
    if type(effect) in primitives:
        return (effect,)
    if (
        type(effect) is ProgramComposition
        and type(effect.first) in primitives
        and type(effect.second) in primitives
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
    effect: BlockEffect, geometry: SourceGeometry
) -> LazyProjection:
    """Admit a supported primitive action into the shared tile execution path."""
    if primitive_tile_power(effect) is None:
        raise TypeError("unsupported canonical tile primitive composition")
    return build_tile_projection(effect, geometry)


def lower_fixed_tile_compatibility(
    effect: BlockEffect,
    compiler: LazyCompiler,
) -> BlockEffect:
    """Lower the exact proof C4 facade to the production physical action DAG.

    The type is imported only after the caller presents the proof definition's
    exact name. Its immutable metadata and table digest are validated before
    the four-step primitive composition is built in the caller's compiler.
    Proof boundary states never enter the tile adapter.
    """
    if type(effect).__name__ != "PhysicalCollatzFourBlockEffect":
        return effect
    from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
        PhysicalCollatzFourBlockEffect,
    )
    from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
    from number_compiler.sequences.collatz.compilation import (
        compile_collatz_physical_power,
    )

    if type(effect) is not PhysicalCollatzFourBlockEffect:
        return effect
    if type(compiler) is not LazyCompiler:
        raise TypeError("fixed C4 lowering requires the canonical compiler")
    validate_fixed_tile_compatibility(effect)
    lowered = compile_collatz_physical_power(compiler, 4).root
    if lowered is None or lowered.exponent != 4:
        raise AssertionError("fixed C4 lowering lost its physical span")
    return lowered


def validate_fixed_tile_compatibility(effect: BlockEffect) -> None:
    """Validate the exact proof C4 facade without allocating runtime state."""
    if type(effect).__name__ != "PhysicalCollatzFourBlockEffect":
        return
    from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
        PhysicalCollatzFourBlockEffect,
        is_verified_physical_four,
    )

    if type(effect) is not PhysicalCollatzFourBlockEffect:
        raise ValueError("fixed C4 lowering requires its exact proof definition")
    try:
        verified = is_verified_physical_four(effect)
    except (TypeError, ValueError) as error:
        raise ValueError(
            "fixed C4 lowering requires its immutable certificate"
        ) from error
    if not verified:
        raise ValueError("fixed C4 lowering requires its immutable certificate")


def build_tile_projection(
    effect: BlockEffect, geometry: SourceGeometry
) -> LazyProjection:
    """Publish one tile runtime, retiring unissued arenas if construction fails."""
    from number_compiler.resources.construction_scope import RuntimeConstruction

    if type(geometry) is not SourceGeometry:
        raise TypeError("tile projection requires authenticated source geometry")
    with RuntimeConstruction(geometry.ledger):
        return _build_tile_projection(effect, geometry)


def _build_tile_projection(
    effect: BlockEffect, geometry: SourceGeometry
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
        geometry._construction, geometry._construction.source
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
    from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect

    if type(effect) not in (
        ProgramComposition,
        BaseBlockEffect,
        FiniteBlockEffect,
        DigitNormalizeBlockEffect,
        NonblankBlockEffect,
        CollatzPhysicalBlockEffect,
    ):
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
    adapter = PrimitiveTileKernelAdapter(tiles, DiamondKernelArena(ledger), interfaces)
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
                ledger.bump("tile_projection_compilation_frames")
                continue
            ledger.reserve(built_owner, entries=1)
            built_credit += 1
            built[identity] = admitted
            ledger.bump("tile_projection_compilation_frames")
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
        geometry._construction.source,
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
