"""Radix projection by canonical division applications over completed tiles."""

from __future__ import annotations

from array import array
from collections.abc import MutableMapping

from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.arithmetic.radix_division import (
    SymbolicBinaryDivisionEffect,
    certified_binary_division_radix,
)
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.execution.tile_scheduler import (
    TileApplication,
    TileScheduler,
)
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.ledger import ResourceLedger

MAX_FINITE_TILE_RADIX = 256
MAX_TILE_RADIX = 1 << 63


def _division_tables(radix: int) -> tuple[tuple[int, ...], bytes]:
    if type(radix) is not int:
        raise TypeError("tile radix requires an exact integer")
    if not 2 <= radix <= MAX_FINITE_TILE_RADIX:
        raise ValueError(
            f"canonical finite tile radix supports 2..{MAX_FINITE_TILE_RADIX}"
        )
    # State = 2 * remainder + quotient-nonzero-in-higher-suffix.  The second
    # bit lets the right-to-left scan turn leading quotient zeroes into blank
    # cells without retaining a coordinate or a quotient prefix.
    states = 2 * radix
    right: list[int] = []
    for state in range(states):
        remainder, seen = divmod(state, 2)
        for symbol in range(3):
            if symbol == 2:
                right.append(state)
                continue
            combined = 2 * remainder + symbol
            quotient, outgoing = divmod(combined, radix)
            right.append(2 * outgoing + int(bool(seen or quotient)))
    outputs: list[int] = []
    for symbol in range(3):
        for state in range(states):
            remainder, seen = divmod(state, 2)
            if symbol == 2:
                outputs.append(2)
                continue
            quotient = (2 * remainder + symbol) // radix
            outputs.append(quotient if seen or quotient else 2)
    return tuple(right), bytes(outputs)


def _division_effect(
    radix: int,
) -> FiniteBlockEffect | SymbolicBinaryDivisionEffect:
    """Return MSD-normalizing binary long division with a bounded carry port."""
    if type(radix) is not int:
        raise TypeError("tile radix requires an exact integer")
    if not 2 <= radix <= MAX_TILE_RADIX:
        raise ValueError(f"canonical tile radix supports 2..{MAX_TILE_RADIX}")
    if radix > MAX_FINITE_TILE_RADIX:
        return SymbolicBinaryDivisionEffect(radix)
    right, outputs = _division_tables(radix)
    states = 2 * radix
    return FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=1,
        right_count=states,
        alphabet_size=3,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", [0] * 3),
        right_transitions=array("I", right),
        outputs=outputs,
        kernel_name=f"normalized-binary-division-{radix}",
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
        blank=2,
    )


def _valid_division_effect(effect: object, radix: int) -> bool:
    return type(radix) is int and certified_binary_division_radix(effect) == radix


class TileRadixProjection:
    """LSD-first radix observations over one canonical binary source tile.

    A sparse entry ``q`` applies ``D**q`` directly to the original source.
    When ``q - 1`` is already complete, the next quotient consumes that
    canonical tile through one ``D`` application.  This reuses dense digit
    observations without retaining or replaying a cold division itinerary.
    """

    __slots__ = (
        "scheduler",
        "adapter",
        "ledger",
        "radix",
        "action",
        "_source",
        "_stage_owner",
        "_stages",
        "_closed",
        "__weakref__",
    )
    ledger: ResourceLedger

    def __init__(
        self,
        scheduler: TileScheduler,
        adapter: PrimitiveTileKernelAdapter,
        source: TileID,
        radix: int,
    ) -> None:
        if type(scheduler) is not TileScheduler:
            raise TypeError("tile radix requires the shared tile scheduler")
        if type(adapter) is not PrimitiveTileKernelAdapter:
            raise TypeError("tile radix requires the primitive tile adapter")
        if (
            scheduler.adapter is not adapter
            or scheduler.tiles is not adapter.tiles
            or scheduler.results is not adapter.results
        ):
            raise ValueError("tile radix runtime components belong to another index")
        if type(radix) is not int:
            raise TypeError("tile radix requires an exact integer")
        if not 2 <= radix <= MAX_TILE_RADIX:
            raise ValueError(f"canonical tile radix supports 2..{MAX_TILE_RADIX}")
        if radix != 2 and radix & (radix - 1) == 0:
            raise ValueError(
                "tile radix projection leaves grouped binary limbs to binary observation"
            )
        source_record = scheduler.tiles.resolve(source)
        alphabet = scheduler.tiles.alphabet(source_record.alphabet)
        if (
            alphabet.symbol_count,
            alphabet.blank,
            alphabet.radix,
            alphabet.cell_bits,
            alphabet.interpretation,
            alphabet.version,
        ) != (
            3,
            2,
            2,
            2,
            "unsigned-radix-cell-with-explicit-blank",
            "canonical-tile-alphabet-v1",
        ):
            raise ValueError("tile radix input is not a canonical binary tile")
        # The authenticated adapter owns primitive admission.  A Collatz
        # application need not have observed this radix before its completed
        # tile is consumed as a division source.
        action = adapter.admit(_division_effect(radix), cocycle=TemporalCocycle())
        if adapter.alphabet(action) != source_record.alphabet:
            raise ValueError("division action has another canonical alphabet")
        self.scheduler, self.adapter, self.ledger = (
            scheduler,
            adapter,
            scheduler.ledger,
        )
        self.radix, self.action = radix, action
        self._source = scheduler.tiles.retain(source)
        self._stage_owner = self.ledger.register(
            f"tile-radix-{len(self.ledger.inventory())}-stages",
            "tile_radix_stage_binding",
        )
        self._stages: MutableMapping[int, TileApplication] = self.ledger.make_dict(
            self._stage_owner,
            nodes_per_entry=0,
        )
        self._closed = False
        self.ledger.register_execution_root(self)

    def _open(self) -> None:
        if type(self._closed) is not bool or self._closed:
            raise ValueError("closed tile radix projection")

    def _stage(self, exponent: int) -> TileApplication:
        found = self._stages.get(exponent)
        if found is not None:
            self.ledger.bump("tile_radix_stage_early_hits")
            return found
        self.ledger.reserve(self._stage_owner, entries=1)
        application: TileApplication | None = None
        try:
            previous_exponent = 0
            previous: TileApplication | None = None
            for candidate_exponent, candidate in self._stages.items():
                if previous_exponent < candidate_exponent < exponent:
                    previous_exponent, previous = candidate_exponent, candidate
            if previous is None:
                action = self.adapter.power(self.action, exponent)
                source = self._source.tile
                self.ledger.bump("tile_radix_direct_power_stages")
            else:
                previous.complete()
                suffix = self.adapter.power(
                    self.action,
                    exponent - previous_exponent,
                )
                action = self.adapter.compose(previous.action, suffix)
                source = self._source.tile
                self.ledger.bump("tile_radix_completed_stage_reuses")
                self.ledger.bump(
                    "tile_radix_completed_stage_reuse_span",
                    exponent - previous_exponent,
                )
            application = self.scheduler.application(
                action,
                source,
                self.adapter.initial_ports(action),
                self.adapter.wiring(action),
            )
            completed = application.complete()
            if len(completed.outgoing_ports) != 2:
                raise ValueError("division result has another boundary shape")
            state = completed.outgoing_ports[1]
            if type(state) is not int or not 0 <= state < 2 * self.radix:
                raise ValueError("division result has an invalid remainder state")
            extent = self.scheduler.tiles.resolve(completed.output).extent
            if bool(state & 1) != bool(extent):
                raise ValueError("division activity disagrees with its quotient")
            self._stages[exponent] = application
            application = None
            self.ledger.bump("tile_radix_stage_publications")
            self.ledger.bump("tile_radix_binary_power_observations")
            self.ledger.counters["tile_radix_stage_peak"] = max(
                self.ledger.counters.get("tile_radix_stage_peak", 0),
                len(self._stages),
            )
            return self._stages[exponent]
        except BaseException:
            if application is not None:
                application.close()
            self.ledger.release(self._stage_owner, entries=1)
            raise

    def _validate_index(self, index: int) -> None:
        self._open()
        if type(index) is not int:
            raise TypeError("radix digit coordinate requires an exact integer")
        if index < 0:
            raise IndexError(index)
        if index >= self.scheduler.tiles.resolve(self._source.tile).width:
            raise IndexError(index)

    @source_reads_only
    def point(self, index: int) -> int:
        self._validate_index(index)
        if (
            index
            and not self.scheduler.tiles.resolve(
                self._stage(index).complete().output,
            ).extent
        ):
            raise IndexError(index)
        completed = self._stage(index + 1).complete()
        self.ledger.bump("tile_radix_digit_observations")
        return completed.outgoing_ports[1] // 2

    @source_reads_only
    def quotient(self, stages: int) -> TileID:
        """Return a pinned canonical quotient root after a positive stage count."""
        if type(stages) is not int:
            raise TypeError("radix quotient stage requires an exact integer")
        if stages < 1:
            raise ValueError("radix quotient stage must be positive")
        self._validate_index(stages - 1)
        return self._stage(stages).complete().output

    @source_reads_only
    def active_width(self) -> int:
        self._open()
        low, high = 1, self.scheduler.tiles.resolve(self._source.tile).width
        while low < high:
            middle = (low + high) // 2
            output = self._stage(middle).complete().output
            if self.scheduler.tiles.resolve(output).extent:
                low = middle + 1
            else:
                high = middle
        if self.scheduler.tiles.resolve(self._stage(low).complete().output).extent:
            raise AssertionError("radix quotient remained active beyond source width")
        return low

    def retained_entries(self) -> int:
        self._open()
        return self.ledger.entries

    def close(self) -> None:
        if type(self._closed) is not bool:
            raise ValueError("malformed tile radix projection")
        if not self._closed:
            count = len(self._stages)
            while self._stages:
                exponent = next(iter(self._stages))
                self._stages.pop(exponent).close()
            self.ledger.release(self._stage_owner, entries=count)
            self._source.close()
            self._closed = True

    def __enter__(self) -> TileRadixProjection:
        self._open()
        return self

    def __exit__(self, *_exception: object) -> None:
        self.close()


class TileRadixObservation:
    """Demand radix remainders from a powered tile application without endpoints."""

    __slots__ = (
        "projection",
        "scheduler",
        "adapter",
        "radix",
        "division",
        "_owner",
        "_apps",
        "_closed",
        "__weakref__",
    )

    def __init__(self, projection: LazyProjection, radix: int) -> None:
        if type(projection) is not LazyProjection:
            raise TypeError("tile radix observation requires an issued tile projection")
        application = projection._open()
        scheduler = projection.scheduler
        adapter = scheduler.adapter
        if type(adapter) is not PrimitiveTileKernelAdapter:
            raise TypeError("tile radix observation requires the shared tile adapter")
        if type(radix) is not int:
            raise TypeError("tile radix requires an exact integer")
        if not 2 <= radix <= MAX_TILE_RADIX:
            raise ValueError(f"canonical tile radix supports 2..{MAX_TILE_RADIX}")
        self.projection, self.scheduler, self.adapter, self.radix = (
            projection,
            scheduler,
            adapter,
            radix,
        )
        self.division = adapter.admit(
            _division_effect(radix), cocycle=TemporalCocycle()
        )
        self._owner = scheduler.ledger.register(
            f"tile-radix-{radix}-observations-{len(scheduler.ledger.inventory())}",
            "tile_radix_observation_binding",
        )
        self._apps: MutableMapping[int, TileApplication] = scheduler.ledger.make_dict(
            self._owner,
        )
        scheduler.ledger.register_container(
            self._owner,
            self._apps,
            payloads=self._apps.items,
        )
        self._closed = False
        scheduler.ledger.register_execution_root(self)
        application.source

    def _application(self, index: int) -> TileApplication:
        if type(self._closed) is not bool or self._closed:
            raise ValueError("closed tile radix observation")
        if type(self.projection) is not LazyProjection:
            raise TypeError("tile radix observation lost its issued projection")
        source_application = self.projection._open()
        if (
            self.projection.scheduler is not self.scheduler
            or self.scheduler.adapter is not self.adapter
            or source_application.scheduler is not self.scheduler
        ):
            raise ValueError("tile radix observation belongs to another application")
        found = self._apps.get(index)
        if found is not None:
            self.scheduler.ledger.bump("tile_radix_observation_early_hits")
            return found
        division = self.adapter.power(self.division, index + 1)
        action = self.adapter.compose(source_application.action, division)
        result = self.scheduler.application(
            action,
            source_application.source,
            self.adapter.initial_ports(action),
            self.adapter.wiring(action),
        )
        try:
            self.scheduler.ledger.reserve(self._owner, entries=1)
            self._apps[index] = result
        except BaseException:
            result.close()
            raise
        self.scheduler.ledger.bump("tile_radix_observation_publications")
        return result

    @source_reads_only
    def digit(self, index: int) -> int:
        if type(index) is not int:
            raise TypeError("radix coordinate must be an exact integer")
        if index < 0:
            raise IndexError(index)
        payload = self._application(index).interface()
        state = payload.outgoing_ports[1]
        if not state:
            raise IndexError(index)
        self.scheduler.ledger.bump("tile_radix_interface_observations")
        return state // 2

    def close(self) -> None:
        if type(self._closed) is not bool:
            raise ValueError("malformed tile radix observation")
        if self._closed:
            return
        count = len(self._apps)
        for index in tuple(self._apps):
            self._apps.pop(index).close()
        if count:
            self.scheduler.ledger.release(self._owner, entries=count)
        self._closed = True


__all__ = [
    "MAX_FINITE_TILE_RADIX",
    "MAX_TILE_RADIX",
    "TileRadixObservation",
    "TileRadixProjection",
]
