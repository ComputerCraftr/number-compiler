"""Finite directed-growth and universal border-width quotients.

This owner keeps three claims separate: Boolean diagonal algebra, a finite
source-issued growth tape, and universal min/max bounds over all inward carry
maps.  Squaring the former two is algebraic; neither authorizes a physical
source repeat.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from enum import Enum
from typing import TYPE_CHECKING

from number_compiler.arithmetic.carry.carry_monoid import (
    apply_carry_fn,
)
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.resources.metric_keys import reverse_add as _metric

from .border_carry_safety import (
    BilateralCyclePort,
    BorderTile,
    bilateral_cycle_letter,
    border_bilateral_port,
)

if TYPE_CHECKING:
    from .q19_border_control import CertifiedBorderGrowth


_MAX_WINDOW = 4096
_MAX_SOURCE_INLETS = 65536
_MAX_POWER_STEPS = 1_000_000
_MAX_STATES = 5000
_MAX_EDGES = 15000
_MAX_COMPOSITION_PAIRS = 5_000_000
_MAX_RELATION_CELLS = 1_000_000


class BorderWidthWork(Enum):
    """Measured operations in the request-local sparse width action."""

    STATE_VISIT = "state_visits"
    STATE = "states"
    EDGE = "edges"
    COMPOSITION_PAIR = "composition_pairs"
    RELATION_CELL = "relation_cells"


class BorderWidthPowerRefused(ValueError):
    """A valid width demand exceeds its finite source or work envelope."""


def _scalar_snapshot(value: object) -> tuple[object, ...]:
    if type(value) in (int, bool, str, bytes, type(None)):
        return type(value), value
    return type(value), id(value)


def _mask_snapshot(mask: object) -> tuple[object, ...]:
    if type(mask) is not DirectedGrowthMask:
        return (type(mask), id(mask))
    return (
        DirectedGrowthMask,
        _scalar_snapshot(mask.window),
        _scalar_snapshot(mask.extra),
        _scalar_snapshot(mask.missing),
    )


def _action_snapshot(action: object) -> tuple[object, ...]:
    if type(action) is not DirectedDiagonalAction:
        return (type(action), id(action))
    return (
        DirectedDiagonalAction,
        _scalar_snapshot(action.window),
        _scalar_snapshot(action.duration),
        _scalar_snapshot(action.growth_first),
        _scalar_snapshot(action.growth_second),
        _scalar_snapshot(action.suffix_extra),
        _scalar_snapshot(action.suffix_missing),
    )


def _inlets_snapshot(inlets: object) -> tuple[object, ...]:
    if type(inlets) is not tuple:
        return (type(inlets), id(inlets))
    return tuple(_inlet_snapshot(inlet) for inlet in inlets)


def _tile_snapshot(tile: object) -> tuple[object, ...]:
    if type(tile) is not BorderTile:
        return (type(tile), id(tile))
    return (
        BorderTile,
        _scalar_snapshot(tile.k),
        _scalar_snapshot(tile.high),
        _scalar_snapshot(tile.low),
    )


def _bilateral_port_snapshot(port: object) -> tuple[object, ...] | None:
    if port is None:
        return None
    if type(port) is not BilateralCyclePort:
        return (type(port), id(port))
    return (
        BilateralCyclePort,
        _tile_snapshot(port.source),
        _tile_snapshot(port.target),
        _scalar_snapshot(port.growth),
        _scalar_snapshot(port.low_carry),
        tuple(port.admitted_middle),
    )


def _inlet_snapshot(inlet: object) -> tuple[object, ...]:
    if type(inlet) is not SourceGrowthInlet:
        return (type(inlet), id(inlet))
    return (
        SourceGrowthInlet,
        _scalar_snapshot(inlet.tick),
        _scalar_snapshot(inlet.growth),
        _bilateral_port_snapshot(inlet.bilateral_port),
    )


def _bit(value: int) -> int:
    if type(value) is not int or value not in (0, 1):
        raise ValueError("growth letters must be exact Boolean integers")
    return value


@dataclass(frozen=True, slots=True)
class DirectedGrowthMask:
    """Disjoint K-bit masks for extra and missing growth in paired tapes."""

    window: int
    extra: int
    missing: int

    def __post_init__(self) -> None:
        if (
            type(self.window) is not int
            or not 1 <= self.window <= _MAX_WINDOW
            or type(self.extra) is not int
            or type(self.missing) is not int
            or self.extra < 0
            or self.missing < 0
            or (self.extra | self.missing) >= 1 << self.window
            or self.extra & self.missing
        ):
            raise ValueError("invalid or overlapping signed diagonal masks")

    @classmethod
    def from_growth_words(
        cls, first: tuple[int, ...], second: tuple[int, ...]
    ) -> DirectedGrowthMask:
        if (
            type(first) is not tuple
            or type(second) is not tuple
            or not first
            or len(first) != len(second)
        ):
            raise ValueError("growth windows must be equal, nonempty tuples")
        extra = missing = 0
        for first_bit, second_bit in zip(first, second, strict=True):
            a, b = _bit(first_bit), _bit(second_bit)
            extra = (extra << 1) | int(a == 0 and b == 1)
            missing = (missing << 1) | int(a == 1 and b == 0)
        return cls(len(first), extra, missing)

    @property
    def xor(self) -> int:
        return self.extra | self.missing

    @property
    def signed_window_growth(self) -> int:
        return self.extra.bit_count() - self.missing.bit_count()

    def shift(self, first_growth: int, second_growth: int) -> DirectedGrowthMask:
        a, b = _bit(first_growth), _bit(second_growth)
        mask = (1 << self.window) - 1
        return DirectedGrowthMask(
            self.window,
            ((self.extra << 1) | int(a == 0 and b == 1)) & mask,
            ((self.missing << 1) | int(a == 1 and b == 0)) & mask,
        )


@dataclass(frozen=True, slots=True)
class DirectedDiagonalAction:
    """Finite inlet word with exact growth counts and a K-bit suffix action."""

    window: int
    duration: int
    growth_first: int
    growth_second: int
    suffix_extra: int
    suffix_missing: int

    def __post_init__(self) -> None:
        if (
            type(self.window) is not int
            or not 1 <= self.window <= _MAX_WINDOW
            or type(self.duration) is not int
            or self.duration < 0
            or type(self.growth_first) is not int
            or type(self.growth_second) is not int
            or not 0 <= self.growth_first <= self.duration
            or not 0 <= self.growth_second <= self.duration
            or type(self.suffix_extra) is not int
            or type(self.suffix_missing) is not int
            or min(self.suffix_extra, self.suffix_missing) < 0
            or (self.suffix_extra | self.suffix_missing)
            >= 1 << min(self.window, self.duration)
            or self.suffix_extra & self.suffix_missing
        ):
            raise ValueError("invalid directed diagonal action")

    @classmethod
    def identity(cls, window: int) -> DirectedDiagonalAction:
        return cls(window, 0, 0, 0, 0, 0)

    @classmethod
    def from_inlets(
        cls, first: tuple[int, ...], second: tuple[int, ...], *, window: int
    ) -> DirectedDiagonalAction:
        if type(first) is not tuple or type(second) is not tuple:
            raise TypeError("paired inlet words must be tuples")
        if len(first) != len(second):
            raise ValueError("paired inlet streams must be synchronized")
        action = cls.identity(window)
        for a_raw, b_raw in zip(first, second, strict=True):
            a, b = _bit(a_raw), _bit(b_raw)
            action = action.then(
                cls(
                    window,
                    1,
                    a,
                    b,
                    int(a == 0 and b == 1),
                    int(a == 1 and b == 0),
                )
            )
        return action

    @property
    def signed_growth(self) -> int:
        return self.growth_second - self.growth_first

    def then(self, later: DirectedDiagonalAction) -> DirectedDiagonalAction:
        if type(later) is not DirectedDiagonalAction or self.window != later.window:
            raise ValueError("diagonal actions have different window widths")
        shift = min(later.duration, self.window)
        mask = (1 << self.window) - 1
        return DirectedDiagonalAction(
            self.window,
            self.duration + later.duration,
            self.growth_first + later.growth_first,
            self.growth_second + later.growth_second,
            ((self.suffix_extra << shift) | later.suffix_extra) & mask,
            ((self.suffix_missing << shift) | later.suffix_missing) & mask,
        )

    def apply(self, state: DirectedGrowthMask) -> DirectedGrowthMask:
        if type(state) is not DirectedGrowthMask or state.window != self.window:
            raise ValueError("incompatible diagonal window")
        shift = min(self.duration, self.window)
        mask = (1 << self.window) - 1
        return DirectedGrowthMask(
            self.window,
            ((state.extra << shift) | self.suffix_extra) & mask,
            ((state.missing << shift) | self.suffix_missing) & mask,
        )

    def width_after(self, width_first: int, width_second: int) -> tuple[int, int]:
        if (
            type(width_first) is not int
            or width_first < 1
            or type(width_second) is not int
            or width_second < 1
        ):
            raise ValueError("positive exact source widths required")
        return width_first + self.growth_first, width_second + self.growth_second

    def formal_power(self, repetitions: int) -> DirectedDiagonalAction:
        """Power a supplied inlet word algebraically, without source authority."""
        if type(repetitions) is not int or not 0 <= repetitions <= _MAX_POWER_STEPS:
            raise ValueError("conditional power exceeds its bounded exponent")
        return binary_power(
            self,
            repetitions,
            identity=self.identity(self.window),
            compose=lambda first, later: first.then(later),
        ).value


@dataclass(frozen=True, slots=True)
class SourceGrowthInlet:
    """A growth bit and any source-issued bilateral port at that tick."""

    tick: int
    growth: int
    bilateral_port: BilateralCyclePort | None

    @property
    def possible_high_carries(self) -> tuple[int, ...] | None:
        if self.bilateral_port is None:
            return None
        return tuple(
            sorted(
                {
                    apply_carry_fn(function, self.bilateral_port.low_carry)
                    for function in self.bilateral_port.admitted_middle
                }
            )
        )


def source_growth_inlets(
    certificate: CertifiedBorderGrowth, start: int, count: int
) -> tuple[SourceGrowthInlet, ...]:
    """Read a bounded slice of the certificate's physical inlet/port tape."""
    from .q19_border_control import CertifiedBorderGrowth

    if type(certificate) is not CertifiedBorderGrowth:
        raise TypeError("source growth inlets require a certified border record")
    if (
        type(start) is not int
        or type(count) is not int
        or start < 0
        or count < 0
        or count > _MAX_SOURCE_INLETS
    ):
        raise ValueError("inlet request outside bounded source certificate")
    certificate.validate(certificate.owner, certificate.source)
    return _source_growth_inlets_validated(certificate, start, count)


def _source_bilateral_port(
    certificate: CertifiedBorderGrowth,
    tick: int,
    growth: int,
    source: BorderTile,
    target: BorderTile,
) -> BilateralCyclePort:
    candidate = bilateral_cycle_letter(source, target, growth)
    if tick == 0:
        initial_middle = certificate._initial_middle_transfer(window_digits=source.k)
        if initial_middle is not None:
            if not candidate.admits(initial_middle):
                raise AssertionError(
                    "source border rejects its authenticated initial transfer"
                )
            candidate = BilateralCyclePort(
                candidate.source,
                candidate.target,
                candidate.growth,
                candidate.low_carry,
                (initial_middle,),
            )
    if candidate.growth != growth:
        raise AssertionError("bilateral port contradicts certified growth")
    exact = bilateral_cycle_letter(candidate.source, candidate.target, growth)
    if not set(candidate.admitted_middle) <= set(exact.admitted_middle):
        raise AssertionError("bilateral middle maps lack a valid successor")
    return candidate


def _source_growth_inlets_validated(
    certificate: CertifiedBorderGrowth, start: int, count: int
) -> tuple[SourceGrowthInlet, ...]:
    if (
        type(start) is not int
        or type(count) is not int
        or start < 0
        or count < 0
        or count > _MAX_SOURCE_INLETS
        or start + count > len(certificate.growth_word)
    ):
        raise ValueError("inlet request outside bounded source certificate")
    if count == 0:
        return ()
    result: list[SourceGrowthInlet] = []
    for tick in range(start, start + count):
        growth = certificate.growth_word[tick]
        candidate: BilateralCyclePort | None = None
        source_tile: BorderTile | None = None
        target_tile: BorderTile | None = None
        if (
            tick + 1 < len(certificate.window_tiles)
            and certificate.window_tiles[tick] is not None
            and certificate.window_tiles[tick + 1] is not None
        ):
            source_tile = certificate.window_tiles[tick]
            target_tile = certificate.window_tiles[tick + 1]
            assert source_tile is not None and target_tile is not None
        elif (
            tick + 1 < len(certificate.outer_pairs)
            and certificate.outer_pairs[tick] is not None
            and certificate.outer_pairs[tick + 1] is not None
        ):
            old, new = certificate.outer_pairs[tick : tick + 2]
            assert old is not None and new is not None
            source_tile, target_tile = BorderTile(1, *old), BorderTile(1, *new)
        if source_tile is not None and target_tile is not None:
            candidate = _source_bilateral_port(
                certificate, tick, growth, source_tile, target_tile
            )
        certificate.owner.ledger.bump(
            _metric.REVERSE_Q19_DIRECTED_DIAGONAL_INLET_VISITS
        )
        result.append(SourceGrowthInlet(tick, growth, candidate))
    return tuple(result)


@dataclass(frozen=True, slots=True)
class CertifiedDiagonalComparison:
    """One same-certificate comparison of two finite growth windows."""

    certificate: CertifiedBorderGrowth
    first_start: int
    second_start: int
    initial: DirectedGrowthMask
    action: DirectedDiagonalAction
    first_inlets: tuple[SourceGrowthInlet, ...]
    second_inlets: tuple[SourceGrowthInlet, ...]
    _registry_key: int = field(default=-1, init=False, repr=False, compare=False)

    def _snapshot(self) -> tuple[object, ...]:
        return (
            self.certificate,
            _scalar_snapshot(self.first_start),
            _scalar_snapshot(self.second_start),
            _mask_snapshot(self.initial),
            _action_snapshot(self.action),
            _inlets_snapshot(self.first_inlets),
            _inlets_snapshot(self.second_inlets),
        )

    def _validate(self) -> None:
        from .q19_border_control import CertifiedBorderGrowth

        if type(self.certificate) is not CertifiedBorderGrowth:
            raise ValueError("diagonal comparison has no issued source certificate")
        self.certificate.owner._issuance_registry.validate_diagonal_comparison(self)

    def terminal(self) -> DirectedGrowthMask:
        self._validate()
        return self.action.apply(self.initial)

    def signed_width_delta(self) -> int:
        self._validate()
        return self.action.signed_growth

    def formal_power(self, repetitions: int) -> DirectedDiagonalAction:
        self._validate()
        return self.action.formal_power(repetitions)


def _issue_diagonal_comparison(
    certificate: CertifiedBorderGrowth,
    first_start: int,
    second_start: int,
    window: int,
    continuation: int,
) -> CertifiedDiagonalComparison:
    from .q19_border_control import CertifiedBorderGrowth

    if type(certificate) is not CertifiedBorderGrowth:
        raise TypeError("diagonal comparison requires a source certificate")
    if (
        type(first_start) is not int
        or type(second_start) is not int
        or type(window) is not int
        or type(continuation) is not int
        or first_start < 0
        or second_start < 0
        or not 1 <= window <= _MAX_WINDOW
        or continuation < 0
        or continuation > _MAX_SOURCE_INLETS
    ):
        raise ValueError("invalid bounded certified diagonal demand")
    certificate.validate(certificate.owner, certificate.source)
    first_stop = first_start + window + continuation
    second_stop = second_start + window + continuation
    if max(first_stop, second_stop) > len(certificate.growth_word):
        raise ValueError("diagonal inlet not fully authorized by source certificate")

    owner = certificate.owner
    inlet_bound = 2 * continuation
    # Snapshot nodes count the fixed proof/action header plus, per inlet, its
    # row slot and snapshot; a bilateral port adds 42 tuple/slot nodes and at
    # most three admitted carry maps. There are two independently built rows.
    snapshot_nodes_bound = 56 + 57 * inlet_bound
    # This is the matching maximum for the retained record, immutable snapshot
    # and issuance pair, before OwnedMemo's one-node metadata wrapper.
    retained_nodes_bound = 81 + 80 * inlet_bound
    scratch_nodes = 16 + 4 * window + 16 * continuation + snapshot_nodes_bound
    owner.ledger.check_capacity(entries=1, nodes=scratch_nodes + retained_nodes_bound)
    with owner.ledger.reservation(owner._scratch_owner, nodes=scratch_nodes):
        initial = DirectedGrowthMask.from_growth_words(
            certificate.growth_word[first_start : first_start + window],
            certificate.growth_word[second_start : second_start + window],
        )
        first_inlets = _source_growth_inlets_validated(
            certificate, first_start + window, continuation
        )
        second_inlets = _source_growth_inlets_validated(
            certificate, second_start + window, continuation
        )
        action = DirectedDiagonalAction.from_inlets(
            tuple(inlet.growth for inlet in first_inlets),
            tuple(inlet.growth for inlet in second_inlets),
            window=window,
        )
        packet = object.__new__(CertifiedDiagonalComparison)
        for name, value in (
            ("certificate", certificate),
            ("first_start", first_start),
            ("second_start", second_start),
            ("initial", initial),
            ("action", action),
            ("first_inlets", first_inlets),
            ("second_inlets", second_inlets),
            ("_registry_key", -1),
        ):
            object.__setattr__(packet, name, value)
        registry = owner._issuance_registry
        key = registry.allocate_diagonal_comparison_key()
        object.__setattr__(packet, "_registry_key", key)
        registry.retain_diagonal_comparison(key, packet)
        try:
            packet._validate()
        except BaseException:
            registry.discard_diagonal_comparison(key, packet)
            raise
        return packet


def certify_diagonal_comparison(
    certificate: CertifiedBorderGrowth,
    *,
    first_start: int,
    second_start: int,
    window: int = 9,
    continuation: int = 0,
) -> CertifiedDiagonalComparison:
    """Build P/N masks from two slices of one physical growth certificate."""
    return _issue_diagonal_comparison(
        certificate,
        first_start,
        second_start,
        window,
        continuation,
    )


@dataclass(frozen=True, slots=True)
class WidthGrowthBounds:
    """Universal minimum/maximum width increments over a finite horizon."""

    steps: int
    min_growth: int
    max_growth: int
    reachable_border_states: int
    entry_width: int
    relation_edges: int
    composition_pairs: int
    peak_relation_cells: int
    constructed_border_states: int

    @property
    def exact_growth(self) -> int | None:
        return self.min_growth if self.min_growth == self.max_growth else None

    @property
    def exact_width(self) -> int | None:
        growth = self.exact_growth
        return None if growth is None else self.entry_width + growth


class UniversalBorderWidthPower:
    """Request-local sparse min/max powers of the bilateral border relation."""

    def __init__(
        self,
        source: BorderTile,
        *,
        entry_width: int,
        max_states: int = 500,
        max_edges: int = 1500,
        max_composition_pairs: int = 2_000_000,
        max_relation_cells: int = 250_000,
        on_work: Callable[[BorderWidthWork, int], None] | None = None,
        on_memory_change: Callable[[int, int], None] | None = None,
    ) -> None:
        _validate_width_limits(
            source,
            entry_width,
            max_states,
            max_edges,
            max_composition_pairs,
            max_relation_cells,
        )
        if on_work is not None and not callable(on_work):
            raise TypeError("work accounting callback must be callable")
        if on_memory_change is not None and not callable(on_memory_change):
            raise TypeError("memory accounting callback must be callable")
        self.source = source
        self.entry_width = entry_width
        self._caps = (
            max_states,
            max_edges,
            max_composition_pairs,
            max_relation_cells,
        )
        self._on_work = on_work
        self._on_memory_change = on_memory_change
        self._states: list[BorderTile] = []
        self._state_index: dict[BorderTile, int] = {}
        self._base_relation: tuple[dict[int, tuple[int, int]], ...] = ()
        self._edge_count = 0
        self._relation_cells = 0
        self._composition_pairs = 0
        self._peak_relation_cells = 0
        self._built = False

    @property
    def states(self) -> tuple[BorderTile, ...]:
        return tuple(self._states)

    def _charge(self, kind: BorderWidthWork, amount: int = 1) -> None:
        if self._on_work is not None:
            self._on_work(kind, amount)

    def _memory_change(self, amount: int) -> None:
        """Charge one state/cell before insertion and release it on reclamation."""
        if self._on_memory_change is not None:
            self._on_memory_change(amount, amount)

    def _build_universal_graph(self) -> None:
        max_states, max_edges, _, max_cells = self._caps
        # The root is real retained state. Reserve it before installing the
        # state list, index, and empty adjacency row.
        self._memory_change(1)
        self._states = [self.source]
        self._state_index = {self.source: 0}
        building_rows: list[dict[int, tuple[int, int]]] = [{}]
        self._charge(BorderWidthWork.STATE)
        cursor = 0
        while cursor < len(self._states):
            self._charge(BorderWidthWork.STATE_VISIT)
            tile = self._states[cursor]
            row = building_rows[cursor]
            cursor += 1
            port = border_bilateral_port(tile)
            seen: set[tuple[BorderTile, int]] = set()
            for alternative in port.alternatives:
                edge = (alternative.target, alternative.growth)
                if edge in seen:
                    continue
                seen.add(edge)
                target = alternative.target
                target_index = self._state_index.get(target)
                if self._edge_count >= max_edges:
                    raise BorderWidthPowerRefused(
                        "reachable border graph exceeds the edge budget"
                    )
                if target_index is None:
                    if len(self._states) >= max_states:
                        raise BorderWidthPowerRefused(
                            "reachable border graph exceeds the state budget"
                        )
                    if self._relation_cells >= max_cells:
                        raise BorderWidthPowerRefused(
                            "base relation exceeds the retained-cell budget"
                        )
                    target_index = len(self._states)
                    self._memory_change(1)
                    self._state_index[target] = target_index
                    self._states.append(target)
                    building_rows.append({})
                    self._charge(BorderWidthWork.STATE)
                old = row.get(target_index)
                if old is None:
                    if self._relation_cells >= max_cells:
                        raise BorderWidthPowerRefused(
                            "base relation exceeds the retained-cell budget"
                        )
                    self._memory_change(1)
                    row[target_index] = (alternative.growth, alternative.growth)
                    self._relation_cells += 1
                    self._charge(BorderWidthWork.RELATION_CELL)
                else:
                    row[target_index] = (
                        min(old[0], alternative.growth),
                        max(old[1], alternative.growth),
                    )
                self._edge_count += 1
                self._charge(BorderWidthWork.EDGE)
            self._peak_relation_cells = max(
                self._peak_relation_cells, self._relation_cells
            )
        self._base_relation = tuple(building_rows)
        self._built = True

    def _compose_relation(
        self,
        left: tuple[dict[int, tuple[int, int]], ...],
        right: tuple[dict[int, tuple[int, int]], ...],
        *,
        active_cells: int,
    ) -> tuple[dict[int, tuple[int, int]], ...]:
        _, _, max_pairs, max_cells = self._caps
        result_rows: list[dict[int, tuple[int, int]]] = []
        output_cells = 0
        left_cells = sum(len(row) for row in left)
        retained_base_cells = 0 if left is self._base_relation else self._relation_cells
        for left_row in left:
            output_row: dict[int, tuple[int, int]] = {}
            for middle, (left_min, left_max) in left_row.items():
                for target, (right_min, right_max) in right[middle].items():
                    if self._composition_pairs >= max_pairs:
                        raise BorderWidthPowerRefused(
                            "relation composition exceeds the pair budget"
                        )
                    self._composition_pairs += 1
                    self._charge(BorderWidthWork.COMPOSITION_PAIR)
                    candidate = left_min + right_min, left_max + right_max
                    previous = output_row.get(target)
                    if previous is None:
                        if (
                            retained_base_cells
                            + left_cells
                            + output_cells
                            + 1
                            + active_cells
                            > max_cells
                        ):
                            raise BorderWidthPowerRefused(
                                "relation square exceeds the retained-cell budget"
                            )
                        self._memory_change(1)
                        output_row[target] = candidate
                        output_cells += 1
                        self._charge(BorderWidthWork.RELATION_CELL)
                    else:
                        output_row[target] = (
                            min(previous[0], candidate[0]),
                            max(previous[1], candidate[1]),
                        )
            result_rows.append(output_row)
        self._peak_relation_cells = max(
            self._peak_relation_cells,
            retained_base_cells + left_cells + output_cells + active_cells,
        )
        return tuple(result_rows)

    def _apply_relation(
        self,
        active: dict[int, tuple[int, int]],
        relation: tuple[dict[int, tuple[int, int]], ...],
    ) -> dict[int, tuple[int, int]]:
        _, _, max_pairs, max_cells = self._caps
        next_active: dict[int, tuple[int, int]] = {}
        relation_cells = sum(len(row) for row in relation)
        retained_base_cells = (
            0 if relation is self._base_relation else self._relation_cells
        )
        for middle, (active_min, active_max) in active.items():
            for target, (step_min, step_max) in relation[middle].items():
                if self._composition_pairs >= max_pairs:
                    raise BorderWidthPowerRefused(
                        "active relation composition exceeds the pair budget"
                    )
                self._composition_pairs += 1
                self._charge(BorderWidthWork.COMPOSITION_PAIR)
                candidate = active_min + step_min, active_max + step_max
                previous = next_active.get(target)
                if previous is None:
                    if (
                        retained_base_cells
                        + relation_cells
                        + len(active)
                        + len(next_active)
                        + 1
                        > max_cells
                    ):
                        raise BorderWidthPowerRefused(
                            "active relation exceeds the retained-cell budget"
                        )
                    self._memory_change(1)
                    next_active[target] = candidate
                    self._charge(BorderWidthWork.RELATION_CELL)
                else:
                    next_active[target] = (
                        min(previous[0], candidate[0]),
                        max(previous[1], candidate[1]),
                    )
        self._peak_relation_cells = max(
            self._peak_relation_cells,
            retained_base_cells + relation_cells + len(active) + len(next_active),
        )
        return next_active

    def bounds(self, steps: int) -> WidthGrowthBounds:
        if type(steps) is not int or not 0 <= steps <= _MAX_POWER_STEPS:
            raise ValueError("width exponent exceeds its finite power budget")
        if self.entry_width < 2 * self.source.k + 1:
            raise BorderWidthPowerRefused(
                "source width does not separate the requested border windows"
            )
        if steps == 0:
            return WidthGrowthBounds(0, 0, 0, 1, self.entry_width, 0, 0, 0, 0)
        if not self._built:
            self._build_universal_graph()
        _, _, _, max_cells = self._caps
        power = self._base_relation
        if self._relation_cells + 1 > max_cells:
            raise BorderWidthPowerRefused(
                "initial relation and active state exceed the cell budget"
            )
        self._memory_change(1)
        active: dict[int, tuple[int, int]] = {0: (0, 0)}
        exponent = steps
        while exponent:
            if exponent & 1:
                old_active_cells = len(active)
                next_active = self._apply_relation(active, power)
                active = next_active
                del next_active
                if old_active_cells:
                    self._memory_change(-old_active_cells)
            exponent >>= 1
            if exponent:
                active_cells = len(active)
                prior_power = power
                prior_power_cells = sum(len(row) for row in prior_power)
                next_power = self._compose_relation(
                    power, power, active_cells=active_cells
                )
                power = next_power
                del next_power
                if prior_power is not self._base_relation:
                    del prior_power
                    if prior_power_cells:
                        self._memory_change(-prior_power_cells)
        if not active:
            raise AssertionError("a total border relation lost every path")
        return WidthGrowthBounds(
            steps,
            min(value[0] for value in active.values()),
            max(value[1] for value in active.values()),
            len(active),
            self.entry_width,
            self._edge_count,
            self._composition_pairs,
            self._peak_relation_cells,
            len(self._states),
        )


def _validate_width_limits(
    source: BorderTile,
    entry_width: int,
    max_states: int,
    max_edges: int,
    max_composition_pairs: int,
    max_relation_cells: int,
) -> None:
    if type(source) is not BorderTile or source.k > 12:
        raise ValueError("universal width relation requires a certified K<=12 tile")
    if type(entry_width) is not int or entry_width < 1:
        raise ValueError("an exact positive source width is required")
    limits = (
        (max_states, 1, _MAX_STATES),
        (max_edges, 1, _MAX_EDGES),
        (max_composition_pairs, 1, _MAX_COMPOSITION_PAIRS),
        (max_relation_cells, 1, _MAX_RELATION_CELLS),
    )
    if any(
        type(value) is not int or not lower <= value <= upper
        for value, lower, upper in limits
    ):
        raise ValueError("width relation caps exceed their bounded request envelope")


__all__ = [
    "BorderWidthPowerRefused",
    "CertifiedDiagonalComparison",
    "DirectedDiagonalAction",
    "DirectedGrowthMask",
    "SourceGrowthInlet",
    "UniversalBorderWidthPower",
    "WidthGrowthBounds",
    "certify_diagonal_comparison",
    "source_growth_inlets",
]
