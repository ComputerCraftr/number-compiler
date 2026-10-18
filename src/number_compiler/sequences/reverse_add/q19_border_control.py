"""Source-certified finite reverse/add growth tapes from edge relations.

The k-digit prefix/suffix relation nondeterministically includes *both*
interior carry values after its first exact source transition. Whenever all
outcomes have the same growth bit, that bit is universally certified without
constructing any intermediate Q19 pair occurrence. The original input uses
its exact source digits; a later issued pair root supplies the already-issued
width transition and exact normalized output digits for the next edge step.

This theorem gives FINITE, source-bound control prefixes; it is not a proof
that the observed word continues periodically or controls arbitrary depths.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator
from contextlib import contextmanager
from dataclasses import dataclass, field
from itertools import chain
from typing import TYPE_CHECKING, Literal

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

from ._q19_issuance import issue_q19_record
from .border_carry_safety import (
    BilateralCarryAlternative,
    BilateralCyclePort,
    BorderTile,
    ConditionalBorderCycle,
    bilateral_cycle_letter,
    border_bilateral_port,
    border_carry_port,
    conditional_return_from_trace,
)
from .diagonal_growth_bank import BorderWidthWork

if TYPE_CHECKING:
    from .conditional_f5_macro import SourceCertifiedF5Macro
    from .diagonal_growth_bank import (
        CertifiedDiagonalComparison,
        WidthGrowthBounds,
    )
    from .macro_conditioned_harmonics import AuthenticatedMacroWindow
    from .q19_controlled_gt_bank import SourceGuardedGTBankAction
    from .q19_occurrence import ReversePairOutputOccurrence
    from .q19_output import ReversePairQ19OutputOwner
    from .q19_word_summary import _Q19
    from .temporal_inward_constraints import ReverseInwardConstraints
    from .temporal_ring_harmonics import ReverseAddTemporalRingBank

_ISSUER = object()
_BORDER_WIDTH_METRIC_KEYS = {
    BorderWidthWork.STATE_VISIT: _reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_STATE_VISITS,
    BorderWidthWork.STATE: _reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_STATES,
    BorderWidthWork.EDGE: _reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_EDGES,
    BorderWidthWork.COMPOSITION_PAIR: (
        _reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_COMPOSITION_PAIRS
    ),
    BorderWidthWork.RELATION_CELL: (
        _reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_RELATION_CELLS
    ),
}


@contextmanager
def _border_width_scratch(
    owner: ReversePairQ19OutputOwner,
) -> Iterator[Callable[[int, int], None]]:
    """Dynamically reserve the live graph frontier on its owner ledger."""
    entries = nodes = 0

    def adjust(entry_delta: int, node_delta: int) -> None:
        nonlocal entries, nodes
        if entry_delta >= 0 and node_delta >= 0:
            owner.ledger.reserve(
                owner._scratch_owner, entries=entry_delta, nodes=node_delta
            )
            entries += entry_delta
            nodes += node_delta
            return
        if entry_delta > 0 or node_delta > 0:
            raise ValueError("scratch reservation deltas must share a sign")
        release_entries, release_nodes = -entry_delta, -node_delta
        if release_entries > entries or release_nodes > nodes:
            raise RuntimeError("width scratch release exceeds its reservation")
        owner.ledger.release(
            owner._scratch_owner,
            entries=release_entries,
            nodes=release_nodes,
        )
        entries -= release_entries
        nodes -= release_nodes

    try:
        yield adjust
    finally:
        if entries or nodes:
            owner.ledger.release(owner._scratch_owner, entries=entries, nodes=nodes)


def _typed_scalar_snapshot(value: object) -> tuple[object, object]:
    immutable_types = (int, bool, str, bytes, type(None))
    if type(value) in immutable_types:
        return type(value), value
    return type(value), id(value)


def _tuple_snapshot(value: object) -> tuple[object, ...]:
    if type(value) is not tuple:
        return type(value), id(value)
    return tuple, tuple(_typed_scalar_snapshot(item) for item in value)


def _outer_pairs_snapshot(value: object) -> tuple[object, ...]:
    if type(value) is not tuple:
        return type(value), id(value)
    pairs: list[object] = []
    for pair in value:
        if type(pair) is tuple:
            pairs.append((tuple, tuple(_typed_scalar_snapshot(item) for item in pair)))
        else:
            pairs.append(_typed_scalar_snapshot(pair))
    return tuple, tuple(pairs)


def _window_tile_snapshot(value: object) -> tuple[object, ...]:
    if type(value) is not BorderTile:
        return _typed_scalar_snapshot(value)
    return (
        BorderTile,
        _typed_scalar_snapshot(value.k),
        _typed_scalar_snapshot(value.high),
        _typed_scalar_snapshot(value.low),
    )


def _window_tiles_snapshot(value: object) -> tuple[object, ...]:
    if type(value) is not tuple:
        return type(value), id(value)
    return tuple, tuple(_window_tile_snapshot(tile) for tile in value)


class BoundaryControlNotAuthorized(ValueError):
    """The finite boundary relation cannot certify every requested event."""


@dataclass(frozen=True, slots=True)
class CertifiedBorderGrowth:
    """Exact physical growth word universally forced by the k-digit relation."""

    owner: ReversePairQ19OutputOwner
    source: ReversePairOutputOccurrence
    growth_word: tuple[int, ...]
    window_digits: int
    max_visited_states: int
    source_pair_inspections: int = 0
    outer_pairs: tuple[tuple[int, int] | None, ...] = ()
    window_tiles: tuple[BorderTile | None, ...] = ()
    physical_growth_certified: Literal[True] = True
    full_integer_certified: Literal[False] = False
    _seal: object = field(default=None, repr=False, compare=False)
    _binding: tuple[object, ...] = field(default=(), repr=False, compare=False)

    def _snapshot(self) -> tuple[object, ...]:
        return (
            self.owner,
            self.source,
            _tuple_snapshot(self.growth_word),
            _typed_scalar_snapshot(self.window_digits),
            _typed_scalar_snapshot(self.max_visited_states),
            _typed_scalar_snapshot(self.source_pair_inspections),
            _outer_pairs_snapshot(self.outer_pairs),
            _window_tiles_snapshot(self.window_tiles),
            _typed_scalar_snapshot(self.physical_growth_certified),
            _typed_scalar_snapshot(self.full_integer_certified),
        )

    def __post_init__(self) -> None:
        if (
            self._seal is not _ISSUER
            or self._binding != self._snapshot()
            or type(self.max_visited_states) is not int
            or self.max_visited_states < 1
            or type(self.source_pair_inspections) is not int
            or self.source_pair_inspections < 0
            or type(self.outer_pairs) is not tuple
            or (self.outer_pairs and len(self.outer_pairs) != len(self.growth_word) + 1)
            or any(
                pair is not None
                and (
                    type(pair) is not tuple
                    or len(pair) != 2
                    or type(pair[0]) is not int
                    or type(pair[1]) is not int
                    or not 1 <= pair[0] <= 9
                    or not 0 <= pair[1] <= 9
                )
                for pair in self.outer_pairs
            )
            or type(self.window_tiles) is not tuple
            or (
                self.window_tiles
                and len(self.window_tiles) != len(self.growth_word) + 1
            )
            or any(
                tile is not None
                and (type(tile) is not BorderTile or tile.k != self.window_digits)
                for tile in self.window_tiles
            )
            or self.physical_growth_certified is not True
            or self.full_integer_certified is not False
        ):
            raise ValueError(
                "border growth certificate must be issued by a live Q19 owner"
            )
        self.owner._issuance_registry.validate_border(self)

    @property
    def final_width(self) -> int:
        """Exact future integer width for the finite certified growth tape."""
        self.validate(self.owner, self.source)
        return self.source.pair_width + sum(self.growth_word)

    def validate(
        self, owner: ReversePairQ19OutputOwner, source: ReversePairOutputOccurrence
    ) -> None:
        if owner is not self.owner or source is not self.source:
            raise ValueError("border growth certificate belongs to a different source")
        if self._seal is not _ISSUER or self._binding != self._snapshot():
            raise ValueError("border growth certificate was changed")
        owner._issuance_registry.validate_border(self)
        owner.validate_issued_occurrence(source)

    def forced_leading_carry_ports(self) -> tuple[tuple[int, ...] | None, ...]:
        """Return only source-issued MSD carry constraints for adjacent borders."""
        self.validate(self.owner, self.source)
        if not self.outer_pairs:
            return (None,) * len(self.growth_word)
        output: list[tuple[int, ...] | None] = []
        for old, new, growth in zip(
            self.outer_pairs[:-1], self.outer_pairs[1:], self.growth_word, strict=True
        ):
            if old is None or new is None:
                output.append(None)
                continue
            port = border_carry_port(BorderTile(1, *old))
            target = BorderTile(1, *new)
            allowed = tuple(
                edge.carry_in
                for edge in port.edges
                if edge.target == target and edge.growth == growth
            )
            if not allowed:
                raise AssertionError(
                    "certified outer border violates its carry relation"
                )
            output.append(allowed)
        return tuple(output)

    def conditional_outer_return(self) -> ConditionalBorderCycle:
        """Return one finite, owner-certified outer-border return.

        This exposes only the conditional one-digit port cycle. It does not
        certify that the inner Q19 source repeats or authorize a second return.
        """
        self.validate(self.owner, self.source)
        if (
            not self.outer_pairs
            or any(pair is None for pair in self.outer_pairs)
            or self.outer_pairs[0] != self.outer_pairs[-1]
        ):
            raise BoundaryControlNotAuthorized(
                "a complete closed outer-border trace is not certified"
            )
        pairs = tuple(pair for pair in self.outer_pairs if pair is not None)
        try:
            return conditional_return_from_trace(pairs, self.growth_word)
        except ValueError as exc:
            raise BoundaryControlNotAuthorized(
                "certified outer trace is not a valid conditional return"
            ) from exc

    def conditional_f5_macro_action(
        self,
        *,
        start: int = 0,
        steps: int | None = None,
        z: int = 2,
    ) -> SourceCertifiedF5Macro:
        """Build an exact F5 action for one closed source-certified trace slice.

        The returned action preserves unknown carry-cochain corrections as
        unresolved inputs.  Its algebraic repeat operation is conditional and
        does not upgrade this finite border certificate to future authority.
        """
        self.validate(self.owner, self.source)
        from .conditional_f5_macro import SourceCertifiedF5Macro

        try:
            return SourceCertifiedF5Macro.from_certificate(
                self, start=start, steps=steps, z=z
            )
        except ValueError as exc:
            raise BoundaryControlNotAuthorized(str(exc)) from exc

    def bilateral_carry_ports(self) -> tuple[BilateralCyclePort | None, ...]:
        """Couple low overflow to every admissible source-middle transfer."""
        self.validate(self.owner, self.source)
        if not self.outer_pairs:
            return (None,) * len(self.growth_word)
        result: list[BilateralCyclePort | None] = []
        # A one-digit outer pair has a different physical middle interval from
        # this certificate's K-digit window; derive the exact K=1 transfer.
        initial_middle = self._initial_middle_transfer(window_digits=1)
        for index, (old, new, growth) in enumerate(
            zip(
                self.outer_pairs[:-1],
                self.outer_pairs[1:],
                self.growth_word,
                strict=True,
            )
        ):
            if old is None or new is None:
                result.append(None)
            else:
                port = bilateral_cycle_letter(
                    BorderTile(1, *old), BorderTile(1, *new), growth
                )
                if index == 0 and initial_middle is not None:
                    if not port.admits(initial_middle):
                        raise AssertionError(
                            "issued first border edge rejects its Q19 middle transfer"
                        )
                    port = BilateralCyclePort(
                        port.source,
                        port.target,
                        port.growth,
                        port.low_carry,
                        (initial_middle,),
                    )
                result.append(port)
        return tuple(result)

    def bilateral_window_ports(self) -> tuple[BilateralCyclePort | None, ...]:
        """Coupled ports for whole K-windows when the finite tile is unique."""
        self.validate(self.owner, self.source)
        if not self.window_tiles:
            return (None,) * len(self.growth_word)
        initial_middle = self._initial_middle_transfer()
        result: list[BilateralCyclePort | None] = []
        for index, (old, new, growth) in enumerate(
            zip(
                self.window_tiles[:-1],
                self.window_tiles[1:],
                self.growth_word,
                strict=True,
            )
        ):
            if old is None or new is None:
                result.append(None)
                continue
            port = bilateral_cycle_letter(old, new, growth)
            if index == 0 and initial_middle is not None:
                if not port.admits(initial_middle):
                    raise AssertionError(
                        "issued first window edge rejects its Q19 middle transfer"
                    )
                port = BilateralCyclePort(
                    port.source,
                    port.target,
                    port.growth,
                    port.low_carry,
                    (initial_middle,),
                )
            result.append(port)
        return tuple(result)

    def directed_growth_diagonal(
        self,
        first_start: int,
        second_start: int,
        *,
        window: int = 9,
        continuation: int = 0,
    ) -> CertifiedDiagonalComparison:
        """Compare two finite slices of this exact source growth tape."""
        from .diagonal_growth_bank import certify_diagonal_comparison

        return certify_diagonal_comparison(
            self,
            first_start=first_start,
            second_start=second_start,
            window=window,
            continuation=continuation,
        )

    def universal_border_width_bounds(
        self,
        steps: int,
        *,
        max_states: int = 500,
        max_edges: int = 1500,
        max_composition_pairs: int = 2_000_000,
        max_relation_cells: int = 250_000,
    ) -> WidthGrowthBounds:
        """Bound width for all bilateral middle maps at a finite horizon.

        The query is available only at the original source root, whose border
        tile and exact width are admitted together. It never reuses a later
        Q19 root after that root's entry transition was consumed.
        """
        from .diagonal_growth_bank import (
            BorderWidthPowerRefused,
            UniversalBorderWidthPower,
        )

        self.validate(self.owner, self.source)
        self.owner.ledger.bump(
            _reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_POWER_REQUESTS
        )
        if self.source is not self.owner.initial:
            self.owner.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_POWER_REFUSALS
            )
            raise BorderWidthPowerRefused(
                "later issued Q19 root has an already-consumed entry transition"
            )
        if not self.window_tiles or self.window_tiles[0] is None:
            self.owner.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_POWER_REFUSALS
            )
            raise BorderWidthPowerRefused(
                "source-root certificate has no exact admitted entry tile"
            )

        def charge(kind: BorderWidthWork, amount: int) -> None:
            self.owner.ledger.bump(_BORDER_WIDTH_METRIC_KEYS[kind], amount)

        try:
            with _border_width_scratch(self.owner) as adjust_memory:
                power = UniversalBorderWidthPower(
                    self.window_tiles[0],
                    entry_width=self.source.pair_width,
                    max_states=max_states,
                    max_edges=max_edges,
                    max_composition_pairs=max_composition_pairs,
                    max_relation_cells=max_relation_cells,
                    on_work=charge,
                    on_memory_change=adjust_memory,
                )
                try:
                    result = power.bounds(steps)
                finally:
                    # Drop all request-local sparse rows before the context
                    # releases their ledger reservation, including on refusal.
                    del power
                return result
        except (BorderWidthPowerRefused, BlockContextBudgetExceeded):
            self.owner.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_POWER_REFUSALS
            )
            raise

    def inward_temporal_constraints(
        self,
        *,
        max_cells: int = 16384,
        include_source_pairs: bool = False,
        include_source_digits: bool = False,
        source_pair_prefix: int = 0,
        max_modular_digits: int = 128,
    ) -> ReverseInwardConstraints:
        """Join NC16 border, bilateral carry, F5 and modular ports *across time*.

        The first growth bit of a later Q19 occurrence was already applied
        to issue that occurrence. It is not replayed as a future transition.
        A finite constraint fixed point never certifies a temporal repetition.
        """
        from .q19_conditional_stencil import GuardedPairStencil
        from .temporal_inward_constraints import ReverseInwardConstraints

        self.validate(self.owner, self.source)
        if type(max_modular_digits) is not int or max_modular_digits < 0:
            raise ValueError("invalid modular-source digit budget")
        if type(source_pair_prefix) is not int or source_pair_prefix < 0:
            raise ValueError("invalid source-pair prefix")
        later = self.source is not self.owner.initial
        skip = int(later)
        w = self.source.output_width if later else self.source.pair_width
        growth = self.growth_word[skip:]
        widths = [w]
        for g in growth:
            widths.append(widths[-1] + g)
        system = ReverseInwardConstraints(
            tuple(widths),
            max_cells=max_cells,
            on_middle_filter_visit=lambda: self.owner.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_INWARD_SYMMETRIC_FILTER_VALUE_VISITS
            ),
        )

        def source_digits() -> tuple[int, ...]:
            if later:
                return tuple(self.owner.digit(self.source, i) for i in range(w))
            return self.owner._digits

        digits = None
        if include_source_digits or w <= max_modular_digits:
            digits = source_digits()
        if include_source_digits:
            assert digits is not None
            system.constrain_prefix(0, "".join(str(d) for d in reversed(digits)))
        if source_pair_prefix > (w + 1) // 2:
            raise ValueError("source-pair probe reaches beyond center")
        if include_source_pairs or source_pair_prefix:
            count = (w + 1) // 2 if include_source_pairs else source_pair_prefix
            stencil = (
                GuardedPairStencil.from_occurrence(self.owner, self.source)
                if later
                else None
            )
            for i in range(count):
                pair = (
                    stencil.cell_at(self.owner, i).coefficient
                    if stencil
                    else self.owner._pair_value_at(self.source, i)
                )
                system.constrain_pair(0, i, pair)
        if self.window_tiles:
            for i, tile in enumerate(self.window_tiles[skip:]):
                if tile is None or i >= len(widths):
                    continue
                if widths[i] < 2 * tile.k + 1:
                    continue
                system.constrain_prefix(i, str(tile.high).zfill(tile.k))
                system.constrain_suffix(i, str(tile.low).zfill(tile.k))
                # If the issued tiles cover everything except the central
                # 1/2 digits, their ORDERED exterior residue is exact. The
                # Q19 pair-sum fold alone could not supply this orientation.
                if widths[i] - 2 * tile.k in (1, 2):
                    external = (
                        tile.high * pow(10, widths[i] - tile.k, 99) + tile.low
                    ) % 99
                    system.constrain_exterior_residue99(i, external)
        if self.outer_pairs:
            for i, outer_pair in enumerate(self.outer_pairs[skip:]):
                if outer_pair is None or i >= len(widths):
                    continue
                system.constrain_digit(i, 0, outer_pair[0])
                system.constrain_digit(i, widths[i] - 1, outer_pair[1])
        # Join an AUTHENTICATED global Q19 SLP cochain to the same finite
        # digits/carry/center solver. Do not read a large source's interior:
        # the pair SLP gives its next reverse/add residue directly even when
        # its even-width *current* residue cannot be recovered from pair sums.
        # A later Q19 occurrence already represents that next integer.
        residue: int | None = None
        next_residue: int | None = None
        if digits is not None:
            residue = sum(d * pow(10, i, 99) for i, d in enumerate(digits)) % 99
        elif max_modular_digits:
            pair_sum99 = self.owner.radix19_cochain(self.source, z=10, modulus=99).pairs
            if later:
                residue = pair_sum99
            elif w & 1:
                residue = 50 * pair_sum99 % 99
            # Even original-width pair sums lose the ordered mod-11 sign.
            # They DO give X_1 exactly, without a source-digit scan.
            else:
                next_residue = pair_sum99
        if max_modular_digits or digits is not None:
            for t, width in enumerate(widths):
                if residue is not None:
                    for modulus in (9, 11, 99):
                        system.constrain_residue(t, modulus, residue % modulus)
                    # The modulo-198 lift needs one certified parity bit.
                    # It is not another cyclotomic multiplication action.
                    parity: int | None = None
                    if t == 0:
                        if digits is not None:
                            parity = digits[0] % 2
                        elif later:
                            parity = self.owner.digit(self.source, 0) % 2
                    else:
                        phase = skip + t - 1
                        if self.outer_pairs and phase < len(self.outer_pairs):
                            outer_pair = self.outer_pairs[phase]
                            if outer_pair is not None:
                                hi, lo = outer_pair
                                parity = (hi + lo) % 2
                    if parity is not None:
                        system.constrain_residue(
                            t, 198, residue + 99 * ((parity - residue) % 2)
                        )
                if t + 1 < len(widths):
                    if residue is not None:
                        residue = residue * (2 if width & 1 else 11) % 99
                    elif t == 0 and not later and w % 2 == 0:
                        if next_residue is None:
                            raise AssertionError("missing ordered next residue")
                        residue = next_residue
        # Correlate the issued K=1 and K>1 borders BEFORE the fixed point.
        # This restores NC16's low carry <-> symmetric middle reset <-> high
        # carry factor for every caller, not just the ring diagnostics.
        coarse = self.bilateral_carry_ports()
        windows = self.bilateral_window_ports()
        for physical in range(skip, len(self.growth_word)):
            t = physical - skip
            for port in (coarse[physical], windows[physical]):
                if port is not None and widths[t] >= 2 * port.source.k + 1:
                    system.constrain_bilateral_port(t, port)
        return system

    def macro_conditioned_harmonics(
        self, *, start: int = 0, duration: int | None = None
    ) -> AuthenticatedMacroWindow:
        """Extract an authenticated finite cycle with its own F5 harmonics."""
        from .macro_conditioned_harmonics import authorize_finite_macro_window

        self.validate(self.owner, self.source)
        return authorize_finite_macro_window(self, start=start, duration=duration)

    def temporal_ring_bank(
        self,
        *,
        start: int = 0,
        duration: int | None = None,
        positions: tuple[int, ...] = (0,),
        source_pair_prefix: int = 0,
        include_source_digits: bool = False,
        max_cells: int = 16384,
        bank_action: SourceGuardedGTBankAction | None = None,
    ) -> ReverseAddTemporalRingBank:
        """Issue a finite two-sided macro/inner-position output action."""
        from .temporal_ring_harmonics import authorize_temporal_ring_bank

        return authorize_temporal_ring_bank(
            self,
            start=start,
            duration=duration,
            positions=positions,
            source_pair_prefix=source_pair_prefix,
            include_source_digits=include_source_digits,
            max_cells=max_cells,
            bank_action=bank_action,
        )

    def initial_two_sided_carry(self) -> BilateralCarryAlternative | None:
        """Check the original low-overflow/middle/high seam from its Q19 SLP."""
        self.validate(self.owner, self.source)
        if self.source is not self.owner.initial:
            return None
        width = self.source.pair_width
        k = self.window_digits
        transfer = self._initial_middle_transfer()
        if transfer is None:
            return None
        digits = self.owner._digits
        high = sum(digits[width - 1 - i] * 10 ** (k - 1 - i) for i in range(k))
        low = sum(digits[i] * 10**i for i in range(k))
        result = border_bilateral_port(BorderTile(k, high, low)).for_middle(transfer)
        if self.growth_word and result.growth != self.growth_word[0]:
            raise AssertionError("source border growth contradicts its middle transfer")
        return result

    def _initial_middle_transfer(
        self, *, window_digits: int | None = None
    ) -> CarryFn | None:
        """Return the compressed source-owned middle function, when available."""
        if self.source is not self.owner.initial:
            return None
        width = self.source.pair_width
        k = self.window_digits if window_digits is None else window_digits
        if width < 2 * k + 1:
            return None
        middle = _initial_pair_interval(self.owner, self.source, k, width - k)
        return (
            CarryFn.CONST0
            if middle.domain == -1
            else CarryFn.CONST1
            if middle.domain == 1
            else CarryFn.ID
        )


def certify_border_growth(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    *,
    steps: int,
    window_digits: int = 2,
    max_states: int = 8192,
) -> CertifiedBorderGrowth:
    """Certify one finite growth itinerary without future source evaluation.

    For the original Q19 pair source, the known original digits authorize the
    first growth event. For any later issued pair source S_n, the pair carry
    terminal authorizes the first growth event and Q19's pointed digit fold
    reconstructs the exact X_(n+1) border. Subsequent events are proved by
    the same all-interior-carry finite edge relation, not by enumerating the
    intermediate source words.
    """
    owner.validate_issued_occurrence(source)
    if type(steps) is not int or not 1 <= steps <= 65536:
        raise ValueError("positive bounded finite edge horizon required")
    if type(window_digits) is not int or not 1 <= window_digits <= 12:
        raise ValueError("edge windows must have width 1..12")
    if type(max_states) is not int or not 1 <= max_states <= 1000000:
        raise ValueError("invalid bounded boundary-state budget")
    cached = owner._issuance_registry.lookup_border(source, steps, window_digits)
    if cached is not None:
        cached.validate(owner, source)
        if max(cached.max_visited_states, cached.source_pair_inspections) > max_states:
            raise BoundaryControlNotAuthorized(
                "retained certificate exceeds the requested state budget"
            )
        return cached
    if steps == 1 and source is not owner.initial:
        owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_ATTEMPTS)
        growth = source.output_width - source.pair_width
        if growth not in (0, 1):
            raise BoundaryControlNotAuthorized(
                "issued Q19 root has no exact one-bit width transition"
            )
        return _issue_border(owner, source, (growth,), window_digits, 1)
    # Reserve the maximum live frontier, the current frontier, the finite
    # output word, and the source scan before allocating any of them.  This is
    # temporary scratch: all sets and the word builder die before the scope
    # releases their charge, including on an undecidable/refused edge.
    width = len(owner._digits) if source is owner.initial else source.output_width
    owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_ATTEMPTS)
    # Live edge/frontier memory depends on the state budget and the actual
    # inspected reset suffix, not the potentially gigantic virtual SLP width.
    scratch_nodes = (
        2 * max_states + 3 * steps + 6 * window_digits + min(width, max_states)
    )
    with owner.ledger.reservation(owner._scratch_owner, nodes=scratch_nodes):
        return _certify_reserved(
            owner,
            source,
            steps=steps,
            window_digits=window_digits,
            max_states=max_states,
        )


def _certify_reserved(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    *,
    steps: int,
    window_digits: int,
    max_states: int,
) -> CertifiedBorderGrowth:
    digits = owner._digits if source is owner.initial else None
    # A later issued pair root S_n emits the digits of X_(n+1), not X_n.
    # Its first growth is already the *terminal carry* of S_n, which is
    # authenticated by the Q19 source metadata. Certify the remaining
    # `steps-1` decisions from the emitted successor's exact edge digits.
    first_growth = (
        () if digits is not None else (source.output_width - source.pair_width,)
    )
    width = len(digits) if digits is not None else source.output_width
    k = window_digits
    if len(first_growth) == steps:
        return _issue_border(owner, source, first_growth, k, 1)
    if width < 2 * k + 1:
        raise BoundaryControlNotAuthorized(
            "source too narrow for independent edge tiles"
        )
    # Original digits and later Q19-issued digits are both LSD-first.
    # Random-access Q19 digits do not materialize an enormous source word.
    digit_at = (
        (lambda i: digits[i])
        if digits is not None
        else (lambda i: owner.digit(source, i))
    )
    prefix = 0
    base = 10**k
    for i in range(width - 1, width - k - 1, -1):
        prefix = 10 * prefix + digit_at(i)
    suffix = sum(digit_at(i) * 10**i for i in range(k))
    if not base // 10 <= prefix < base:
        raise BoundaryControlNotAuthorized(
            "source prefix does not fit an active k-digit tile"
        )
    incoming, source_pair_inspections = _source_inner_carry(
        owner, source, width=width, k=k, max_states=max_states
    )
    if digits is not None:
        middle = _initial_pair_interval(owner, source, k, width - k)
        middle_transfer = (
            CarryFn.CONST0
            if middle.domain == -1
            else CarryFn.CONST1
            if middle.domain == 1
            else CarryFn.ID
        )
        joined = border_bilateral_port(BorderTile(k, prefix, suffix)).for_middle(
            middle_transfer
        )
        if joined.high_carry != incoming:
            raise AssertionError("low overflow and source Q19 middle transfer disagree")

    tiles: set[tuple[int, int]] = {(prefix, suffix)}
    bits: list[int] = []
    outer_trace: list[tuple[int, int] | None] = [None] * len(first_growth)
    window_trace: list[BorderTile | None] = [None] * len(first_growth)
    visited = 1
    for tick in range(steps - len(first_growth)):
        owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_STEPS)
        outer_trace.append(_forced_outer_pair(tiles, k))
        window_trace.append(
            BorderTile(k, *next(iter(tiles))) if len(tiles) == 1 else None
        )
        future: set[tuple[int, int]] = set()
        possibilities: set[int] = set()
        for high_tile, low_tile in tiles:
            owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_STATE_VISITS)
            admitted = (incoming,) if tick == 0 else (0, 1)
            port = border_carry_port(BorderTile(k, high_tile, low_tile), admitted)
            for edge in port.edges:
                owner.ledger.bump(
                    _reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_EDGE_TRANSITIONS
                )
                possibilities.add(edge.growth)
                future.add((edge.target.high, edge.target.low))
                if len(future) > max_states:
                    raise BoundaryControlNotAuthorized(
                        f"boundary state budget exceeded at step {tick}"
                    )
        visited = max(visited, len(future))
        if len(possibilities) != 1:
            raise BoundaryControlNotAuthorized(
                f"interior carry alternatives disagree on growth at step {tick}; "
                f"certified prefix={''.join(map(str, bits))}"
            )
        bits.append(possibilities.pop())
        tiles = future
    outer_trace.append(_forced_outer_pair(tiles, k))
    window_trace.append(BorderTile(k, *next(iter(tiles))) if len(tiles) == 1 else None)
    return _issue_border(
        owner,
        source,
        first_growth + tuple(bits),
        k,
        visited,
        source_pair_inspections=source_pair_inspections,
        outer_pairs=tuple(outer_trace),
        window_tiles=tuple(window_trace),
    )


def _forced_outer_pair(tiles: set[tuple[int, int]], k: int) -> tuple[int, int] | None:
    possibilities = {(high // (10 ** (k - 1)), low % 10) for high, low in tiles}
    return next(iter(possibilities)) if len(possibilities) == 1 else None


def _initial_pair_interval(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    start: int,
    end: int,
) -> _Q19:
    """Fold an exact pair interval in source order without lowering the SLP."""
    width = source.pair_width
    half = owner._summaries[source.root].symbols
    if not 0 <= start <= end <= width:
        raise IndexError((start, end))
    if end <= half:
        return owner._range_summary(source.root, start, end)
    if start >= half:
        return owner._range_summary(
            source.root, width - end, width - start, reverse=True
        )
    return owner._range_summary(source.root, start, half).then(
        owner._range_summary(source.root, width - end, width - half, reverse=True)
    )


def _source_inner_carry(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    *,
    width: int,
    k: int,
    max_states: int,
) -> tuple[int, int]:
    """Authorize the first high-window carry from the actual Q19 pair source."""
    from .q19_conditional_stencil import GuardedPairStencil

    stencil = GuardedPairStencil.from_occurrence(owner, source)
    if source is owner.initial:
        end = width - k
        complete = _initial_pair_interval(owner, source, 0, end)
        if complete.domain == 0:
            depth = end
            carry = 0
        else:
            low, high = 1, end
            while low < high:
                middle = (low + high) // 2
                interval = _initial_pair_interval(owner, source, end - middle, end)
                if interval.domain == 0:
                    low = middle + 1
                else:
                    high = middle
            depth = low
            decisive = _initial_pair_interval(owner, source, end - depth, end)
            carry = int(decisive.domain == 1)
        owner.ledger.bump(
            _reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_SOURCE_PAIR_INSPECTIONS,
            min(depth, max_states),
        )
        if depth > max_states:
            raise BoundaryControlNotAuthorized(
                "unresolved source 9-wire exceeds the reset probe budget"
            )
        if carry != stencil.carry_at(owner, end):
            raise AssertionError(
                "compressed source reset fold disagrees with Q19 carry"
            )
        return carry, depth

    half = (width + 1) // 2
    inspections = 0
    candidate_indices = chain(range(k, half), range(half - 1 - (width & 1), -1, -1))
    for index in candidate_indices:
        if inspections >= max_states:
            raise BoundaryControlNotAuthorized(
                "unresolved emitted-source 9-wire exceeds the reset probe budget"
            )
        inspections += 1
        owner.ledger.bump(
            _reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_SOURCE_PAIR_INSPECTIONS
        )
        coefficient = stencil.cell_at(owner, index).coefficient
        if coefficient != 9:
            return int(coefficient > 9), inspections
    return 0, inspections


def _issue_border(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    word: tuple[int, ...],
    k: int,
    visited: int,
    *,
    source_pair_inspections: int = 0,
    outer_pairs: tuple[tuple[int, int] | None, ...] = (),
    window_tiles: tuple[BorderTile | None, ...] = (),
) -> CertifiedBorderGrowth:
    record = object.__new__(CertifiedBorderGrowth)
    attrs = {
        "owner": owner,
        "source": source,
        "growth_word": word,
        "window_digits": k,
        "max_visited_states": visited,
        "source_pair_inspections": source_pair_inspections,
        "outer_pairs": outer_pairs,
        "window_tiles": window_tiles,
        "physical_growth_certified": True,
        "full_integer_certified": False,
    }
    issue_q19_record(record, attrs, _ISSUER)
    retained = owner._issuance_registry.retain_border(record)
    try:
        retained.__post_init__()
    except BaseException:
        owner._issuance_registry.discard_border(record)
        raise
    owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_CERTIFICATES)
    return retained


__all__ = [
    "BoundaryControlNotAuthorized",
    "CertifiedBorderGrowth",
    "certify_border_growth",
]
