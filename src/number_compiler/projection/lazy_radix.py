"""Radix points from canonical tile applications and certified source morphisms.

Positive powered fields use the shared tile scheduler for general division.
The verified C/C² original-source laws and the finite 1-4-2 cycle retain their
source-only direct observations; they never construct or retain a future field.
Numeric ports support ``2 <= radix <= 2**63`` and scalar results share the
application's capped microblock cache.
"""

from __future__ import annotations

from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ExactSource,
)
from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
from number_compiler.projection.microblock_cache import (
    ExactMicroblock,
    MicroblockCache,
    MicroblockKey,
)
from number_compiler.projection.radix_fused_action import (
    FusedDivisionAction,
    FusedRadixArena,
    FusedRadixBindingKey,
)
from number_compiler.projection.radix_original_source import OriginalRadixArena
from number_compiler.projection.tile_radix import (
    TileRadixObservation,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.cycle import fixed_cycle_target


class RadixProjection:
    """One powered binary provider viewed through exact radix observations."""

    def __init__(
        self,
        radix: int,
        width: int,
        ledger: ResourceLedger,
        microblocks: MicroblockCache | None = None,
        *,
        width_is_upper_bound: bool = False,
    ) -> None:
        if type(radix) is not int or type(width) is not int:
            raise TypeError("radix and binary width must be exact integers")
        if not 2 <= radix <= 1 << 63:
            raise UnsupportedInterfaceError(
                "lazy radix points require 2 <= radix <= 2**63"
            )
        if width < 1:
            raise ValueError("binary width must be positive")
        if type(width_is_upper_bound) is not bool:
            raise TypeError("radix width policy must be boolean")
        self.radix, self.width, self.ledger = radix, width, ledger
        self._width_is_upper_bound = width_is_upper_bound
        self._microblocks = (
            MicroblockCache.shared(ledger) if microblocks is None else microblocks
        )
        if self._microblocks.ledger is not ledger:
            raise ValueError("microblock cache belongs to another index")
        ledger.register_execution_root(self)
        self._fused: FusedRadixArena | None = None
        self._native_source: OriginalRadixArena | None = None
        self._tile_observation: TileRadixObservation | None = None
        self._bound_source: ExactSource | None = None
        self._bound_steps: int | None = None
        fused_owner = ledger.register(
            f"radix-{radix}-fused-bindings", "spatial_binding"
        )
        self._fused_actions: OwnedMemo[FusedRadixBindingKey, FusedDivisionAction] = (
            OwnedMemo(ledger, fused_owner, evictable=True)
        )

    def _block_program(self, term: PoweredCollatzTerm) -> ActionProgramID:
        if term.effect is None:
            raise ValueError("block radix projection requires a positive powered term")
        return term._compiler.reference(term.effect)

    def _provider_digit(self, term: PoweredCollatzTerm, index: int) -> int:
        """Observe one digit through a division action in the shared scheduler.

        Completed quotient tiles are canonical scheduler results and can be
        reused by adjacent observations. No continuation/provider backend or
        separate flat quotient word is available here.
        """
        key = MicroblockKey(
            self._block_program(term), self.radix, index + 1, 0, "remainder"
        )
        self.ledger.bump("radix_provider_digit_requests")
        cached = self._microblocks.get(key)
        if cached is not None:
            self.ledger.bump("radix_provider_digit_early_hits")
            return int(cached.encoded)

        # Exterior admission uses the same affine image; a zero remainder
        # alone cannot distinguish an internal zero digit from blank padding.
        numerator, divisor = term._source_numerator()
        if index and numerator < divisor * self.radix**index:
            raise IndexError(index)
        digit = term.radix_digit(self.radix, index)
        if not 0 <= digit < self.radix:
            raise AssertionError("radix provider produced an invalid digit")
        self._microblocks.put(
            key, ExactMicroblock(digit, max(1, (self.radix - 1).bit_length()))
        )
        self.ledger.bump("radix_provider_digit_evaluations")
        return digit

    def _original_affine_digit(
        self, term: PoweredCollatzTerm, index: int, source_skip: int, incoming: int
    ) -> int:
        """Observe the source affine law through canonical prefix summaries."""
        if self._native_source is None:
            self._native_source = OriginalRadixArena(self.ledger)
        encoding = self._native_source.encode(term._source_construction, self.radix)
        return self._native_source.affine_shifted_point(
            encoding, source_skip, index, incoming
        )

    @source_reads_only
    def digit(self, term: PoweredCollatzTerm, index: int) -> int:
        if type(term) is not PoweredCollatzTerm:
            raise TypeError("radix projection requires an owned powered Collatz term")
        if type(index) is not int:
            raise TypeError("digit coordinate must be an exact integer")
        source = term._source_construction.validate_source()
        if (
            term._ledger is not self.ledger
            or self._bound_source is not None
            and (source is not self._bound_source or term.steps != self._bound_steps)
        ):
            raise ValueError("radix projection belongs to another binary source")
        observed_width = (
            term.maximum_width if self._width_is_upper_bound else term.width()
        )
        if observed_width != self.width:
            raise ValueError("radix projection belongs to another binary source")
        if not 0 <= index < self.width:
            raise IndexError(index)
        self._bound_source, self._bound_steps = source, term.steps
        # These fixed C/C² kernel identities transport ORIGINAL coordinates:
        # C(2u)=u, C(2u+1)=3(2u+1)+1, C²(4u)=u,
        # C²(4u+2)=3(2u+1)+1, C²(2u+1)=3u+2.
        # There is no temporal itinerary or intermediate field here.
        source_skip, final_shift, affine = 0, 0, False
        native = term.steps <= 2
        if term.steps == 1:
            affine = bool(term.seed_digits[0])
            source_skip = int(not affine)
        elif term.steps == 2:
            if term.seed_digits[0]:
                affine, final_shift = True, 1
            else:
                affine = len(term.seed_digits) > 1 and bool(term.seed_digits[1])
                source_skip = 1 if affine else 2
        # For b=3*2**m, the affine case (3*u+1)>>d has low digit
        # (3*r+1)>>d, r=u mod 2**(m+d), followed by the original suffix.
        # d is at most one and the arithmetic payload is at most 64 bits.
        factor, remainder = divmod(self.radix, 3)
        native = native and (
            not affine or remainder == 0 and factor > 0 and factor & (factor - 1) == 0
        )
        if native:
            low_bits = factor.bit_length() - 1 + final_shift if affine else 0
            source_start = source_skip + low_bits
            if affine and index == 0:
                low = 0
                for position in range(
                    min(low_bits, len(term.seed_digits) - source_skip)
                ):
                    low = self.ledger.observe_arithmetic(
                        low | (term.seed_digits[source_skip + position] << position)
                    )
                    self.ledger.bump("radix_native_original_bit_reads")
                self.ledger.bump(
                    "radix_native_odd_constant_queries"
                    if not low_bits
                    else "radix_native_odd_low_limb_queries"
                )
                return (
                    self.ledger.observe_arithmetic(
                        self.ledger.observe_arithmetic(3 * low) + 1
                    )
                    >> final_shift
                )
            if source_start >= len(term.seed_digits):
                raise IndexError(index)
            if self._native_source is None:
                self._native_source = OriginalRadixArena(self.ledger)
            source_index = index - int(affine)
            # The two-step compatibility path retains its certified complete
            # original encoding for source-audit callers.  Its scalar query can
            # still use the bounded observation and avoid rescanning that full
            # encoding once per requested digit.
            encoding = (
                self._native_source.encode(term._source_construction, self.radix)
                if term.steps == 2
                else None
            )
            bounded = self._native_source.bounded_shifted_point(
                term._source_construction,
                self.radix,
                source_start,
                source_index,
            )
            if bounded is not None:
                self.ledger.bump("radix_native_bounded_source_queries")
                return bounded
            if encoding is None:
                encoding = self._native_source.encode(
                    term._source_construction, self.radix
                )
            self.ledger.bump(
                "radix_native_odd_shift_queries"
                if affine
                else "radix_native_source_queries"
            )
            return self._native_source.shifted_point(
                encoding, source_start, source_index
            )
        # Reuse the certified physical three-cycle after the C/C² original
        # source morphisms.  The native routes intentionally retain their
        # immutable source encoding for the public source-audit contract.
        cycle_value = fixed_cycle_target(term.seed_digits, term.steps)
        if cycle_value is not None:
            self.ledger.bump("radix_fixed_cycle_observations")
            if index == 0:
                return cycle_value % self.radix
            if index == 1 and cycle_value >= self.radix:
                return cycle_value // self.radix
            if index == 2 and self.radix == 2 and cycle_value == 4:
                return 1
            raise IndexError(index)
        if affine and (
            term.steps == 2 or term.steps == 1 and (index >= 4 or self.radix > 12)
        ):
            # (3*(2u+1)+1)/2=3u+2; no intermediate odd endpoint.
            return self._original_affine_digit(
                term, index, source_skip + final_shift, 2 if final_shift else 1
            )
        # The small source/C1 fused interface is a bounded kernel shortcut.
        # Other providers use binary division powers in the shared scheduler.
        if term.steps <= 1 and self.radix <= 12 and index < 4:
            key = FusedRadixBindingKey(index)
            action = self._fused_actions.get(key)
            if action is None:
                # Reserve the association before constructing its semantic DAG;
                # successful publication cannot leave an orphaned action.
                self.ledger.reserve(self._fused_actions.owner, entries=1)
                try:
                    if self._fused is None:
                        self._fused = FusedRadixArena(self.ledger)
                    physical = term.steps == 1 and bool(term.seed_digits[0])
                    shift = int(term.steps == 1 and not physical)
                    action = self._fused.compile(
                        term.seed_digits,
                        radix=self.radix,
                        stages=index + 1,
                        physical=physical,
                        shift=shift,
                    )
                    self._fused_actions._data[key] = action
                except BaseException:
                    self.ledger.release(self._fused_actions.owner, entries=1)
                    raise
            else:
                self.ledger.bump("radix_fused_binding_hits")
            if self._fused is None:
                raise AssertionError("fused binding has no semantic arena")
            return self._fused.digit(action)
        return self._provider_digit(term, index)


@source_reads_only
def collatz_radix_digit(term: PoweredCollatzTerm, radix: int, index: int) -> int:
    if type(term) is not PoweredCollatzTerm:
        raise TypeError("radix projection requires an owned powered Collatz term")
    if type(radix) is not int or type(index) is not int:
        raise TypeError("radix and digit coordinate must be exact integers")
    if radix < 2:
        raise ValueError("radix must be at least two")
    if radix > 1 << 63:
        raise UnsupportedInterfaceError(
            "lazy radix points require 2 <= radix <= 2**63; use explicit digits/materialize for wider radices"
        )
    if index < 0:
        raise IndexError(index)
    # Scalar observations use the proved upper bound for admission.  The
    # binary point or radix carry result decides exact exterior coordinates;
    # computing the complete active width first would turn one digit request
    # into an unrelated width query.
    width = term.maximum_width
    if not 0 <= index < width:
        raise IndexError(index)
    term._ledger.bump("radix_observations")
    if radix & (radix - 1) == 0:
        limb_bits = radix.bit_length() - 1
        start = index * limb_bits
        if start >= width:
            raise IndexError(index)
        result = 0
        for position in range(min(limb_bits, width - start)):
            symbol = term._point_symbol(start + position)
            if symbol == 2:
                if position == 0:
                    raise IndexError(index)
                # The limb starts inside the value; its high blank cells are
                # zero padding. No complete-width observation is necessary.
                break
            result = term._ledger.observe_arithmetic(result | (symbol << position))
        return result
    projection = term._radix_projections.get(radix)
    if projection is None:
        owner = term._ledger.register(
            "radix-applications", "application_index", "INDEX_OWNED"
        )
        term._ledger.reserve(owner, entries=1)
        try:
            projection = RadixProjection(
                radix,
                width,
                term._ledger,
                term._microblocks,
                width_is_upper_bound=True,
            )
        except BaseException:
            term._ledger.release(owner, entries=1)
            raise
        term._radix_projections[radix] = projection
    return projection.digit(term, index)


__all__ = ["RadixProjection", "collatz_radix_digit"]
