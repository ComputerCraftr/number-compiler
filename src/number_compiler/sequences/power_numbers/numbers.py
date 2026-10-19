"""Canonical Fermat / Mersenne carriers and exact bounded projectors.

These families share the same cyclotomic, radix-word, factor-set, and powered
operator machinery used by reverse-add, Collatz, and the prime projector:

* ``F_n = 2**(2**n)+1 = Phi_(2**(n+1))(2)`` is a pure 2-power cyclotomic /
  negacyclic channel.  Subtracting one conjugates generation to squaring.
* ``M_p = 2**p-1 = Phi_p(2)`` when ``p`` is prime is an odd cyclotomic /
  cyclic channel.  The trace-square map ``x -> x*x-2`` conjugates to exponent
  doubling in the norm-one quadratic unit ``2+sqrt(3)``.

These generator identities do not construct the candidate's primality bit.
Production classification requires a separately proved candidate-derived
observation; missing recovery remains unresolved.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd
from typing import TYPE_CHECKING, Unpack

from number_compiler.arithmetic.fields.symbolic_extent import DyadicExtent
from number_compiler.sequences.prime.set import is_prime_u64, smallest_factor

if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.fermat_causal_border_matrix import (
        FermatCausalBorderMatrix,
    )
    from number_compiler.sequences.power_numbers.fermat_powered_port_matrix import (
        FermatPoweredPortMatrix,
    )
    from number_compiler.sequences.power_numbers.fermat_pumped_radial_unit import (
        FermatPumpedRadialUnit,
    )
    from number_compiler.sequences.power_numbers.mersenne_trace_port_matrix import (
        MersennePoweredTraceMatrix,
    )
    from number_compiler.sequences.power_numbers.signed_terminal_halo import (
        SignedFoldBirthWindow,
    )
    from number_compiler.sequences.power_numbers.source_halo import (
        StableUnwrappedHaloBlock,
    )
    from number_compiler.sequences.power_numbers.source_matrix import (
        FermatMultiradixPort,
        UnwrappedInnerDigitStencil,
        UnwrappedInnerRadixPort,
    )
    from number_compiler.sequences.power_numbers.terminal_source_demand import (
        SourceTerminalDemand,
    )
    from number_compiler.sequences.power_numbers.three_dyadic_boolean_counter import (
        BoundedCompleteUnitCertificate,
        BoundedFermatCounterCertificate,
        DyadicBooleanCounterWindow,
    )
    from number_compiler.sequences.power_numbers.three_dyadic_pivot_moore import (
        DyadicPivotMoore,
    )
    from number_compiler.sequences.power_numbers.three_dyadic_radial_counter_tape import (
        DyadicCertifiedTape,
    )
    from number_compiler.sequences.power_numbers.three_power_adaptive_interior import (
        AdaptiveInteriorAction,
        AdaptiveRefinedTape,
    )
    from number_compiler.sequences.power_numbers.three_power_bilateral_border import (
        ThreePowerBilateralInteriorQuotient,
        ThreePowerBilateralQuotient,
    )
    from number_compiler.sequences.power_numbers.three_power_joint_quotient import (
        ThreePowerJointQuotient,
    )
    from number_compiler.sequences.power_numbers.three_power_signed_border_action import (
        SourceWeightedTriplingAction,
    )
    from number_compiler.sequences.power_numbers.three_power_signed_phase import (
        SourceRestrictedPhaseRelation,
    )
    from number_compiler.sequences.power_numbers.three_power_temporal_source_morphism import (
        CertifiedFermatRootTemporalMorphism,
        FermatSourceDemandOptions,
    )
    from number_compiler.sequences.power_numbers.three_power_two_sided_cylinder import (
        FermatTwoSidedSourceCylinder,
    )


@dataclass(frozen=True, slots=True)
class FermatNumberSpec:
    index: int

    def __post_init__(self) -> None:
        if self.index < 0:
            raise ValueError(self.index)

    @property
    def exponent_extent(self) -> DyadicExtent:
        return DyadicExtent(self.index)

    @property
    def bit_length_extent(self) -> DyadicExtent:
        return DyadicExtent(self.index, 1)

    @property
    def cyclotomic_order_extent(self) -> DyadicExtent:
        return DyadicExtent(self.index + 1)

    @property
    def exponent(self) -> int:
        # Compatibility/materialization view.  Production source compilation
        # uses exponent_extent and never calls this property.
        return self.exponent_extent.materialize(max_power=self.index)

    @property
    def cyclotomic_order(self) -> int:
        return self.cyclotomic_order_extent.materialize(max_power=self.index + 1)

    @property
    def bit_length(self) -> int:
        return self.bit_length_extent.materialize(max_power=self.index)

    @property
    def description_bits(self) -> int:
        return max(1, self.index.bit_length())

    def materialize(self, *, max_bits: int = 1_000_000) -> int:
        max_bits = int(max_bits)
        if max_bits <= 0 or self.bit_length_extent > max_bits:
            raise ValueError((self.bit_length_extent, max_bits))
        # The guard above proves the exponent is small enough for the requested
        # materialization budget before any dyadic boundary is lowered.
        exponent = self.exponent_extent.materialize(max_power=max_bits.bit_length())
        return (1 << exponent) + 1

    def terminal_source_demand(self) -> SourceTerminalDemand:
        """Return a lazy, candidate-bound source obligation, never a proof bit."""
        from number_compiler.sequences.power_numbers.terminal_source_demand import (
            SourceTerminalDemand,
        )

        return SourceTerminalDemand.for_candidate("fermat", self.index)

    def demand_three_power_bilateral_border(
        self,
        level: int,
        *,
        low_binary_places: int = 12,
        low_decimal_places: int = 4,
        high_binary_places: int = 8,
        high_decimal_places: int = 4,
        max_work_units: int = 25_000_000,
    ) -> ThreePowerBilateralQuotient:
        """Source-authenticated *ordinary* 3X border/carry constraints.

        Combines binary and decimal low carry orbits with certified leading
        Sturmian prefixes. The unknown interior remains a set of possible
        transfers; no false F_n prime bit or dyadic temporal step is inferred.
        """
        from number_compiler.sequences.power_numbers.three_power_bilateral_border import (
            demand_three_power_bilateral_quotient,
        )

        return demand_three_power_bilateral_quotient(
            self.index,
            level,
            low_binary_places=low_binary_places,
            low_decimal_places=low_decimal_places,
            high_binary_places=high_binary_places,
            high_decimal_places=high_decimal_places,
            max_work_units=max_work_units,
        )

    def demand_three_power_bilateral_interior(
        self,
        level: int,
        *,
        binary_windows: tuple[tuple[int, int], ...] = (),
        decimal_windows: tuple[tuple[int, int], ...] = (),
        low_binary_places: int = 12,
        low_decimal_places: int = 4,
        high_binary_places: int = 8,
        high_decimal_places: int = 4,
        max_work_units: int = 25_000_000,
    ) -> ThreePowerBilateralInteriorQuotient:
        """Propagate certified binary/decimal interior windows in both directions.

        Keeps conditional carry transfer and absolute H5 of witnessed islands.
        It does NOT interpret the ordinary 3X step as the dyadic square.
        """
        from number_compiler.sequences.power_numbers.three_power_bilateral_border import (
            demand_three_power_bilateral_interior,
        )

        return demand_three_power_bilateral_interior(
            self.index,
            level,
            binary_windows=binary_windows,
            decimal_windows=decimal_windows,
            low_binary_places=low_binary_places,
            low_decimal_places=low_decimal_places,
            high_binary_places=high_binary_places,
            high_decimal_places=high_decimal_places,
            max_work_units=max_work_units,
        )

    def demand_three_power_inward_phase_quotient(
        self,
        level: int,
        *,
        phase_binary_places: int = 64,
        phase_decimal_places: int = 6,
        binary_windows: tuple[tuple[int, int], ...] = (),
        decimal_windows: tuple[tuple[int, int], ...] = (),
        low_binary_places: int = 12,
        low_decimal_places: int = 4,
        high_binary_places: int = 8,
        high_decimal_places: int = 4,
    ) -> ThreePowerBilateralInteriorQuotient:
        """Use phase-selected inward carry/H5 masks in both radial borders.

        All phase masks derive from this source level, never from a sampled
        2rev10 trajectory.  This local source quotient is not a prime bit.
        """
        from number_compiler.sequences.power_numbers.three_power_bilateral_border import (
            demand_three_power_inward_phase_quotient,
        )

        return demand_three_power_inward_phase_quotient(
            self.index,
            level,
            phase_binary_places=phase_binary_places,
            phase_decimal_places=phase_decimal_places,
            binary_windows=binary_windows,
            decimal_windows=decimal_windows,
            low_binary_places=low_binary_places,
            low_decimal_places=low_decimal_places,
            high_binary_places=high_binary_places,
            high_decimal_places=high_decimal_places,
        )

    def demand_three_power_signed_border_action(
        self,
        level: int,
        *,
        phase_binary_places: int = 64,
        phase_decimal_places: int = 6,
        binary_windows: tuple[tuple[int, int], ...] = (),
        decimal_windows: tuple[tuple[int, int], ...] = (),
        low_binary_places: int = 12,
        low_decimal_places: int = 4,
        high_binary_places: int = 8,
        high_decimal_places: int = 4,
    ) -> SourceWeightedTriplingAction:
        """Demand signed source ports, retaining unknown middle contributions."""
        from number_compiler.sequences.power_numbers.three_power_signed_border_action import (
            demand_signed_tripling_action,
        )

        return demand_signed_tripling_action(
            self.index,
            level,
            phase_binary_places=phase_binary_places,
            phase_decimal_places=phase_decimal_places,
            binary_windows=binary_windows,
            decimal_windows=decimal_windows,
            low_binary_places=low_binary_places,
            low_decimal_places=low_decimal_places,
            high_binary_places=high_binary_places,
            high_decimal_places=high_decimal_places,
        )

    def demand_three_power_two_sided_source_cylinder(
        self,
        level: int,
        *,
        phase_binary_places: int = 64,
        phase_decimal_places: int = 6,
        binary_windows: tuple[tuple[int, int], ...] = (),
        decimal_windows: tuple[tuple[int, int], ...] = (),
        low_binary_places: int = 12,
        low_decimal_places: int = 4,
        high_binary_places: int = 8,
        high_decimal_places: int = 4,
    ) -> FermatTwoSidedSourceCylinder:
        """Joint low CRT/high radial source cylinder; no candidate squarings."""
        action = self.demand_three_power_signed_border_action(
            level,
            phase_binary_places=phase_binary_places,
            phase_decimal_places=phase_decimal_places,
            binary_windows=binary_windows,
            decimal_windows=decimal_windows,
            low_binary_places=low_binary_places,
            low_decimal_places=low_decimal_places,
            high_binary_places=high_binary_places,
            high_decimal_places=high_decimal_places,
        )
        return action.demand_two_sided_source_cylinder()

    def demand_three_power_source_restricted_phase(
        self,
        level: int,
        *,
        max_fibers: int = 64,
        inward_boundaries: int = 8,
        phase_binary_places: int = 64,
        phase_decimal_places: int = 6,
        binary_windows: tuple[tuple[int, int], ...] = (),
        decimal_windows: tuple[tuple[int, int], ...] = (),
        low_binary_places: int = 12,
        low_decimal_places: int = 4,
        high_binary_places: int = 8,
        high_decimal_places: int = 4,
    ) -> SourceRestrictedPhaseRelation:
        """Source-wide CRT/Sturmian guards applied to signed phase counts."""
        source = self.demand_three_power_signed_border_action(
            level,
            phase_binary_places=phase_binary_places,
            phase_decimal_places=phase_decimal_places,
            binary_windows=binary_windows,
            decimal_windows=decimal_windows,
            low_binary_places=low_binary_places,
            low_decimal_places=low_decimal_places,
            high_binary_places=high_binary_places,
            high_decimal_places=high_decimal_places,
        )
        return source.demand_source_restricted_phase_relation(
            max_fibers=max_fibers, inward_boundaries=inward_boundaries
        )

    def demand_three_power_temporal_source_morphism(
        self,
        level: int,
        dyadic_steps: int = 1,
        **source_options: Unpack[FermatSourceDemandOptions],
    ) -> CertifiedFermatRootTemporalMorphism:
        """Demand exact dyadic source-root endpoints with open interior carries."""
        from number_compiler.sequences.power_numbers.three_power_temporal_source_morphism import (
            demand_fermat_source_temporal_morphism,
        )

        return demand_fermat_source_temporal_morphism(
            self, level, dyadic_steps, **source_options
        )

    def demand_joint_three_power_quotient(
        self,
        level: int,
        demands: tuple[tuple[int, int], ...] = (
            (2, 16),
            (3, 10),
            (5, 8),
            (7, 6),
            (10, 6),
            (11, 5),
            (13, 5),
            (27, 4),
        ),
        *,
        moving_width: int = 12,
    ) -> ThreePowerJointQuotient:
        """Share one unwrapped source across finite CRT, pivot and Walsh demands.

        The packet does not evaluate the Fermat candidate modulus or issue a
        primality status. Walsh transforms are computed only when requested
        from the returned packet.
        """
        from number_compiler.sequences.power_numbers.three_power_joint_quotient import (
            demand_three_power_joint_quotient,
        )

        return demand_three_power_joint_quotient(
            self.index, level, demands, moving_width=moving_width
        )

    def demand_pumped_radial_unit(self, level: int) -> FermatPumpedRadialUnit:
        """Retain the exact symbolic radial/unit split at one nested level.

        This is a source description only. It does not evaluate the unit
        modulo the Fermat candidate or contribute a primality decision.
        """
        from number_compiler.sequences.power_numbers.fermat_pumped_radial_unit import (
            FermatPumpedRadialUnit,
        )

        return FermatPumpedRadialUnit(self.index, level)

    def demand_dyadic_pivot_moore(
        self, level: int, offsets: tuple[int, ...] = (0, 1, 2, 3, 5, 6)
    ) -> DyadicPivotMoore:
        """Demand bounded local pivot ports inside this Fermat source horizon.

        The returned Moore observer retains ``level`` as occurrence metadata;
        its finite state is not a candidate-primality observation.
        """
        if type(self.index) is not int or self.index < 1:
            raise ValueError(("Fermat source index", self.index))
        if type(level) is not int or level < 1:
            raise ValueError(("dyadic source level", level))
        if not self.exponent_extent.contains_index(level):
            raise ValueError(("level-exceeds-Fermat-source", level, self.index))
        from number_compiler.sequences.power_numbers.three_dyadic_pivot_moore import (
            DyadicPivotMoore,
        )

        return DyadicPivotMoore(level, offsets)

    def demand_bounded_boolean_counter_certificate(
        self,
    ) -> BoundedFermatCounterCertificate:
        """Source-derived complete small-index proof; refuse before expansion.

        This explicitly budgeted proof uses finite-precision Boolean counter
        windows and does not promote the unrestricted primality query.
        """
        from number_compiler.sequences.power_numbers.three_dyadic_boolean_counter import (
            demand_bounded_fermat_counter_certificate,
        )

        return demand_bounded_fermat_counter_certificate(self.index)

    def demand_bounded_complete_unit_certificate(
        self,
    ) -> BoundedCompleteUnitCertificate:
        """Demand the full terminal 2-adic unit under its separate bit budget.

        This explicit source-width operation is opt-in and does not change the
        production primality route or claim a uniform cost bound in the index.
        """
        from number_compiler.sequences.power_numbers.three_dyadic_boolean_counter import (
            demand_bounded_complete_unit_certificate,
        )

        return demand_bounded_complete_unit_certificate(self.index)

    def demand_dyadic_boolean_counter(
        self, level: int, width: int, *, offset: int = 0
    ) -> DyadicBooleanCounterWindow:
        """Source-authenticated binary counter with signed positional classes.

        No terminal prime result is issued: the requested finite window does
        not imply completeness of the global negacyclic remainder.
        """
        from number_compiler.sequences.power_numbers.three_dyadic_boolean_counter import (
            MAX_COUNTER_FOLD_WIDTH,
            demand_dyadic_boolean_counter,
        )

        if type(self.index) is not int or self.index < 1:
            raise ValueError(("invalid-Fermat-index", self.index))
        if type(level) is not int or level < 1:
            raise ValueError(("invalid-dyadic-source-level", level))
        if not self.exponent_extent.contains_index(level):
            raise ValueError(("level-exceeds-Fermat-source", level, self.index))
        if self.index > MAX_COUNTER_FOLD_WIDTH.bit_length() - 1:
            raise ValueError("Fermat counter fold width exceeds the explicit budget")
        return demand_dyadic_boolean_counter(
            level, width, fermat_width=1 << self.index, offset=offset
        )

    def demand_three_power_output_tape(
        self,
        level: int,
        *,
        low_bits: int = 128,
        leading_bits: int = 32,
        max_precision_bits: int = 8_192,
        max_work_units: int = 25_000_000,
    ) -> DyadicCertifiedTape:
        """Join the certified radial prefix and exact low Boolean tape.

        Only the returned leading and low intervals are readable; any
        uncovered middle positions remain UNKNOWN. The finite source update
        is not a candidate-modulus primality computation.
        """
        if type(self.index) is not int or not 1 <= self.index <= 16:
            raise ValueError("Fermat source index must be positive")
        if (
            type(level) is not int
            or level < 1
            or not self.exponent_extent.contains_index(level)
        ):
            raise ValueError("three-power level lies outside the Fermat source horizon")
        from number_compiler.arithmetic.fields.homogeneous_growth import (
            GrowthArithmeticEvaluator,
        )
        from number_compiler.resources.ledger import ResourceLedger
        from number_compiler.sequences.power_numbers.three_dyadic_radial_counter_tape import (
            ThreeDyadicRadialCounterTransducer,
        )

        with GrowthArithmeticEvaluator(
            ResourceLedger(),
            max_precision_bits=max_precision_bits,
            max_work_units=max_work_units,
        ) as evaluator:
            return ThreeDyadicRadialCounterTransducer(level).composed_step(
                evaluator,
                fermat_width=1 << self.index,
                low_bits=low_bits,
                leading_bits=leading_bits,
            )

    def demand_adaptive_three_power_interior(
        self,
        level: int,
        windows: tuple[tuple[int, int], ...],
        *,
        radix_demands: tuple[tuple[int, int], ...] = ((2, 6), (5, 4), (10, 4)),
    ) -> AdaptiveInteriorAction:
        """Demand source-authenticated interior bits and bounded radix ports."""
        from number_compiler.sequences.power_numbers.three_power_adaptive_interior import (
            demand_three_power_adaptive_interior,
        )

        return demand_three_power_adaptive_interior(
            self.index, level, windows, radix_demands=radix_demands
        )

    def demand_adaptive_three_power_output_tape(
        self,
        level: int,
        windows: tuple[tuple[int, int], ...],
        *,
        radix_demands: tuple[tuple[int, int], ...] = ((2, 6), (5, 4), (10, 4)),
        low_bits: int = 128,
        leading_bits: int = 32,
    ) -> AdaptiveRefinedTape:
        """Add genuinely source-derived interior intervals to the partial tape."""
        from number_compiler.sequences.power_numbers.three_power_adaptive_interior import (
            AdaptiveRefinedTape,
        )

        tape = self.demand_three_power_output_tape(
            level, low_bits=low_bits, leading_bits=leading_bits
        )
        action = self.demand_adaptive_three_power_interior(
            level, windows, radix_demands=radix_demands
        )
        return AdaptiveRefinedTape(tape, action)

    def demand_three_power_multiradix_port(
        self, level: int, base: int, places: int
    ) -> FermatMultiradixPort:
        """Demand bounded low-radix carry/borrow wires of ``3**(2**level)``.

        The small-modulus source observation is separate from candidate
        reduction and is not a terminal remainder or primality certificate.
        """
        from number_compiler.sequences.power_numbers.source_matrix import (
            demand_three_power_multiradix_port,
        )

        return demand_three_power_multiradix_port(self.index, level, base, places)

    def demand_three_power_causal_border_matrix(
        self,
        level: int,
        physical_steps: int,
        *,
        base: int = 10,
        position: int = 0,
        max_work_units: int | None = None,
    ) -> FermatCausalBorderMatrix:
        """Select a finite carry row from the existing bilateral source owner.

        The requested physical span and radix position remain separate. This
        is an ordinary finite ``X -> 3X`` source transfer, not a claim that
        its carry word repeats or that the Fermat signed fold is complete.
        """
        from number_compiler.sequences.power_numbers.fermat_causal_border_matrix import (
            demand_fermat_causal_border_matrix,
        )

        return demand_fermat_causal_border_matrix(
            self,
            level,
            physical_steps,
            base=base,
            position=position,
            max_work_units=max_work_units,
        )

    def demand_fermat_powered_port_matrix(
        self,
        level: int,
        physical_steps: int,
        *,
        base: int = 10,
        position: int = 0,
    ) -> FermatPoweredPortMatrix:
        """Production, registry-first conditional 3X port action.

        Unlike a finite row trace, this transports authenticated modular
        inlet/outlet conditions in logarithmic temporal work and supports
        genuine physical ``then``/``square`` without reissuing the root.
        It does not decide the candidate's primality bit.
        """
        from number_compiler.sequences.power_numbers.fermat_powered_port_matrix import (
            demand_fermat_powered_port_matrix,
        )

        return demand_fermat_powered_port_matrix(
            self, level, physical_steps, base=base, position=position
        )

    def demand_unwrapped_inner_radix_port(
        self, level: int, base: int
    ) -> UnwrappedInnerRadixPort:
        """Demand bounded source carry/borrow/digit wires under the no-wrap guard."""
        from number_compiler.sequences.power_numbers.source_matrix import (
            demand_unwrapped_inner_radix_port,
        )

        return demand_unwrapped_inner_radix_port("fermat", self.index, level, base)

    def demand_unwrapped_inner_digit_stencil(
        self, level: int, base: int, positions: tuple[int, ...]
    ) -> UnwrappedInnerDigitStencil:
        """Demand only selected digits of the raw inner square source."""
        from number_compiler.sequences.power_numbers.source_matrix import (
            demand_unwrapped_inner_digit_stencil,
        )

        return demand_unwrapped_inner_digit_stencil(
            "fermat", self.index, level, base, positions
        )

    def power_stable_unwrapped_inner_halo(
        self, source_level: int, span: int
    ) -> StableUnwrappedHaloBlock:
        """Power an explicitly requested stationary no-wrap binary halo."""
        from number_compiler.sequences.power_numbers.source_halo import (
            StableUnwrappedHaloBlock,
        )

        return StableUnwrappedHaloBlock("fermat", self.index, source_level, span)

    def project_signed_fold_birth_window(
        self, source: object, *, start: int = 0, length: int = 64
    ) -> SignedFoldBirthWindow:
        """Project an already supplied negacyclic fold, conditionally."""
        from number_compiler.arithmetic.carry.signed_weighted_carry import (
            WideSignedCarryAction,
        )
        from number_compiler.sequences.power_numbers.signed_terminal_halo import (
            demand_signed_birth_window,
        )

        if type(source) is not WideSignedCarryAction:
            raise TypeError("signed-fold projection requires a carry SLP")
        if (
            source.sign != -1
            or source.width & (source.width - 1)
            or source.width.bit_length() - 1 != self.index
        ):
            raise ValueError("Fermat signed-fold width or negacyclic seam mismatch")
        return demand_signed_birth_window(source, start=start, length=length)


@dataclass(frozen=True, slots=True)
class MersenneNumberSpec:
    exponent: int

    def __post_init__(self) -> None:
        if self.exponent <= 0:
            raise ValueError(self.exponent)

    @property
    def bit_length(self) -> int:
        return self.exponent

    @property
    def description_bits(self) -> int:
        return max(1, self.exponent.bit_length())

    def materialize(self, *, max_bits: int = 1_000_000) -> int:
        max_bits = int(max_bits)
        if max_bits <= 0 or self.bit_length > max_bits:
            raise ValueError((self.bit_length, max_bits))
        return (1 << self.exponent) - 1

    def terminal_source_demand(self) -> SourceTerminalDemand:
        """Return a lazy cyclic trace demand, not a Lucas-Lehmer certificate."""
        from number_compiler.sequences.power_numbers.terminal_source_demand import (
            SourceTerminalDemand,
        )

        return SourceTerminalDemand.for_candidate("mersenne", self.exponent)

    def project_signed_fold_birth_window(
        self, source: object, *, start: int = 0, length: int = 64
    ) -> SignedFoldBirthWindow:
        """Project an already supplied cyclic fold, conditionally."""
        from number_compiler.arithmetic.carry.signed_weighted_carry import (
            WideSignedCarryAction,
        )
        from number_compiler.sequences.power_numbers.signed_terminal_halo import (
            demand_signed_birth_window,
        )

        if type(source) is not WideSignedCarryAction:
            raise TypeError("signed-fold projection requires a carry SLP")
        if source.sign != 1 or source.width != self.exponent:
            raise ValueError("Mersenne signed-fold width or cyclic seam mismatch")
        return demand_signed_birth_window(source, start=start, length=length)

    def demand_mersenne_trace_matrix(
        self, trace_steps: int, *, base: int = 10, position: int = 0
    ) -> MersennePoweredTraceMatrix:
        """Source-only norm-one trace matrix; never a primality witness."""
        from number_compiler.sequences.power_numbers.mersenne_trace_port_matrix import (
            demand_mersenne_trace_matrix,
        )

        return demand_mersenne_trace_matrix(
            self.exponent, trace_steps, base=base, position=position
        )

    def demand_unwrapped_inner_radix_port(
        self, level: int, base: int
    ) -> UnwrappedInnerRadixPort:
        """Demand bounded source carry/borrow/digit wires under the no-wrap guard."""
        from number_compiler.sequences.power_numbers.source_matrix import (
            demand_unwrapped_inner_radix_port,
        )

        return demand_unwrapped_inner_radix_port("mersenne", self.exponent, level, base)

    def demand_unwrapped_inner_digit_stencil(
        self, level: int, base: int, positions: tuple[int, ...]
    ) -> UnwrappedInnerDigitStencil:
        """Demand only selected digits of the raw norm-one trace square."""
        from number_compiler.sequences.power_numbers.source_matrix import (
            demand_unwrapped_inner_digit_stencil,
        )

        return demand_unwrapped_inner_digit_stencil(
            "mersenne", self.exponent, level, base, positions
        )

    def power_stable_unwrapped_inner_halo(
        self, source_level: int, span: int
    ) -> StableUnwrappedHaloBlock:
        """Power an explicitly requested stationary no-wrap binary halo."""
        from number_compiler.sequences.power_numbers.source_halo import (
            StableUnwrappedHaloBlock,
        )

        return StableUnwrappedHaloBlock("mersenne", self.exponent, source_level, span)


@dataclass(frozen=True, slots=True)
class CyclotomicRadixWordSpec:
    """Symbolic reinterpretation of a sparse binary special-number word.

    ``family='fermat'`` means the digit word ``1 0^(2^n-1) 1`` evaluated in
    ``radix``; ``family='mersenne'`` means ``1^p`` evaluated in ``radix``.
    These are respectively ``Phi_(2^(n+1))(radix)`` and, for prime ``p``,
    ``Phi_p(radix)``.  The digit program stays compact even when the evaluated
    integer is enormous.
    """

    family: str
    parameter: int
    radix: int

    def __post_init__(self) -> None:
        if (
            self.family not in ("fermat", "mersenne")
            or self.parameter < 0
            or self.radix < 2
        ):
            raise ValueError(self)
        if self.family == "mersenne" and self.parameter <= 0:
            raise ValueError(self)

    @property
    def cyclotomic_order_extent(self) -> DyadicExtent | int:
        return (
            DyadicExtent(self.parameter + 1)
            if self.family == "fermat"
            else self.parameter
        )

    @property
    def digit_length_extent(self) -> DyadicExtent | int:
        return (
            DyadicExtent(self.parameter, 1)
            if self.family == "fermat"
            else self.parameter
        )

    @property
    def cyclotomic_order(self) -> int:
        value = self.cyclotomic_order_extent
        return (
            value.materialize(max_power=value.power)
            if isinstance(value, DyadicExtent)
            else int(value)
        )

    @property
    def digit_length(self) -> int:
        value = self.digit_length_extent
        return (
            value.materialize(max_power=value.power)
            if isinstance(value, DyadicExtent)
            else int(value)
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "cyclotomic-radix-word",
            self.family,
            int(self.parameter),
            int(self.radix),
        )

    @property
    def description_bits(self) -> int:
        return max(1, self.parameter.bit_length()) + max(1, self.radix.bit_length()) + 1

    def materialize(self, *, max_digits: int = 100_000) -> int:
        max_digits = int(max_digits)
        extent = self.digit_length_extent
        if (
            (extent > max_digits)
            if isinstance(extent, DyadicExtent)
            else (int(extent) > max_digits)
        ):
            raise ValueError((extent, max_digits))
        if self.family == "fermat":
            exponent = DyadicExtent(self.parameter).materialize(
                max_power=max_digits.bit_length()
            )
            return int(pow(self.radix, exponent)) + 1
        return (int(pow(self.radix, self.parameter)) - 1) // (self.radix - 1)


def fermat_radix_reinterpretation(index: int, radix: int) -> CyclotomicRadixWordSpec:
    return CyclotomicRadixWordSpec("fermat", int(index), int(radix))


def mersenne_radix_reinterpretation(
    exponent: int, radix: int
) -> CyclotomicRadixWordSpec:
    return CyclotomicRadixWordSpec("mersenne", int(exponent), int(radix))


def fermat_number(index: int) -> int:
    return FermatNumberSpec(int(index)).materialize()


def mersenne_number(exponent: int) -> int:
    return MersenneNumberSpec(int(exponent)).materialize()


def fermat_successor(value: int) -> int:
    """Polynomial generation recurrence ``F_(n+1)=(F_n-1)^2+1``."""
    value = int(value)
    if value < 3:
        raise ValueError(value)
    return (value - 1) * (value - 1) + 1


def mersenne_successor(value: int) -> int:
    """Exponent-by-one recurrence ``M_(n+1)=2*M_n+1``."""
    value = int(value)
    if value < 1:
        raise ValueError(value)
    return 2 * value + 1


def fermat_previous_product(index: int) -> int:
    """Return ``prod(F_0..F_(n-1)) = F_n-2`` for bounded materialized ``n``."""
    index = int(index)
    if index < 0:
        raise ValueError(index)
    return FermatNumberSpec(index).materialize() - 2


def mersenne_gcd_spec(first_exponent: int, second_exponent: int) -> MersenneNumberSpec:
    """Symbolic form of ``gcd(M_a,M_b)=M_gcd(a,b)``."""
    a, b = int(first_exponent), int(second_exponent)
    if a <= 0 or b <= 0:
        raise ValueError((a, b))
    return MersenneNumberSpec(gcd(a, b))


def special_modulus_matches(family: str, parameter: int, modulus: int) -> bool:
    """Validate a concrete Fermat/Mersenne modulus without duplicate huge powers."""
    family, parameter, modulus = str(family), int(parameter), int(modulus)
    if family == "fermat":
        m = modulus - 1
        exponent = m.bit_length() - 1 if m > 0 else -1
        return (
            parameter >= 0
            and m > 0
            and not (m & (m - 1))
            and exponent > 0
            and not (exponent & (exponent - 1))
            and exponent.bit_length() - 1 == parameter
        )
    if family == "mersenne":
        m = modulus + 1
        return (
            parameter >= 2
            and m > 0
            and not (m & (m - 1))
            and m.bit_length() - 1 == parameter
        )
    raise ValueError(family)


def verified_special_divisor(
    family: str, parameter: int, modulus: int, defect: int
) -> int:
    """Check an admitted integer witness against the exact candidate source."""
    if not special_modulus_matches(family, parameter, modulus):
        raise ValueError("defect modulus does not match the requested special source")
    support = gcd(modulus, defect)
    if not 1 < support < modulus:
        raise ValueError("unissued defect must exhibit a proper candidate divisor")
    return support


def mersenne_exponent_is_prime(exponent: int) -> bool:
    """Decide the exponent gate without producing an unnecessary factor.

    Mersenne primality only reaches the number-level theorem when the exponent
    itself is prime.  For machine-word exponents the repository already has an
    exact deterministic Miller--Rabin predicate, so do not trial-divide all the
    way to sqrt(p) merely to learn the same Boolean.  Larger Python integers
    retain the exact historical factor-producing fallback.
    """
    n = int(exponent)
    if n < 2:
        return False
    if n < (1 << 64):
        return is_prime_u64(n)
    return smallest_factor(n) is None


def mersenne_composite_exponent_factor(
    exponent: int, *, max_divisor: int | None = None
) -> MersenneNumberSpec | None:
    """Return a symbolic proper Mersenne divisor when the exponent is composite."""
    n = int(exponent)
    if n <= 1:
        raise ValueError(n)
    factor = smallest_factor(n, max_divisor=max_divisor)
    return None if factor is None else MersenneNumberSpec(factor)


def fermat_factor_stride(index: int) -> int:
    """Stride forced on prime divisors of ``F_n`` for ``n>=2``."""
    index = int(index)
    if index < 2:
        raise ValueError(index)
    return 1 << (index + 2)


def mersenne_factor_stride(exponent: int) -> int:
    """Every prime divisor of ``2**p-1`` for prime ``p`` is ``1 mod 2p``."""
    exponent = int(exponent)
    if exponent < 2:
        raise ValueError(exponent)
    return 2 * exponent


__all__ = [
    "CyclotomicRadixWordSpec",
    "FermatNumberSpec",
    "MersenneNumberSpec",
    "fermat_factor_stride",
    "fermat_number",
    "fermat_previous_product",
    "fermat_radix_reinterpretation",
    "fermat_successor",
    "mersenne_composite_exponent_factor",
    "mersenne_exponent_is_prime",
    "mersenne_factor_stride",
    "mersenne_gcd_spec",
    "mersenne_number",
    "mersenne_radix_reinterpretation",
    "mersenne_successor",
    "special_modulus_matches",
    "verified_special_divisor",
]
