"""Issued source-bound powers of guarded Collatz skew actions."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, TypeGuard, TypeVar, cast

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
    require_integer,
)
from number_compiler.arithmetic.fields.affine_high_digits import (
    AffineHighDigitTransport,
)
from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
    HomogeneousGrowthScale,
)
from number_compiler.arithmetic.fields.radial_sturmian import (
    RadialSturmianClock,
    RadialSturmianPacket,
)
from number_compiler.arithmetic.fields.three_power_radix import (
    ThreePowerRadixOrbit,
    difference_power_block,
)
from number_compiler.arithmetic.fields.walsh import walsh64_mod5
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.skew_cylinder_repeat import (
    RepeatedWordMooreCylinder,
)
from number_compiler.sequences.collatz.temporal_f5_observer import (
    project_dyadic_fields_f5,
)
from number_compiler.sequences.collatz.unified_skew_clock import SkewQuadraticClock

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.border_return_grammar import (
        BorderReturnMacro,
    )
    from number_compiler.sequences.collatz.boundary_macros import (
        CollatzBoundaryMacro,
    )
    from number_compiler.sequences.collatz.unified_skew_chain import UnifiedSkewChain

_ExactType = TypeVar("_ExactType")


def _is_exact_instance(
    value: object, expected: type[_ExactType]
) -> TypeGuard[_ExactType]:
    """Narrow only after the exact runtime-type boundary."""
    return type(value) is expected


def _cylinder_snapshot(cylinder: RepeatedWordMooreCylinder) -> tuple[object, ...]:
    return cylinder.publication_snapshot()


def _clock_snapshot(clock: SkewQuadraticClock | None) -> tuple[object, ...] | None:
    if clock is None:
        return None
    return (
        clock.precision,
        clock.steps,
        clock.odds,
        clock.value,
        clock.linear,
        clock.quadratic,
        clock.position_sum,
        clock.first_odd,
        clock.last_odd,
    )


@dataclass(frozen=True, slots=True, init=False)
class GuardedSkewCylinderPower:
    """Sealed power of one issued action, with family selection kept separate."""

    source: int
    repetitions: int
    odd_symbols: int
    action: DyadicTerminalFieldAction
    cylinder: RepeatedWordMooreCylinder
    skew_clock: SkewQuadraticClock | None
    radial_clock: RadialSturmianClock
    physical_ticks: int
    _issuer: object = field(repr=False, compare=False)
    _binding: tuple[object, ...] = field(repr=False, compare=False)

    def __init__(self) -> None:
        raise TypeError("guarded skew powers require issued source authority")

    @classmethod
    def _issue(
        cls,
        source: int,
        repetitions: int,
        odd_symbols: int,
        action: DyadicTerminalFieldAction,
        cylinder: RepeatedWordMooreCylinder,
        clock: SkewQuadraticClock | None,
        radial: RadialSturmianClock,
        physical_ticks: int,
    ) -> GuardedSkewCylinderPower:
        record = object.__new__(cls)
        for name, value in (
            ("source", source),
            ("repetitions", repetitions),
            ("odd_symbols", odd_symbols),
            ("action", action),
            ("cylinder", cylinder),
            ("skew_clock", clock),
            ("radial_clock", radial),
            ("physical_ticks", physical_ticks),
        ):
            object.__setattr__(record, name, value)
        cylinder_snapshot = _cylinder_snapshot(cylinder)
        clock_snapshot = _clock_snapshot(clock)
        object.__setattr__(
            record,
            "_binding",
            (
                source,
                repetitions,
                odd_symbols,
                action,
                cylinder,
                cylinder_snapshot,
                clock,
                clock_snapshot,
                radial,
                radial.scale,
                radial.scale.growths,
                radial.scale.halvings,
                physical_ticks,
                action.coefficient_snapshot(),
            ),
        )
        object.__setattr__(record, "_issuer", record)
        return record

    @classmethod
    def from_boundary_macro(
        cls,
        macro: CollatzBoundaryMacro,
        repetitions: int,
        *,
        evaluator: GrowthArithmeticEvaluator | None = None,
        preflight: Callable[[int], None] | None = None,
        precision: int = 32,
    ) -> GuardedSkewCylinderPower:
        from number_compiler.sequences.collatz.boundary_macros import (
            CollatzBoundaryMacro,
            validate_boundary_macro,
        )
        from number_compiler.sequences.collatz.innovation_input_tape import (
            boundary_macro_specs,
        )

        if type(macro) is not CollatzBoundaryMacro:
            raise TypeError("named parity power requires its issued boundary macro")
        validate_boundary_macro(macro)
        clock = SkewQuadraticClock.factors(boundary_macro_specs(macro), precision)
        return cls._from_issued_action(
            source=macro.source,
            expected_endpoint=macro.endpoint,
            action=macro.fields,
            odd_symbols=macro.odd_symbols,
            physical_ticks=macro.physical_ticks,
            clock=clock,
            repetitions=repetitions,
            evaluator=evaluator,
            preflight=preflight,
        )

    @classmethod
    def from_border_return(
        cls,
        macro: BorderReturnMacro,
        repetitions: int,
        *,
        evaluator: GrowthArithmeticEvaluator | None = None,
        preflight: Callable[[int], None] | None = None,
        precision: int = 32,
    ) -> GuardedSkewCylinderPower:
        from number_compiler.sequences.collatz.border_return_grammar import (
            BorderReturnMacro,
            validate_border_return_macro,
        )

        if type(macro) is not BorderReturnMacro:
            raise TypeError("6305 power requires its issued return macro")
        validate_border_return_macro(macro)
        factors = tuple(((bit,), count) for bit, count in macro.parts)
        clock = SkewQuadraticClock.factors(factors, precision)
        return cls._from_issued_action(
            source=macro.source,
            expected_endpoint=macro.endpoint,
            action=macro.fields,
            odd_symbols=macro.odd_symbols,
            physical_ticks=macro.physical_ticks,
            clock=clock,
            repetitions=repetitions,
            evaluator=evaluator,
            preflight=preflight,
        )

    @classmethod
    def from_chain(
        cls,
        chain: UnifiedSkewChain,
        repetitions: int,
        *,
        evaluator: GrowthArithmeticEvaluator | None = None,
        preflight: Callable[[int], None] | None = None,
    ) -> GuardedSkewCylinderPower:
        from number_compiler.sequences.collatz.unified_skew_chain import (
            UnifiedSkewChain,
        )

        if type(chain) is not UnifiedSkewChain:
            raise TypeError("guarded power requires a producer-issued skew chain")
        chain.verify()
        return cls._from_issued_action(
            source=chain.source,
            expected_endpoint=chain.endpoint,
            action=chain.fields,
            odd_symbols=chain.odd_symbols,
            physical_ticks=chain.physical_ticks,
            clock=chain.clock,
            repetitions=repetitions,
            evaluator=evaluator,
            preflight=preflight,
            cylinder=chain.repeat_cylinder,
        )

    @classmethod
    def inspect_boundary_macro(
        cls,
        macro: CollatzBoundaryMacro,
        repetitions: int,
        *,
        evaluator: GrowthArithmeticEvaluator,
        precision: int = 32,
    ) -> tuple[RepeatedWordMooreCylinder, GuardedSkewCylinderPower | None]:
        """Build the defect class once, with a power only when admitted."""
        from number_compiler.sequences.collatz.boundary_macros import (
            CollatzBoundaryMacro,
            validate_boundary_macro,
        )
        from number_compiler.sequences.collatz.innovation_input_tape import (
            boundary_macro_specs,
        )

        if type(macro) is not CollatzBoundaryMacro:
            raise TypeError("named parity inspection requires its issued macro")
        validate_boundary_macro(macro)
        clock = SkewQuadraticClock.factors(boundary_macro_specs(macro), precision)
        return cls._inspect_issued_action(
            source=macro.source,
            expected_endpoint=macro.endpoint,
            action=macro.fields,
            odd_symbols=macro.odd_symbols,
            physical_ticks=macro.physical_ticks,
            clock=clock,
            repetitions=repetitions,
            evaluator=evaluator,
        )

    @classmethod
    def inspect_border_return(
        cls,
        macro: BorderReturnMacro,
        repetitions: int,
        *,
        evaluator: GrowthArithmeticEvaluator,
        precision: int = 32,
    ) -> tuple[RepeatedWordMooreCylinder, GuardedSkewCylinderPower | None]:
        """Inspect a source-bound 6305 word without recomputing its defect."""
        from number_compiler.sequences.collatz.border_return_grammar import (
            BorderReturnMacro,
            validate_border_return_macro,
        )

        if type(macro) is not BorderReturnMacro:
            raise TypeError("6305 inspection requires its issued return macro")
        validate_border_return_macro(macro)
        factors = tuple(((bit,), count) for bit, count in macro.parts)
        clock = SkewQuadraticClock.factors(factors, precision)
        return cls._inspect_issued_action(
            source=macro.source,
            expected_endpoint=macro.endpoint,
            action=macro.fields,
            odd_symbols=macro.odd_symbols,
            physical_ticks=macro.physical_ticks,
            clock=clock,
            repetitions=repetitions,
            evaluator=evaluator,
        )

    @classmethod
    def inspect_chain(
        cls,
        chain: UnifiedSkewChain,
        repetitions: int,
        *,
        evaluator: GrowthArithmeticEvaluator,
    ) -> tuple[RepeatedWordMooreCylinder, GuardedSkewCylinderPower | None]:
        """Inspect a chain and return its one computed same-word class."""
        from number_compiler.sequences.collatz.unified_skew_chain import (
            UnifiedSkewChain,
        )

        if type(chain) is not UnifiedSkewChain:
            raise TypeError("guarded inspection requires a producer-issued chain")
        chain.verify()
        return cls._inspect_issued_action(
            source=chain.source,
            expected_endpoint=chain.endpoint,
            action=chain.fields,
            odd_symbols=chain.odd_symbols,
            physical_ticks=chain.physical_ticks,
            clock=chain.clock,
            repetitions=repetitions,
            evaluator=evaluator,
            cylinder=chain.repeat_cylinder,
        )

    @classmethod
    def _inspect_issued_action(
        cls,
        *,
        source: int,
        expected_endpoint: int,
        action: DyadicTerminalFieldAction,
        odd_symbols: int,
        physical_ticks: int,
        clock: SkewQuadraticClock | None,
        repetitions: int,
        evaluator: GrowthArithmeticEvaluator,
        cylinder: RepeatedWordMooreCylinder | None = None,
    ) -> tuple[RepeatedWordMooreCylinder, GuardedSkewCylinderPower | None]:
        repetitions = require_integer(repetitions, "inspected repetition count", 1)
        if type(evaluator) is not GrowthArithmeticEvaluator:
            raise TypeError("same-word inspection requires its growth evaluator")
        if cylinder is None:
            cylinder = RepeatedWordMooreCylinder.from_action(
                action, source, evaluator=evaluator
            )
        else:
            if type(cylinder) is not RepeatedWordMooreCylinder:
                raise ValueError("inspected repeat class is not issued")
            cylinder.verify_for(action, source)
        if not cylinder.admits(repetitions):
            return cylinder, None
        power = cls._from_issued_action(
            source=source,
            expected_endpoint=expected_endpoint,
            action=action,
            odd_symbols=odd_symbols,
            physical_ticks=physical_ticks,
            clock=clock,
            repetitions=repetitions,
            evaluator=None,
            preflight=None,
            cylinder=cylinder,
        )
        return cylinder, power

    @classmethod
    def from_chain_fitting(
        cls,
        chain: UnifiedSkewChain,
        maximum_repetitions: int,
        *,
        preflight: Callable[[int], None],
    ) -> GuardedSkewCylinderPower | None:
        """Power as many repeated words as fit both clocks and source guard."""
        from number_compiler.sequences.collatz.unified_skew_chain import (
            UnifiedSkewChain,
        )

        if type(chain) is not UnifiedSkewChain:
            raise TypeError("guarded power requires a producer-issued skew chain")
        chain.verify()
        maximum_repetitions = require_integer(
            maximum_repetitions, "maximum guarded repetition count", 1
        )
        if not callable(preflight):
            raise TypeError("fitting a guarded power requires a run-work preflight")
        cylinder = chain.repeat_cylinder
        if cylinder is None:
            cylinder = RepeatedWordMooreCylinder.from_action(
                chain.fields, chain.source, preflight=preflight
            )
        accepted = (
            maximum_repetitions
            if cylinder.remaining_repetitions is None
            else min(maximum_repetitions, cylinder.remaining_repetitions)
        )
        if accepted <= 1:
            return None
        return cls._from_issued_action(
            source=chain.source,
            expected_endpoint=chain.endpoint,
            action=chain.fields,
            odd_symbols=chain.odd_symbols,
            physical_ticks=chain.physical_ticks,
            clock=chain.clock,
            repetitions=accepted,
            evaluator=None,
            preflight=preflight,
            cylinder=cylinder,
        )

    @classmethod
    def _from_issued_action(
        cls,
        *,
        source: int,
        expected_endpoint: int,
        action: DyadicTerminalFieldAction,
        odd_symbols: int,
        physical_ticks: int,
        clock: SkewQuadraticClock | None,
        repetitions: int,
        evaluator: GrowthArithmeticEvaluator | None,
        preflight: Callable[[int], None] | None,
        cylinder: RepeatedWordMooreCylinder | None = None,
    ) -> GuardedSkewCylinderPower:
        repetitions = require_integer(repetitions, "guarded repetition count", 0)
        if (
            type(action) is not DyadicTerminalFieldAction
            or not action.producer_issued
            or type(odd_symbols) is not int
            or odd_symbols < 0
            or type(physical_ticks) is not int
            or physical_ticks != action.steps + odd_symbols
        ):
            raise ValueError("issued clocks differ from their source action")
        if type(expected_endpoint) is not int or expected_endpoint <= 0:
            raise ValueError("issued parity action has no exact endpoint witness")
        if cylinder is None:
            cylinder = RepeatedWordMooreCylinder.from_action(
                action, source, evaluator=evaluator, preflight=preflight
            )
        else:
            if type(cylinder) is not RepeatedWordMooreCylinder:
                raise ValueError("fitted repeat class is not issued")
            cylinder.verify_for(action, source)
            if not cylinder.admits(repetitions):
                raise ValueError("fitted repeat class belongs to another parity action")
        if not cylinder.admits(repetitions):
            raise ValueError("power crosses the admitted repeated-word cylinder")
        if clock is not None:
            clock.verify(action, source, expected_endpoint)
            if (clock.steps, clock.odds) != (action.steps, odd_symbols):
                raise ValueError("quadratic clock is detached from the issued action")
        radial = RadialSturmianClock(
            HomogeneousGrowthScale(odd_symbols, action.steps)
        ).power(repetitions)
        powered_clock = clock.power(repetitions) if clock is not None else None
        if powered_clock is not None and powered_clock.radial_sturmian_clock != radial:
            raise AssertionError("quadratic and radial powers disagree")
        return cls._issue(
            source,
            repetitions,
            odd_symbols,
            action,
            cylinder,
            powered_clock,
            radial,
            physical_ticks * repetitions,
        )

    def verify(self) -> None:
        action_value: object = getattr(self, "action", None)
        cylinder_value: object = getattr(self, "cylinder", None)
        skew_clock_value: object = getattr(self, "skew_clock", None)
        radial_clock = self.radial_clock
        if not _is_exact_instance(action_value, DyadicTerminalFieldAction):
            raise ValueError("guarded skew-power authority fields were altered")
        if not _is_exact_instance(cylinder_value, RepeatedWordMooreCylinder):
            raise ValueError("guarded skew-power authority fields were altered")
        if skew_clock_value is not None and not _is_exact_instance(
            skew_clock_value, SkewQuadraticClock
        ):
            raise ValueError("guarded skew-power authority fields were altered")
        if not _is_exact_instance(radial_clock, RadialSturmianClock):
            raise ValueError("guarded skew-power authority fields were altered")
        action = action_value
        cylinder = cylinder_value
        skew_clock = skew_clock_value
        source_value: object = getattr(self, "source", None)
        repetitions_value: object = getattr(self, "repetitions", None)
        odd_symbols_value: object = getattr(self, "odd_symbols", None)
        physical_ticks_value: object = getattr(self, "physical_ticks", None)
        if any(
            type(value) is not int
            for value in (
                source_value,
                repetitions_value,
                odd_symbols_value,
                physical_ticks_value,
            )
        ):
            raise ValueError("guarded skew-power scalar fields were altered")
        source = cast(int, source_value)
        repetitions = cast(int, repetitions_value)
        odd_symbols = cast(int, odd_symbols_value)
        physical_ticks = cast(int, physical_ticks_value)
        binding = getattr(self, "_binding", None)
        if (
            type(self) is not GuardedSkewCylinderPower
            or getattr(self, "_issuer", None) is not self
            or not is_exact_object_tuple(binding)
            or len(binding) != 14
            or source is not binding[0]
            or repetitions is not binding[1]
            or odd_symbols is not binding[2]
            or action is not binding[3]
            or cylinder is not binding[4]
            or skew_clock is not binding[6]
            or self.radial_clock is not binding[8]
            or radial_clock.scale is not binding[9]
            or radial_clock.scale.growths is not binding[10]
            or radial_clock.scale.halvings is not binding[11]
            or physical_ticks is not binding[12]
            or action.coefficient_snapshot() != binding[13]
        ):
            raise ValueError("guarded skew-power seal is invalid")
        if _cylinder_snapshot(cylinder) != binding[5]:
            raise ValueError("guarded skew-power defect snapshot changed")
        cylinder.verify_for(action, source)
        if skew_clock is not None and _clock_snapshot(skew_clock) != binding[7]:
            raise ValueError("guarded skew-power clock snapshot changed")
        if (
            not action.producer_issued
            or not action.certifies(source)
            or cylinder.source != source
            or cylinder.normalized_steps != action.steps
            or cylinder.gain != action.gain
            or cylinder.offset != action.offset
            or not cylinder.admits(repetitions)
            or radial_clock.scale
            != HomogeneousGrowthScale(
                odd_symbols * repetitions,
                action.steps * repetitions,
            )
            or physical_ticks != (action.steps + odd_symbols) * repetitions
            or (
                skew_clock is not None
                and skew_clock.radial_sturmian_clock != radial_clock
            )
        ):
            raise ValueError("guarded temporal power does not match its source word")

    @property
    def normalized_steps(self) -> int:
        return self.action.steps * self.repetitions

    @property
    def next_repeat_class(self) -> int | None:
        self.verify()
        return self.cylinder.after(self.repetitions)

    @property
    def materialization_bound_bits(self) -> int:
        """Conservative preflight for coefficients and the source endpoint."""
        self.verify()
        coefficient_bits = max(
            self.action.gain.bit_length(),
            abs(self.action.offset).bit_length(),
            self.action.sum_gain.bit_length(),
            abs(self.action.sum_offset).bit_length(),
            self.action.previous_gain.bit_length(),
            abs(self.action.previous_offset).bit_length(),
            1,
        )
        total_steps = self.normalized_steps
        return (
            self.source.bit_length()
            + 4 * total_steps
            + coefficient_bits
            + self.repetitions.bit_length()
            + 32
        )

    def radial_leading_binary(
        self, evaluator: GrowthArithmeticEvaluator, width: int = 8
    ) -> RadialSturmianPacket:
        self.verify()
        return self.radial_clock.leading_binary(evaluator, width)

    def demanded_homogeneous_difference(
        self, *, base: int, places: int, exponent_gap: int
    ) -> dict[str, object]:
        """Join this source-admitted power to demanded homogeneous 3**q ports."""
        self.verify()
        if type(base) is not int or base not in (3, 6, 10, 64):
            raise ValueError("unsupported Collatz difference radix")
        if type(places) is not int or not 1 <= places <= 64:
            raise ValueError("difference places must be in 1..64")
        if type(exponent_gap) is not int or exponent_gap < 1:
            raise ValueError("difference exponent gap must be positive")
        q = self.odd_symbols * self.repetitions
        if self.radial_clock.scale.growths != q:
            raise AssertionError("radial and powered innovation exponents disagree")
        modulus = base**places
        orbit = ThreePowerRadixOrbit("ordinary", q, base)
        residue = orbit.residue(places)
        tripling_carry = 3 * residue // modulus
        doubling_carry = 2 * residue // modulus
        forward_borrow = orbit.forward_innovation_borrow(places)
        pivot = orbit.forward_difference_xor(places)
        raw, valuation, normalized = difference_power_block(q, exponent_gap, modulus)
        packet: dict[str, object] = {
            "base": base,
            "places": places,
            "powered_odd_exponent": q,
            "exponent_gap": exponent_gap,
            "tripling_carry": tripling_carry,
            "doubling_carry": doubling_carry,
            "power_difference_borrow": tripling_carry - doubling_carry,
            "forward_innovation_borrow": forward_borrow,
            "forward_xor": pivot,
            "raw_difference_modulus": raw,
            "exact_dyadic_factors": valuation,
            "normalized_difference_modulus": normalized,
            "scope": "source-certified homogeneous action; affine guard unchanged",
        }
        if base == 64 and places == 64:
            mask = orbit.forward_mask(64, "forward_difference_xor")
            packet["forward_xor_mask"] = mask
            packet["walsh64_mod5"] = walsh64_mod5(mask)
        return packet

    def observation(
        self,
        evaluator: GrowthArithmeticEvaluator | None = None,
        *,
        width: int = 8,
        difference_request: tuple[int, int, int] | None = None,
    ) -> dict[str, object]:
        """Describe the admitted word power without implying family closure."""
        self.verify()
        packet: dict[str, object] = {
            "source": self.source,
            "normalized_word_steps": self.action.steps,
            "word_odd_symbols": self.odd_symbols,
            "requested_repetitions": self.repetitions,
            "remaining_repetition_class": self.next_repeat_class,
            "repeated_physical_ticks": self.physical_ticks,
            "quadratic_clock_published": self.skew_clock is not None,
            "scope": "same source-admitted parity word only; no next-family claim",
        }
        powered_f5 = project_dyadic_fields_f5(self.action).power(self.repetitions)
        packet["powered_f5_action"] = {
            "scale": powered_f5.scale,
            "offset": powered_f5.offset,
            "source_residue": self.source % 5,
            "endpoint_residue": powered_f5.apply(self.source % 5),
        }
        if difference_request is not None:
            if type(difference_request) is not tuple or len(difference_request) != 3:
                raise ValueError("difference request must be (base, places, gap)")
            base, places, gap = difference_request
            packet["powered_difference"] = self.demanded_homogeneous_difference(
                base=base, places=places, exponent_gap=gap
            )
        if self.skew_clock is not None:
            packet["quadratic_clock"] = {
                "steps": self.skew_clock.steps,
                "odds": self.skew_clock.odds,
                "value": self.skew_clock.value,
                "linear": self.skew_clock.linear,
                "quadratic": self.skew_clock.quadratic,
                "position_sum": self.skew_clock.position_sum,
                "first_odd": self.skew_clock.first_odd,
                "last_odd": self.skew_clock.last_odd,
            }
        if evaluator is not None:
            from dataclasses import asdict

            packet["radial_sturmian"] = asdict(
                self.radial_leading_binary(evaluator, width)
            )
        return packet

    def materialize(
        self,
        *,
        max_materialization_bits: int,
        evaluator: GrowthArithmeticEvaluator | None = None,
        preflight: Callable[[int], None] | None = None,
    ) -> tuple[DyadicTerminalFieldAction, int]:
        """Demand exact powered coefficients and endpoint under an explicit cap."""
        self.verify()
        max_materialization_bits = require_integer(
            max_materialization_bits, "temporal-power materialization budget", 1
        )
        if (evaluator is None) == (preflight is None):
            raise TypeError("power materialization requires one work owner")
        required = self.materialization_bound_bits
        if required > max_materialization_bits:
            if evaluator is not None:
                evaluator.ledger.bump(_shared_keys.GROWTH_ARITHMETIC_BUDGET_REFUSALS)
            raise BlockContextBudgetExceeded(
                "powered coefficients and endpoint exceed the explicit bit budget"
            )
        if evaluator is not None:
            if type(evaluator) is not GrowthArithmeticEvaluator:
                raise TypeError("power evaluator has another owner")
            coefficient_bits = required - self.source.bit_length()
            work_units = max(1, self.normalized_steps * coefficient_bits)
            operand_bits = (
                self.source.bit_length()
                + self.action.gain.bit_length()
                + abs(self.action.offset).bit_length()
                + self.normalized_steps
            )
            with evaluator.charge_work(
                work_units,
                0,
                operand_bits,
                storage_bits=required,
            ):
                return self._materialize_admitted(max_materialization_bits)
        assert preflight is not None
        preflight(required)
        return self._materialize_admitted(max_materialization_bits)

    def _materialize_admitted(
        self, max_materialization_bits: int
    ) -> tuple[DyadicTerminalFieldAction, int]:
        powered = self.action.power(self.repetitions)
        coefficient_sizes = (
            powered.gain.bit_length(),
            abs(powered.offset).bit_length(),
            powered.sum_gain.bit_length(),
            abs(powered.sum_offset).bit_length(),
            powered.previous_gain.bit_length(),
            abs(powered.previous_offset).bit_length(),
        )
        if max(coefficient_sizes) > max_materialization_bits:
            raise AssertionError(
                "powered action exceeded its preflight coefficient cap"
            )
        if not powered.certifies(self.source):
            raise AssertionError("defect guard disagrees with powered source action")
        endpoint = powered.endpoint(self.source)
        if endpoint.bit_length() > max_materialization_bits:
            raise AssertionError("powered endpoint exceeded its preflight bit cap")
        if self.skew_clock is not None:
            self.skew_clock.verify(powered, self.source, endpoint)
        return powered, endpoint

    def high_digit_transport(
        self,
        width: int = 8,
        *,
        max_materialization_bits: int,
        evaluator: GrowthArithmeticEvaluator | None = None,
        preflight: Callable[[int], None] | None = None,
    ) -> AffineHighDigitTransport:
        """Materialize this admitted power, then observe its signed high carry."""
        from number_compiler.arithmetic.fields.affine_high_digits import (
            affine_high_digit_transport,
        )

        action, endpoint = self.materialize(
            max_materialization_bits=max_materialization_bits,
            evaluator=evaluator,
            preflight=preflight,
        )
        return affine_high_digit_transport(endpoint, action.offset, action.steps, width)


__all__ = ["GuardedSkewCylinderPower"]
