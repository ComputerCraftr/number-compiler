"""Positive source fibers for exact Mahler carry and odd-run transport.

The interval/congruence arithmetic lives in ``IntegerCylinder``.  This
family wrapper supplies only the positive odd-source constructor and the
source-issued Mahler action/next-exponent rules.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Literal

from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational,
    HalfOpenInterval,
)
from number_compiler.arithmetic.fields.integer_cylinder import IntegerCylinder
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import antihydra as _antihydra_keys
from number_compiler.sequences.antihydra.mahler_odd_macro import (
    MahlerOddToOddAction,
)

_MAX_BINARY_PRECISION = 8192
_MAX_FIVE_PLACES = 32
_MAX_SUMMARY_UPPER_BITS = 8192


def _fiber_operand_bits(fiber: MahlerGuardedSourceFiber) -> int:
    cylinder = fiber.integers
    integer_operands = (
        cylinder.lower,
        cylinder.upper,
        cylinder.residue,
        cylinder.modulus,
        fiber.ledger_balance,
    )
    rational_operands = (
        fiber.fractional_guard.lower,
        fiber.fractional_guard.upper,
    )
    return sum(abs(value).bit_length() for value in integer_operands) + sum(
        abs(value.numerator).bit_length() + value.denominator.bit_length()
        for value in rational_operands
    )


def _action_operand_bits(action: MahlerOddToOddAction) -> int:
    return sum(
        abs(value).bit_length()
        for value in (
            action.extent,
            action.joint.gain,
            action.joint.innovation,
            action.source_residue,
            action.source_modulus,
            action.delta,
            action.minimum,
        )
    )


@dataclass(frozen=True, slots=True)
class MahlerTwoSidedCylinder(IntegerCylinder):
    """Exact positive integer members in a leading interval and low coset."""

    def __post_init__(self) -> None:
        super(MahlerTwoSidedCylinder, self).__post_init__()
        if self.lower < 1:
            raise ValueError("Mahler source fibers contain only positive integers")

    @classmethod
    def from_pointed_source(
        cls,
        source: int,
        *,
        binary_bits: int,
        five_places: int,
        leading_bits: int,
        ledger: ResourceLedger | None = None,
    ) -> MahlerTwoSidedCylinder:
        """Build an upper-prefix interval intersected with exact 2/5 suffixes."""
        if type(source) is not int or source <= 0 or source % 2 != 1:
            raise ValueError("pointed Mahler source must be positive odd")
        if (
            type(binary_bits) is not int
            or not 1 <= binary_bits <= _MAX_BINARY_PRECISION
            or type(five_places) is not int
            or not 0 <= five_places <= _MAX_FIVE_PLACES
            or type(leading_bits) is not int
            or not 1 <= leading_bits <= source.bit_length()
        ):
            raise ValueError("two-sided observation needs finite source precisions")
        if ledger is not None and type(ledger) is not ResourceLedger:
            raise TypeError("Mahler cylinder accounting needs its query ledger")
        if ledger is not None:
            # Precharge a conservative operand-size estimate before shifts,
            # modular reduction or constructing the finite coset modulus.
            source_bits = source.bit_length()
            modulus_bits_bound = binary_bits + 3 * five_places
            ledger.bump(
                _antihydra_keys.MAHLER_SOURCE_ARITHMETIC_OPERAND_BITS,
                4 * source_bits
                + 2 * modulus_bits_bound
                + binary_bits
                + five_places
                + leading_bits,
            )
        offset = source.bit_length() - leading_bits
        leading = source >> offset
        lower = max(1, leading << offset)
        upper = ((leading + 1) << offset) - 1
        modulus = (1 << binary_bits) * 5**five_places
        return cls(lower, upper, source % modulus, modulus)

    @property
    def binary_precision(self) -> int:
        """Number of authenticated low binary bits in the full coset stride."""
        return v2_positive(self.modulus)

    def admitted_by(
        self, action: MahlerOddToOddAction
    ) -> MahlerTwoSidedCylinder | None:
        """Restrict this source fiber to an already issued odd-return word."""
        if type(action) is not MahlerOddToOddAction:
            raise TypeError("Mahler admission needs an issued odd-to-odd action")
        action.verify_issued()
        return self.intersect_congruence(action.source_residue, action.source_modulus)

    def transport(self, action: MahlerOddToOddAction) -> MahlerTwoSidedCylinder:
        """Transport the complete admitted progression, retaining its 3-power."""
        if type(action) is not MahlerOddToOddAction:
            raise TypeError("Mahler transport needs an issued odd-to-odd action")
        action.verify_issued()
        admitted = self.admitted_by(action)
        if admitted is None or admitted.count != self.count:
            raise ValueError("source fiber does not imply the complete action guard")
        if action.extent == 0:
            return admitted
        transported = admitted.affine_image(
            action.joint.gain,
            action.joint.innovation,
            1 << action.extent,
        )
        if transported.count != admitted.count:
            raise ArithmeticError("Mahler transport changed source-fiber cardinality")
        if transported.first % 2 != 1 or transported.last % 2 != 1:
            raise ArithmeticError("odd-to-odd action lost endpoint parity")
        return transported

    @property
    def forced_next_odd_exponent(self) -> int | None:
        """Return the exact next valuation only when every member agrees."""
        first = self.first
        if first % 2 == 0:
            return None
        if self.count == 1:
            return v2_positive(3 * first + 1)
        precision = self.binary_precision
        if precision == 0:
            return None
        valuation = v2_positive(3 * self.residue + 1)
        return valuation if valuation < precision else None

    def next_forced_event(
        self,
        *,
        max_extent: int = 4096,
    ) -> tuple[MahlerOddToOddAction, MahlerTwoSidedCylinder] | None:
        """Issue one source-wide odd event, or stop at the first unknown inlet."""
        if type(max_extent) is not int or not 1 <= max_extent <= 4096:
            raise ValueError("Mahler event extent must be in 1..4096")
        exponent = self.forced_next_odd_exponent
        if exponent is None or exponent > max_extent:
            return None
        action = MahlerOddToOddAction.run(exponent, max_extent=max_extent)
        restricted = self.admitted_by(action)
        if restricted is None or restricted.count != self.count:
            raise ArithmeticError("forced Mahler exponent did not admit every source")
        # A point/fiber may imply the action guard only after intersecting the
        # stronger source coset with it.  Transport that admitted coset: its
        # stride carries the guard even when the original finite fiber is a
        # singleton and its ambient modulus is too small to imply it.
        return action, restricted.transport(action)

    def forced_future(
        self,
        *,
        max_events: int = 16,
        max_extent: int = 4096,
    ) -> tuple[MahlerOddToOddAction, MahlerTwoSidedCylinder, int]:
        """Compose the finite forced prefix; no continuation is inferred at a gap."""
        if type(max_events) is not int or max_events < 0:
            raise ValueError("forced future event budget must be natural")
        if type(max_extent) is not int or not 1 <= max_extent <= 4096:
            raise ValueError("forced future extent must be in 1..4096")
        action = MahlerOddToOddAction.identity()
        cylinder = self
        events = 0
        for _ in range(max_events):
            remaining = max_extent - action.extent
            if remaining < 1:
                break
            step = cylinder.next_forced_event(max_extent=remaining)
            if step is None:
                break
            next_action, target = step
            action = action.then(next_action)
            cylinder = target
            events += 1
        return action, cylinder, events

    def leading_binary(self, width: int) -> tuple[int, int] | None:
        """Return the common exact leading prefix only when both endpoints agree."""
        if type(width) is not int or width < 1:
            raise ValueError("leading binary width must be positive")
        if self.first.bit_length() != self.last.bit_length():
            return None
        source_width = self.first.bit_length()
        if width > source_width:
            return None
        shift = source_width - width
        first_prefix, last_prefix = self.first >> shift, self.last >> shift
        return (width, first_prefix) if first_prefix == last_prefix else None

    def low_ports(self, bits: int, five_places: int) -> tuple[int, int] | None:
        """Return exactly forced low binary and 5-adic digits."""
        if (
            type(bits) is not int
            or type(five_places) is not int
            or bits < 0
            or five_places < 0
            or five_places > _MAX_FIVE_PLACES
            or bits > self.binary_precision
        ):
            return None
        five_power = 5**five_places if five_places else 1
        if self.modulus % five_power:
            return None
        return (
            self.residue % (1 << bits) if bits else 0,
            self.residue % five_power if five_places else 0,
        )

    def summary(
        self,
        *,
        upper_bits: int = 8,
        low_bits: int = 8,
        five_places: int = 2,
        ledger: ResourceLedger | None = None,
    ) -> dict[str, object]:
        if (
            type(upper_bits) is not int
            or not 1 <= upper_bits <= _MAX_SUMMARY_UPPER_BITS
            or type(low_bits) is not int
            or not 0 <= low_bits <= _MAX_BINARY_PRECISION
            or type(five_places) is not int
            or not 0 <= five_places <= _MAX_FIVE_PLACES
        ):
            raise ValueError("Mahler cylinder summary precision is outside its budget")
        if ledger is not None and type(ledger) is not ResourceLedger:
            raise TypeError("Mahler cylinder summary accounting needs its query ledger")
        if ledger is not None:
            operand_bits = sum(
                abs(value).bit_length()
                for value in (self.lower, self.upper, self.residue, self.modulus)
            )
            ledger.bump(
                _antihydra_keys.MAHLER_SOURCE_ARITHMETIC_OPERAND_BITS,
                4 * operand_bits + upper_bits + low_bits + 3 * five_places,
            )
        return {
            "interval": (self.lower, self.upper),
            "source_coset": (self.residue, self.modulus),
            "candidate_count": self.count,
            "binary_precision": self.binary_precision,
            "forced_upper_binary": self.leading_binary(upper_bits),
            "forced_lower_radices": self.low_ports(low_bits, five_places),
            "forced_next_odd_exponent": self.forced_next_odd_exponent,
            "all_time_claim": False,
        }


class MahlerFractionalGuardEmpty(ValueError):
    """The integer action is admitted but no strict fractional input survives."""


class MahlerLedgerUnsafe(ValueError):
    """The exact action's prefix ledger minimum rejects the incoming balance."""


@dataclass(frozen=True, slots=True)
class MahlerGuardedSourceFiber:
    """Finite product of source integers, fractional inputs and ledger balance.

    This is an exact finite continuation domain. The carried balance and
    interval are explicit coordinates; the object makes no claim that every
    source integer corresponds to an Antihydra execution or that the fiber is
    nonempty at every future step.
    """

    integers: MahlerTwoSidedCylinder
    fractional_guard: HalfOpenInterval = field(default_factory=HalfOpenInterval)
    ledger_balance: int = 0

    def __post_init__(self) -> None:
        if type(self.integers) is not MahlerTwoSidedCylinder:
            raise TypeError("guarded Mahler fiber requires its integer cylinder")
        if type(self.fractional_guard) is not HalfOpenInterval:
            raise TypeError(
                "guarded Mahler fiber requires an exact fractional interval"
            )
        if type(self.ledger_balance) is not int:
            raise TypeError("guarded Mahler ledger balance must be an exact integer")
        if self.integers.first % 2 != 1 or (
            self.integers.count > 1 and self.integers.modulus % 2 != 0
        ):
            raise ValueError("odd source fiber must contain only odd integers")

    def advance(self, action: MahlerOddToOddAction) -> MahlerGuardedSourceFiber:
        """Transport all three coordinates only under complete exact guards."""
        if type(action) is not MahlerOddToOddAction:
            raise TypeError("guarded fiber transport requires an issued odd action")
        action.verify_issued()
        admitted = self.integers.admitted_by(action)
        if admitted is None or admitted.count != self.integers.count:
            raise ValueError("odd action does not admit the complete integer fiber")
        fractional_input = self.fractional_guard.intersect(action.joint.guard)
        if fractional_input.empty:
            raise MahlerFractionalGuardEmpty(
                "integer source guard is valid but strict fractional guard is empty"
            )
        if self.ledger_balance + action.minimum < 0:
            raise MahlerLedgerUnsafe(
                "odd action violates its exact prefix ledger guard"
            )

        # ``admitted`` retains any extra guard precision required by the
        # action.  In particular a singleton can become a guarded singleton
        # with a larger modulus; transporting the unrefined ambient cylinder
        # would incorrectly reject it for insufficient stride divisibility.
        target = admitted.transport(action)
        denominator = action.joint.source_modulus
        scale = ExactRational(action.joint.gain, denominator)
        offset = ExactRational(-action.joint.innovation, denominator)
        fractional_output = HalfOpenInterval(
            scale * fractional_input.lower + offset,
            scale * fractional_input.upper + offset,
        )
        return MahlerGuardedSourceFiber(
            target, fractional_output, self.ledger_balance + action.delta
        )

    def forced_future(
        self,
        *,
        max_events: int = 16,
        max_extent: int = 128,
        ledger: ResourceLedger | None = None,
    ) -> tuple[
        MahlerOddToOddAction,
        MahlerGuardedSourceFiber,
        int,
        Literal[
            "event_limit",
            "extent_limit",
            "fractional_guard",
            "ledger_safety",
            "source_not_forced",
        ],
    ]:
        """Build only the finite uniformly forced, fully guarded prefix."""
        if type(max_events) is not int or not 0 <= max_events <= 128:
            raise ValueError("forced-future event budget must be in 0..128")
        if type(max_extent) is not int or not 1 <= max_extent <= 4096:
            raise ValueError("forced-future bit budget must be in 1..4096")
        if ledger is not None and type(ledger) is not ResourceLedger:
            raise TypeError("Mahler forced-future accounting needs its query ledger")
        total = MahlerOddToOddAction.identity()
        state = self
        accepted = 0
        reason: Literal[
            "event_limit",
            "extent_limit",
            "fractional_guard",
            "ledger_safety",
            "source_not_forced",
        ] = "event_limit"
        for _ in range(max_events):
            if ledger is not None:
                ledger.bump(
                    _antihydra_keys.MAHLER_SOURCE_ARITHMETIC_OPERAND_BITS,
                    _fiber_operand_bits(state),
                )
            exponent = state.integers.forced_next_odd_exponent
            if exponent is None:
                reason = "source_not_forced"
                break
            remaining = max_extent - total.extent
            if exponent > remaining:
                reason = "extent_limit"
                break
            step = MahlerOddToOddAction.run(exponent, max_extent=remaining)
            if ledger is not None:
                ledger.bump(
                    _antihydra_keys.MAHLER_SOURCE_ARITHMETIC_OPERAND_BITS,
                    _action_operand_bits(step),
                )
            try:
                target = state.advance(step)
            except MahlerFractionalGuardEmpty:
                reason = "fractional_guard"
                break
            except MahlerLedgerUnsafe:
                reason = "ledger_safety"
                break
            total = total.then(step)
            state = target
            accepted += 1
        return total, state, accepted, reason


__all__ = (
    "MahlerFractionalGuardEmpty",
    "MahlerGuardedSourceFiber",
    "MahlerLedgerUnsafe",
    "MahlerTwoSidedCylinder",
)
