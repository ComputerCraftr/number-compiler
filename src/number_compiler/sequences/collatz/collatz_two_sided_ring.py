"""Exact upper-interval / lower-CRT source cylinders for Collatz border rings.

A source is *a finite coset in an integer interval*, not a reconstructed
sequence of interior digits.  An authenticated affine parity-word moves its
ENTIRE coset, including its full 3-primary stride; a divided 2-adic modulus
must never be substituted for that image.  The next 6305 carry/tail is forced
only when all source alternatives share its valuation.  Otherwise the exact
conditional splitting operation retains every admissible alternative.

This is a conditional finite-horizon successor interface.  The Sturmian
homogeneous phase constrains upper scaling but does not certify affine
endpoint digits or an unknown future parity word by itself.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.integer_cylinder import IntegerCylinder
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.collatz_digit_coverage import (
        Radix6DigitCoverage,
    )


def _record_cylinder_operand_bits(ledger: ResourceLedger | None, *values: int) -> None:
    if ledger is not None:
        ledger.bump(
            _collatz_keys.COLLATZ_TWO_SIDED_CYLINDER_OPERAND_BITS,
            sum(value.bit_length() for value in values),
        )


@dataclass(frozen=True, slots=True)
class CollatzTwoSidedCylinder(IntegerCylinder):
    """Exactly ``[lower,upper] ∩ {n ≡ residue (mod modulus)}``.

    The large affine stride is retained, including any acquired factor of 3.
    It is never projected down to a CRT observer for successor authorization.
    """

    def __post_init__(self) -> None:
        super(CollatzTwoSidedCylinder, self).__post_init__()
        if self.lower < 1 or self.upper < self.lower:
            raise ValueError("Collatz cylinder needs a positive interval")

    @classmethod
    def from_pointed_source(
        cls,
        source: int,
        *,
        binary_bits: int,
        five_places: int = 1,
        leading_bits: int = 8,
        ledger: ResourceLedger | None = None,
    ) -> CollatzTwoSidedCylinder:
        """Authenticate the upper source *itself* and its finite lower residue.

        Leading bits are read from the actual source, NEVER guessed from the
        homogeneous Sturmian scale. The class can contain several integers.
        """
        if type(source) is not int or source <= 0:
            raise ValueError("pointed Collatz source must be positive")
        if ledger is not None and type(ledger) is not ResourceLedger:
            raise TypeError("cylinder construction accounting needs a query ledger")
        if (
            type(binary_bits) is not int
            or not 1 <= binary_bits <= 8192
            or type(five_places) is not int
            or not 0 <= five_places <= 32
            or type(leading_bits) is not int
            or not 1 <= leading_bits <= source.bit_length()
        ):
            raise ValueError("two-sided precision is outside the bounded request")
        shift = source.bit_length() - leading_bits
        _record_cylinder_operand_bits(ledger, source, shift)
        prefix = source >> shift
        _record_cylinder_operand_bits(ledger, prefix, shift)
        lower = prefix << shift
        _record_cylinder_operand_bits(ledger, prefix, 1, shift)
        upper = ((prefix + 1) << shift) - 1
        _record_cylinder_operand_bits(ledger, 1, binary_bits)
        binary_modulus = 1 << binary_bits
        _record_cylinder_operand_bits(ledger, 5, five_places)
        five_modulus = 5**five_places
        _record_cylinder_operand_bits(ledger, binary_modulus, five_modulus)
        modulus = binary_modulus * five_modulus
        _record_cylinder_operand_bits(ledger, source, modulus)
        residue = source % modulus
        cylinder = cls(lower, upper, residue, modulus)
        if ledger is not None:
            ledger.bump(_collatz_keys.COLLATZ_TWO_SIDED_CYLINDER_CONSTRUCTIONS)
        return cylinder

    @property
    def binary_precision(self) -> int:
        return v2_positive(self.modulus)

    def forced_residue(self, modulus: int) -> int | None:
        """Exact same residue for every source, else a genuinely open inlet."""
        if type(modulus) is not int or modulus < 1:
            raise ValueError("radix residue modulus must be positive")
        if self.count == 1:
            return self.first % modulus
        return self.residue % modulus if self.modulus % modulus == 0 else None

    def intersect_interval(
        self,
        lower: int,
        upper: int,
        *,
        ledger: ResourceLedger | None = None,
    ) -> CollatzTwoSidedCylinder | None:
        if ledger is not None and type(ledger) is not ResourceLedger:
            raise TypeError("cylinder intersection accounting needs a query ledger")
        if type(lower) is not int or type(upper) is not int:
            return super(CollatzTwoSidedCylinder, self).intersect_interval(lower, upper)
        _record_cylinder_operand_bits(
            ledger, self.lower, self.upper, self.residue, self.modulus, lower, upper
        )
        result = super(CollatzTwoSidedCylinder, self).intersect_interval(lower, upper)
        if result is not None and ledger is not None:
            ledger.bump(_collatz_keys.COLLATZ_TWO_SIDED_CYLINDER_CONSTRUCTIONS)
        return result

    def intersect_congruence(
        self,
        residue: int,
        modulus: int,
        *,
        ledger: ResourceLedger | None = None,
    ) -> CollatzTwoSidedCylinder | None:
        if ledger is not None and type(ledger) is not ResourceLedger:
            raise TypeError("cylinder intersection accounting needs a query ledger")
        if type(residue) is not int or type(modulus) is not int:
            return super(CollatzTwoSidedCylinder, self).intersect_congruence(
                residue, modulus
            )
        _record_cylinder_operand_bits(
            ledger,
            self.lower,
            self.upper,
            self.residue,
            self.modulus,
            residue,
            modulus,
        )
        result = super(CollatzTwoSidedCylinder, self).intersect_congruence(
            residue, modulus
        )
        if result is not None and ledger is not None:
            ledger.bump(_collatz_keys.COLLATZ_TWO_SIDED_CYLINDER_CONSTRUCTIONS)
        return result

    def admitted_by(
        self, action: DyadicTerminalFieldAction, *, ledger: ResourceLedger | None = None
    ) -> CollatzTwoSidedCylinder | None:
        if type(action) is not DyadicTerminalFieldAction or not action.producer_issued:
            raise TypeError("two-sided admission requires a producer-issued action")
        return self.intersect_congruence(
            action.source_residue, action.source_modulus, ledger=ledger
        )

    def transport(
        self,
        action: DyadicTerminalFieldAction,
        *,
        ledger: ResourceLedger | None = None,
    ) -> CollatzTwoSidedCylinder:
        """Exact affine image of *all* admitted sources, conserving count.

        It is unsafe to divide a source stride by 2**steps unless the entire
        coset implies the full parity word, including all discarded bits.
        """
        if type(action) is not DyadicTerminalFieldAction or not action.producer_issued:
            raise TypeError("two-sided transport requires an issued parity action")
        if ledger is not None and type(ledger) is not ResourceLedger:
            raise TypeError("cylinder transport accounting needs a query ledger")
        _record_cylinder_operand_bits(ledger, 2, action.steps)
        denominator = 1 << action.steps
        admitted = self.admitted_by(action, ledger=ledger)
        if admitted is None or admitted.count != self.count:
            raise ValueError("unforced Collatz parity inlet")
        if action.steps == 0:
            return admitted

        def charge_affine_image(bits: int) -> None:
            if ledger is not None:
                ledger.bump(
                    _collatz_keys.COLLATZ_TWO_SIDED_CYLINDER_OPERAND_BITS,
                    bits,
                )

        out = admitted.affine_image(
            action.gain,
            action.offset,
            denominator,
            charge_bits=charge_affine_image if ledger is not None else None,
        )
        if type(out) is not CollatzTwoSidedCylinder or out.count != admitted.count:
            raise ArithmeticError("Collatz affine transport lost source alternatives")
        if ledger is not None:
            ledger.bump(_collatz_keys.COLLATZ_TWO_SIDED_CYLINDER_CONSTRUCTIONS)
        return out

    def radix6_coverage(
        self,
        *,
        max_leading_digits: int | None = None,
        max_trailing_digits: int | None = None,
        ledger: ResourceLedger | None = None,
    ) -> Radix6DigitCoverage | None:
        """Certify only exact high/low base-6 digit intervals."""
        from number_compiler.sequences.collatz.collatz_digit_coverage import (
            certify_radix6_coverage,
        )

        return certify_radix6_coverage(
            self,
            max_leading_digits=max_leading_digits,
            max_trailing_digits=max_trailing_digits,
            ledger=ledger,
        )

    @property
    def forced_next_6305_tail(self) -> int | None:
        """Next 3-ending return length common to every source in the coset.

        For x=10q+3, 3x+1=10(3q+1), so j=v2(3x+1)-1.
        Above the retained binary precision, valuations are not guessed.
        """
        if self.forced_residue(10) != 3:
            return None
        return self._forced_next_6305_tail_after_border()

    def _forced_next_6305_tail_after_border(self) -> int | None:
        """Compute the tail after the caller has established the 3-border."""
        if self.count == 1:
            return v2_positive(3 * self.first + 1) - 1
        precision = self.binary_precision
        if precision < 2:
            return None
        val = v2_positive(3 * self.residue + 1)
        return val - 1 if 1 <= val < precision else None

    def forced_next_return(
        self,
        *,
        max_tail: int = 4096,
        ledger: ResourceLedger | None = None,
        max_physical_ticks: int | None = None,
    ) -> tuple[int, DyadicTerminalFieldAction, CollatzTwoSidedCylinder] | None:
        """Publish one next 6305 word only when EVERY source admits it."""
        if type(max_tail) is not int or not 0 <= max_tail <= 4096:
            raise ValueError("requested tail budget is invalid")
        if ledger is not None and type(ledger) is not ResourceLedger:
            raise TypeError("border continuation accounting needs a query ledger")
        if max_physical_ticks is not None and (
            type(max_physical_ticks) is not int or max_physical_ticks < 0
        ):
            raise ValueError("physical return budget must be nonnegative")
        if ledger is not None:
            ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_CHECKS)
            _record_cylinder_operand_bits(
                ledger, self.lower, self.upper, self.residue, self.modulus, 10
            )
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_OPERAND_BITS,
                self.lower.bit_length()
                + self.upper.bit_length()
                + self.residue.bit_length()
                + self.modulus.bit_length()
                + (10).bit_length(),
            )
        if self.forced_residue(10) != 3:
            if ledger is not None:
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_REFUSALS
                )
            return None
        if ledger is not None:
            ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_VALUATION_CHECKS)
            _record_cylinder_operand_bits(
                ledger, self.lower, self.upper, self.residue, self.modulus, 3, 1
            )
        tail = self._forced_next_6305_tail_after_border()
        if tail is None or tail > max_tail:
            if ledger is not None:
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_REFUSALS
                )
            return None
        duration = tail + 4
        if max_physical_ticks is not None and duration > max_physical_ticks:
            if ledger is not None:
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_REFUSALS
                )
            return None
        if ledger is not None:
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
                tail.bit_length() + 1,
            )
        one = DyadicTerminalFieldAction.one_run(1)
        if ledger is not None:
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
                sum(value.bit_length() for value in one.coefficient_snapshot()),
            )
        zero = DyadicTerminalFieldAction.zero_run(tail)
        if ledger is not None:
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
                sum(value.bit_length() for value in zero.coefficient_snapshot()),
            )
        if ledger is not None:
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
                sum(
                    value.bit_length()
                    for value in (
                        one.gain,
                        one.offset,
                        one.sum_gain,
                        one.sum_offset,
                        zero.gain,
                        zero.offset,
                        zero.sum_gain,
                        zero.sum_offset,
                    )
                ),
            )
        prefix_action = one.then(zero)
        if ledger is not None:
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
                sum(
                    value.bit_length()
                    for value in (
                        *prefix_action.coefficient_snapshot(),
                        *one.coefficient_snapshot(),
                    )
                ),
            )
        action = prefix_action.then(one)
        return tail, action, self.transport(action, ledger=ledger)

    def forced_border_word_for_ticks(
        self,
        physical_ticks: int,
        *,
        max_returns: int = 32,
        max_tail: int = 128,
        ledger: ResourceLedger | None = None,
    ) -> (
        tuple[
            DyadicTerminalFieldAction,
            CollatzTwoSidedCylinder,
            tuple[int, ...],
        ]
        | None
    ):
        """Select a finite changing-tail word only when it fills this horizon.

        Each return is inferred from the complete transported interval/coset.
        The method refuses an open next tail and any request that would stop
        partway through a return; no cycle or repeated-tail premise is used.
        """
        if type(physical_ticks) is not int or physical_ticks <= 0:
            raise ValueError("physical border horizon must be positive")
        if type(max_returns) is not int or not 1 <= max_returns <= 64:
            raise ValueError("border return count is outside 1..64")
        if type(max_tail) is not int or not 0 <= max_tail <= 4096:
            raise ValueError("border tail budget lies outside 0..4096")
        if ledger is not None and type(ledger) is not ResourceLedger:
            raise TypeError("border continuation accounting needs a query ledger")

        state = self
        action = DyadicTerminalFieldAction.identity()
        remaining = physical_ticks
        tails: list[int] = []
        for _ in range(max_returns):
            next_return = state.forced_next_return(
                max_tail=max_tail,
                ledger=ledger,
                max_physical_ticks=remaining,
            )
            if next_return is None:
                return None
            tail, fragment, target = next_return
            duration = tail + 4
            if ledger is not None:
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
                    state.modulus.bit_length()
                    + fragment.gain.bit_length()
                    + fragment.offset.bit_length()
                    + fragment.sum_gain.bit_length()
                    + fragment.sum_offset.bit_length()
                    + action.gain.bit_length()
                    + action.offset.bit_length()
                    + action.sum_gain.bit_length()
                    + action.sum_offset.bit_length(),
                )
            action = action.then(fragment)
            tails.append(tail)
            state = target
            remaining -= duration
            if remaining == 0:
                return action, state, tuple(tails)
            # The 6305 recurrence selects only 3-ending inlets. An 8-ending
            # exit is valid as the final endpoint, but it cannot be extended
            # by pretending it is another 3-ending return.
        if ledger is not None:
            ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_REFUSALS)
        return None

    def forced_future(
        self,
        *,
        max_returns: int = 8,
        max_tail: int = 128,
        ledger: ResourceLedger | None = None,
    ) -> tuple[DyadicTerminalFieldAction, CollatzTwoSidedCylinder, tuple[int, ...]]:
        """Compose an exact finite 3->3 driver, stopping before an open exit.

        This never assumes the next tail is periodic. If the next 6305 return
        would reach an 8-ending border, it is intentionally NOT included in
        the returned 3->3 word; the existing exit producer remains authoritative.
        """
        if type(max_returns) is not int or not 0 <= max_returns <= 64:
            raise ValueError("source-wide return horizon must be in 0..64")
        if ledger is not None and type(ledger) is not ResourceLedger:
            raise TypeError("border continuation accounting needs a query ledger")
        state = self
        action = DyadicTerminalFieldAction.identity()
        tails: list[int] = []
        for _ in range(max_returns):
            step = state.forced_next_return(max_tail=max_tail, ledger=ledger)
            if step is None:
                break
            j, fragment, target = step
            if ledger is not None:
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
                    sum(
                        value.bit_length()
                        for value in (
                            action.gain,
                            action.offset,
                            action.sum_gain,
                            action.sum_offset,
                            fragment.gain,
                            fragment.offset,
                            fragment.sum_gain,
                            fragment.sum_offset,
                        )
                    ),
                )
            _record_cylinder_operand_bits(
                ledger, target.lower, target.upper, target.residue, target.modulus, 10
            )
            if target.forced_residue(10) != 3:
                break
            action = action.then(fragment)
            state = target
            tails.append(j)
        return action, state, tuple(tails)

    def conditional_next_tails(
        self, *, max_tail: int = 8, ledger: ResourceLedger | None = None
    ) -> tuple[tuple[int | None, CollatzTwoSidedCylinder], ...]:
        """Partition an uncertain 3-border into exact disjoint tail cylinders.

        The ``None`` branch is the unresolved long tail j>=max_tail. There
        is no synthetic 'other' successor. Counts are checked exhaustively
        by modular arithmetic; the count itself may be arbitrarily large.
        """
        if type(max_tail) is not int or not 1 <= max_tail <= 64:
            raise ValueError("conditional 6305 tail bound must be 1..64")
        if ledger is not None and type(ledger) is not ResourceLedger:
            raise TypeError("conditional tail accounting needs a query ledger")
        _record_cylinder_operand_bits(
            ledger, self.lower, self.upper, self.residue, self.modulus, max_tail
        )
        if self.forced_residue(10) != 3:
            return ()
        children: list[tuple[int | None, CollatzTwoSidedCylinder]] = []
        for j in range(max_tail):
            _record_cylinder_operand_bits(ledger, j, self.modulus)
            _record_cylinder_operand_bits(ledger, 2, j + 2)
            modulus = 1 << (j + 2)
            inverse_three = pow(3, -1, modulus)
            _record_cylinder_operand_bits(ledger, 1, j + 1)
            power_two = 1 << (j + 1)
            _record_cylinder_operand_bits(ledger, power_two, 1, inverse_three, modulus)
            residue = (power_two - 1) * inverse_three % modulus
            child = self.intersect_congruence(residue, modulus, ledger=ledger)
            if child is not None:
                children.append((j, child))
        modulus = 1 << (max_tail + 1)
        _record_cylinder_operand_bits(ledger, max_tail, self.modulus)
        _record_cylinder_operand_bits(ledger, 1, max_tail + 1)
        inverse_three = pow(3, -1, modulus)
        _record_cylinder_operand_bits(ledger, inverse_three, modulus)
        residue = (-inverse_three) % modulus
        tail = self.intersect_congruence(residue, modulus, ledger=ledger)
        if tail is not None:
            children.append((None, tail))
        if sum(child.count for _, child in children) != self.count:
            raise ArithmeticError("conditional 6305 splitting lost source fibers")
        return tuple(children)

    def leading_binary(self, width: int) -> tuple[int, int] | None:
        """Only an actual affine endpoint prefix common to all sources."""
        if type(width) is not int or width < 1:
            raise ValueError("leading prefix width must be positive")
        lo, hi = self.first, self.last
        if lo.bit_length() != hi.bit_length() or lo.bit_length() < width:
            return None
        shift = lo.bit_length() - width
        return (lo.bit_length(), lo >> shift) if lo >> shift == hi >> shift else None

    def summary(self, *, high_bits: int = 8) -> dict[str, object]:
        return {
            "source_interval": (self.lower, self.upper),
            "exact_coset": (self.residue, self.modulus),
            "source_alternatives": self.count,
            "binary_precision": self.binary_precision,
            "leading_binary": self.leading_binary(high_bits),
            "forced_next_6305_tail": self.forced_next_6305_tail,
            "forced_crt160": self.forced_residue(160),
            "forced_f5": self.forced_residue(5),
            "forced_radix6_digits": tuple(
                ((residue // (6**position)) % 6 if residue is not None else None)
                for position in range(3)
                for residue in (self.forced_residue(6 ** (position + 1)),)
            ),
            "all_depth_claim": False,
        }


__all__ = ("CollatzTwoSidedCylinder",)
