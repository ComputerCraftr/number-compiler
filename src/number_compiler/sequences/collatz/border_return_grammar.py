"""Exact physical 6305 border-return actions, with explicit 8/9 exit ports.

A 3-ending source ``10*q+3`` has the source-certified return

    3 -> 0^(j+1) -> 5 -> 6 -> (3 or 8)

where ``3*q+1 = 2**j*u`` with odd ``u``.  The entire normalized
action is ``1 0**j 1``.  Its ``j+2`` normalized symbols contain two
odd symbols, so the physical action costs ``j+4`` ticks.  In physical
time, ``T**(j+2)(x) = 5*u``; two more ticks reach ``(15*u+1)//2``.
The upper border ``u mod 4`` decides whether
the resulting integer ends in 3 again; ``u mod 8`` separates 8->4 from
8->9.  Neither the zero tail nor the odd half-steps are replayed.

This is an exact finite, source-bound *sequence of returns*. It does not
assume an indefinitely periodic border grammar or convergence for any source.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Final

from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.border_carry_cylinder import (
    next_6305_upper_numerator,
)
from number_compiler.sequences.collatz.border_identity import (
    BorderEntryPort,
    BorderExitPort,
    BoundaryPathKind,
    GuardedBorderPath,
    border_return_path,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.joint_radix_border import JointRadix6Source

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.position_cycle_harmonics import (
        PositionHarmonicSpectrum,
    )
    from number_compiler.sequences.collatz.temporal_f5_observer import (
        CollatzF5AffineAction,
    )

COLLATZ_BORDER_RETURN_ACTION_TAG: Final[str] = "collatz-border-return-v1"

_ISSUER = object()
_MAX_RETURNS_PER_ACTION = 64


@dataclass(frozen=True, slots=True, init=False)
class BorderReturnMacro:
    """Sealed, composable 6305 return program, including upper exit guard."""

    identity: GuardedBorderPath
    source: int
    endpoint: int
    physical_ticks: int
    odd_symbols: int
    fields: DyadicTerminalFieldAction
    width_blank: BlankLedger
    parts: tuple[tuple[int, int], ...]
    zero_tails: tuple[int, ...]
    returns: int
    entry_port: BorderEntryPort
    exit_port: BorderExitPort
    _binding: tuple[object, ...] = field(repr=False, compare=False)
    _issuer: object = field(repr=False, compare=False)

    def __init__(self) -> None:
        raise TypeError("border-return macros require an exact source admission")

    @property
    def normalized_symbols(self) -> int:
        return self.fields.steps

    @property
    def repetitions(self) -> int:
        return len(self.zero_tails)

    @property
    def return_physical_ticks(self) -> tuple[int, ...]:
        """Physical duration of each completed 3-border segment."""
        return tuple(tail + 4 for tail in self.zero_tails)

    @property
    def return_normalized_steps(self) -> tuple[int, ...]:
        """Normalized duration of each completed 3-border segment."""
        return tuple(tail + 2 for tail in self.zero_tails)

    @property
    def maximum_repetitions(self) -> int:
        """Return the finite program cap, not a future convergence bound."""
        return _MAX_RETURNS_PER_ACTION

    def demanded_position_harmonics(
        self,
        radix: int,
        position: int,
        *,
        walsh64: bool = False,
    ) -> PositionHarmonicSpectrum:
        """Read digit frequencies at the exact source-bound return seams.

        The homogeneous zero-tail-free case uses its centered affine orbit.
        Variable tails keep their issued upper cursors and are bounded by this
        producer's finite 64-return cap; no zero-tail digits are replayed.
        """
        from number_compiler.arithmetic.contracts.block_effect import (
            BlockContextBudgetExceeded,
        )
        from number_compiler.arithmetic.fields.homogeneous_growth import (
            HomogeneousGrowthScale,
        )
        from number_compiler.arithmetic.fields.walsh import walsh64_mod5
        from number_compiler.sequences.collatz.border_carry_cylinder import (
            Border6305CarryCylinder,
        )
        from number_compiler.sequences.collatz.position_cycle_harmonics import (
            PositionHarmonicSpectrum,
        )

        validate_border_return_macro(self)
        if not self.zero_tails:
            raise ValueError("position harmonic needs an admitted 6305 return")
        if type(radix) is not int or not 2 <= radix <= 64:
            raise ValueError("position radix must be 2..64")
        if type(position) is not int or position < 0:
            raise ValueError("position must be nonnegative")
        if (position + 1) * radix.bit_length() > 4096:
            raise BlockContextBudgetExceeded(
                "position exceeds the exact modulus budget"
            )
        if type(walsh64) is not bool:
            raise TypeError("Walsh64 demand must be Boolean")
        if walsh64 and len(self.zero_tails) < 64:
            raise ValueError("Walsh64 needs 64 authenticated border returns")

        current = self.source
        if self.entry_port is BorderEntryPort.DIGIT_SIX:
            current //= 2
        elif self.entry_port is BorderEntryPort.DIGIT_ZERO:
            current >>= v2_positive(current)
        if current % 10 == 5:
            current = (3 * current + 1) // 2
        if current % 10 != 3:
            raise ValueError("issued return word has no three-digit source seam")

        if not any(self.zero_tails):
            initial = Border6305CarryCylinder.from_three_digit(current)
            if initial.zero_tail != 0:
                raise AssertionError("all-zero return word has a nonzero initial tail")
            return initial.demanded_position_harmonics(
                len(self.zero_tails), radix, position, walsh64=walsh64
            )

        modulus = radix ** (position + 1)
        place = modulus // radix
        counts = [0] * radix
        mask = 0
        cursor: Border6305CarryCylinder | None = None
        total_halvings = 0
        for index, zero_tail in enumerate(self.zero_tails):
            if cursor is None:
                cursor = Border6305CarryCylinder.from_three_digit(current)
            if cursor.zero_tail != zero_tail:
                raise AssertionError("variable-tail orbit lost its issued upper cursor")
            before_digit = (current // place) % radix
            endpoint = cursor.endpoint
            counts[before_digit] += 1
            if walsh64 and index < 64 and ((endpoint // place) % radix != before_digit):
                mask |= 1 << index
            total_halvings += zero_tail + 2
            following = cursor.next_return()
            if index + 1 < len(self.zero_tails) and following is None:
                raise AssertionError(
                    "issued variable-tail word crosses a terminal border"
                )
            current, cursor = endpoint, following

        return PositionHarmonicSpectrum(
            radix=radix,
            position=position,
            repetitions=len(self.zero_tails),
            counts=tuple(counts),
            forced_position_interval=None,
            forced_position_digit=None,
            two_adic_forced_through=None,
            ternary_forced_from=None,
            odd_preperiod=None,
            odd_period=None,
            evaluated_cells=len(self.zero_tails),
            radial_scale=HomogeneousGrowthScale(
                2 * len(self.zero_tails), total_halvings
            ),
            walsh64_change_mod5=walsh64_mod5(mask) if walsh64 else None,
        )

    def f5_action(self) -> CollatzF5AffineAction:
        from number_compiler.sequences.collatz.temporal_f5_observer import (
            _project_dyadic_fields_f5,
        )

        return _project_dyadic_fields_f5(self.fields)

    def structural_payload(self) -> tuple[object, ...]:
        """Structural immutable values only; never publish action objects."""
        fields = self.fields
        return (
            COLLATZ_BORDER_RETURN_ACTION_TAG,
            self.identity.structural_key(),
            self.source,
            self.endpoint,
            self.physical_ticks,
            self.odd_symbols,
            fields.steps,
            fields.gain,
            fields.offset,
            fields.sum_gain,
            fields.sum_offset,
            fields.previous_gain,
            fields.previous_offset,
            *self.width_blank.as_tuple(),
            self.parts,
            self.zero_tails,
            self.returns,
            self.entry_port.value,
            self.exit_port.value,
        )

    def observation(self) -> dict[str, object]:
        return {
            "border": self.identity.observation(run_parameters=self.zero_tails),
            "source": self.source,
            "endpoint": self.endpoint,
            "physical_ticks": self.physical_ticks,
            "normalized_symbols": self.normalized_symbols,
            "odd_symbols": self.odd_symbols,
            "zero_tail_valuations": self.zero_tails,
            "return_forced_decimal_carry": {
                "source_units": 3,
                "product_units": 0,
                "carry_into_next_decimal_position": 1,
            },
            "return_radial_scale": {
                "growths": 2 * len(self.zero_tails),
                "halvings": sum(self.zero_tails) + 2 * len(self.zero_tails),
                "scope": "completed 6305 returns; entry and exit are separate",
            },
            "return_affine_binary_corrections": tuple(
                2 if exponent == 0 else 1 for exponent in self.zero_tails
            ),
            "return_physical_ticks": self.return_physical_ticks,
            "return_normalized_steps": self.return_normalized_steps,
            "return_clock_scope": (
                "per completed 3-to-3/8 segment; macro totals also include "
                "any entry and 8/9 exit actions"
            ),
            "completed_returns": self.returns,
            "entry_port": self.entry_port.value,
            "exit_port": self.exit_port.value,
            "completed_final_division": True,
            "scope": "authenticated 6305 return/exit graph, not a universal future ID",
        }


def validate_border_return_macro(macro: BorderReturnMacro) -> None:
    """Reject foreign and changed macro payloads, including border provenance."""
    if (
        type(macro) is not BorderReturnMacro
        or getattr(macro, "_issuer", None) is not _ISSUER
    ):
        raise ValueError("border-return macro has no producer authority")
    binding = (
        macro.identity,
        macro.source,
        macro.endpoint,
        macro.physical_ticks,
        macro.odd_symbols,
        macro.fields,
        macro.width_blank,
        macro.parts,
        macro.zero_tails,
        macro.returns,
        macro.entry_port,
        macro.exit_port,
    )
    if (
        macro._binding != binding
        or type(macro.identity) is not GuardedBorderPath
        or macro.identity.kind is not BoundaryPathKind.THREE_BORDER_RETURN
        or macro.identity.entry_digit != macro.entry_port.value
        or macro.identity.exit_digit != macro.endpoint % 10
        or macro.source <= 0
        or macro.endpoint <= 0
        or not macro.zero_tails
        or len(macro.zero_tails) > _MAX_RETURNS_PER_ACTION
        or not 0 <= macro.returns <= len(macro.zero_tails)
        or type(macro.fields) is not DyadicTerminalFieldAction
        or not macro.fields.producer_issued
        or type(macro.width_blank) is not BlankLedger
        or macro.fields.steps + macro.odd_symbols != macro.physical_ticks
        or sum(macro.return_physical_ticks) > macro.physical_ticks
        or sum(macro.return_normalized_steps) > macro.fields.steps
        or macro.fields.endpoint(macro.source) != macro.endpoint
        or sum(length for _, length in macro.parts) != macro.fields.steps
        or sum(length for bit, length in macro.parts if bit) != macro.odd_symbols
        or macro.parts[0][0] != macro.source & 1
        or macro.width_blank.delta
        != macro.endpoint.bit_length() - macro.source.bit_length()
    ):
        raise ValueError("border-return macro differs from its authenticated program")


def select_border_return_macro(
    source: int,
    available_physical_ticks: int,
    *,
    max_returns: int = _MAX_RETURNS_PER_ACTION,
    minimum_useful_physical_ticks: int = 0,
    preflight: Callable[[int], None] | None = None,
    ledger: ResourceLedger | None = None,
    radix_state: JointRadix6Source | None = None,
) -> BorderReturnMacro | None:
    """Produce one complete cross-family action without scalar Collatz replay.

    A finite number of *border* tests may be necessary; each test is a
    valuation and residue on the exact upper coordinate, not a scan of the
    zero tail.  No preview or default modular clock authorizes an exit.
    """
    if type(source) is not int or source <= 0:
        raise ValueError("Collatz border source must be a positive integer")
    if type(available_physical_ticks) is not int or available_physical_ticks < 0:
        raise ValueError("Collatz border request needs a nonnegative tick budget")
    if type(max_returns) is not int or not 1 <= max_returns <= _MAX_RETURNS_PER_ACTION:
        raise ValueError("border return bound must be between 1 and 64")
    if (
        type(minimum_useful_physical_ticks) is not int
        or minimum_useful_physical_ticks < 0
    ):
        raise ValueError("minimum useful physical ticks must be a nonnegative integer")
    state = (
        radix_state
        if radix_state is not None
        else JointRadix6Source.from_source(source)
    )
    if type(state) is not JointRadix6Source:
        raise TypeError("border-return selector requires a radix-6 source state")
    state.require_source(source)

    if ledger is not None:
        ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_CHECKS)

    def account_operands(*values: int) -> None:
        if ledger is not None:
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_OPERAND_BITS,
                sum(value.bit_length() for value in values),
            )

    def record_refusal() -> None:
        if ledger is not None:
            ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_REFUSALS)

    def below_minimum(candidate_ticks: int) -> bool:
        """Reject only strictly shorter candidates; ties remain admissible."""
        account_operands(candidate_ticks, minimum_useful_physical_ticks)
        if ledger is not None:
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_THRESHOLD_COMPARISONS
            )
        if candidate_ticks >= minimum_useful_physical_ticks:
            return False
        record_refusal()
        if ledger is not None:
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_THRESHOLD_REFUSALS
            )
        return True

    account_operands(source, available_physical_ticks)
    # No admitted macro can outlast the caller's physical horizon.  Use this
    # cheap upper bound before residue/valuation classification and before any
    # preflight or powered-action construction.  Equality is deliberately kept:
    # `minimum_useful_physical_ticks` is inclusive and preserves tie behavior.
    if below_minimum(available_physical_ticks):
        if ledger is not None:
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_EXTENT_BOUND_REFUSALS
            )
        return None
    if available_physical_ticks < 4:
        record_refusal()
        return None
    if state.decimal_residue(10) not in (0, 3, 5) and state.decimal_residue(20) != 6:
        record_refusal()
        return None

    runs: list[tuple[int, int]] = []
    tails: list[int] = []
    current = source
    budget = available_physical_ticks
    physical = 0
    normalized = 0
    returns = 0
    width = BlankLedger()
    entry = (
        BorderEntryPort.DIGIT_THREE
        if state.decimal_residue(10) == 3
        else (
            BorderEntryPort.DIGIT_SIX
            if state.decimal_residue(20) == 6
            else BorderEntryPort.DIGIT_FIVE
            if state.decimal_residue(10) == 5
            else BorderEntryPort.DIGIT_ZERO
        )
    )
    exit_port = BorderExitPort.UNRESOLVED
    final_threshold_admitted = False

    def append(bit: int, count: int, target: int, *, lower: int, upper: int) -> None:
        nonlocal current, budget, physical, normalized, width, state
        if count <= 0:
            return
        ticks = count * (2 if bit else 1)
        if budget < ticks:
            raise AssertionError("border admission exceeded its physical clock")
        if runs and runs[-1][0] == bit:
            old, length = runs[-1]
            runs[-1] = (old, length + count)
        else:
            runs.append((bit, count))
        before_width = current.bit_length()
        after_width = target.bit_length()
        width = width.then(
            BlankLedger(
                after_width - before_width, lower - before_width, upper - before_width
            )
        )
        state = state.after_normalized(bit, count, target)
        current = target
        budget -= ticks
        physical += ticks
        normalized += count

    # The initial 6->3, 0*->5, and 5->6->(3 or 8) are explicitly
    # source-authenticated entrance ports.  They are not guessed predecessors.
    if entry is BorderEntryPort.DIGIT_SIX:
        account_operands(current)
        append(
            0,
            1,
            current // 2,
            lower=(current // 2).bit_length(),
            upper=current.bit_length(),
        )
    elif entry is BorderEntryPort.DIGIT_ZERO:
        account_operands(current)
        if ledger is not None:
            ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_VALUATION_CHECKS)
        exponent = v2_positive(current)
        if budget < exponent:
            record_refusal()
            return None
        account_operands(exponent, budget)
        append(
            0,
            exponent,
            current >> exponent,
            lower=(current >> exponent).bit_length(),
            upper=current.bit_length(),
        )
    if state.decimal_residue(10) == 5:
        if budget < 2:
            record_refusal()
            return None
        account_operands(current, budget)
        raw = 3 * current + 1
        append(
            1,
            1,
            raw // 2,
            lower=min(current, raw // 2).bit_length(),
            upper=raw.bit_length(),
        )

    # The lower decimal carry is fixed by the entry digit 3. Carry its exact
    # upper numerator across returns so the hot loop need not reconstruct q
    # from the complete endpoint after each selected return.
    upper_numerator: int | None = None
    returns_to_three = state.decimal_residue(10) == 3
    last_upper_odd: int | None = None
    while returns_to_three and len(tails) < max_returns:
        account_operands(current)
        if upper_numerator is None:
            upper_numerator = 3 * ((current - 3) // 10) + 1
        account_operands(upper_numerator)
        if ledger is not None:
            ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_VALUATION_CHECKS)
        exponent = v2_positive(upper_numerator)
        if budget < exponent + 4:
            break
        odd = upper_numerator >> exponent
        last_upper_odd = odd
        physical_before = physical
        normalized_before = normalized
        account_operands(exponent, odd, budget)
        start = current
        raw = 3 * start + 1
        account_operands(raw)
        # One odd step takes two physical ticks.  The exact zero tail is
        # determined by v2(3*q+1), including exponent zero.
        append(
            1,
            1,
            raw // 2,
            lower=min(start, raw // 2).bit_length(),
            upper=raw.bit_length(),
        )
        if exponent:
            target = 5 * odd
            append(
                0,
                exponent,
                target,
                lower=target.bit_length(),
                upper=current.bit_length(),
            )
        if current != 5 * odd:
            raise AssertionError("border zero tail lost its upper odd coordinate")
        raw = 15 * odd + 1
        append(
            1,
            1,
            raw // 2,
            lower=min(current, raw // 2).bit_length(),
            upper=raw.bit_length(),
        )
        if (
            physical - physical_before != exponent + 4
            or normalized - normalized_before != exponent + 2
        ):
            raise AssertionError("border return lost its distinct clocks")
        tails.append(exponent)
        upper_numerator = next_6305_upper_numerator(odd)
        returns_to_three = upper_numerator is not None
        # The independently transported F5 and parity ports check the exact
        # output of the upper carry cylinder before another return is admitted.
        if state.residue5 != 3 or (not state.even) != returns_to_three:
            raise AssertionError("upper/lower carry ports disagree with F5 and parity")
        if returns_to_three:
            returns += 1
        else:
            break

    if not tails:
        record_refusal()
        return None

    if returns_to_three:
        exit_port = (
            BorderExitPort.RETURN_TO_THREE
            if budget
            else BorderExitPort.RETURN_AT_HORIZON
        )
    else:
        if last_upper_odd is None:
            raise AssertionError("8 exit lacks the upper odd carry coordinate")
        endpoint_residue20 = ((15 * (last_upper_odd & 7) + 1) >> 1) % 20
        if endpoint_residue20 == 8:
            exit_port = BorderExitPort.EIGHT_TO_FOUR
        elif endpoint_residue20 == 18:
            exit_port = BorderExitPort.EIGHT_TO_NINE
        else:
            raise AssertionError("8 border has an impossible upper carry residue")
        if state.residue5 != 3 or state.even is False:
            raise AssertionError("8 border disagrees with transported F5/parity ports")
        if state.decimal_residue(10) != 8:
            raise AssertionError("upper carry exit did not reach an 8 digit")
        if budget:
            # Project the complete 8->9 suffix before mutating the local run
            # program.  In particular, a rejected candidate never allocates
            # the potentially large `3**run` endpoint and never preflights the
            # dyadic coefficient payload it will not publish.
            projected_physical = physical + 1
            projected_budget = budget - 1
            projected_run = 0
            projected_guard_valuation = 0
            if exit_port is BorderExitPort.EIGHT_TO_NINE:
                projected_current = current // 2
                projected_guard = projected_current + 1
                account_operands(projected_current, projected_guard, projected_budget)
                if ledger is not None:
                    ledger.bump(
                        _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_VALUATION_CHECKS
                    )
                projected_guard_valuation = v2_positive(projected_guard)
                projected_run = min(projected_guard_valuation, projected_budget // 2)
                projected_physical += 2 * projected_run
            if below_minimum(projected_physical):
                return None
            final_threshold_admitted = True
            account_operands(current, budget)
            append(
                0,
                1,
                current // 2,
                lower=(current // 2).bit_length(),
                upper=current.bit_length(),
            )
            if exit_port is BorderExitPort.EIGHT_TO_NINE:
                # A newly produced interior 9 always has the authenticated
                # incoming 8.  Pump the odd 9->8 return where the budget
                # contains complete normalized odd steps.
                guard_valuation = projected_guard_valuation
                run = projected_run
                if run:
                    # Reserve before constructing the potentially large
                    # powered endpoint, not after `3**run` has allocated it.
                    if preflight is not None:
                        preflight(sum(length for _, length in runs) + run)
                    before = current
                    account_operands(before, run)
                    endpoint = (3**run) * ((before + 1) >> run) - 1
                    account_operands(endpoint)
                    append(
                        1,
                        run,
                        endpoint,
                        lower=before.bit_length(),
                        upper=(2 * endpoint).bit_length(),
                    )
                    exit_port = (
                        BorderExitPort.EIGHT_TO_NINE_TO_EIGHT
                        if run == guard_valuation
                        else BorderExitPort.EIGHT_TO_NINE_OPEN
                    )
                else:
                    exit_port = BorderExitPort.EIGHT_TO_NINE_PENDING

    if not runs:
        return None
    if not final_threshold_admitted and below_minimum(physical):
        return None
    # The resource owner authorizes every coefficient allocation before the
    # powered field action is constructed, not after its large limbs exist.
    if preflight is not None:
        preflight(sum(count for _, count in runs))
    fields = DyadicTerminalFieldAction.identity()
    for bit, count in runs:
        segment = (
            DyadicTerminalFieldAction.one_run(count)
            if bit
            else DyadicTerminalFieldAction.zero_run(count)
        )
        fields = fields.then(segment)
    odd_count = sum(length for bit, length in runs if bit)
    if (
        fields.steps != normalized
        or fields.steps + odd_count != physical
        or fields.endpoint(source) != current
    ):
        raise AssertionError("border-return composed action differs from its exit")
    binding: tuple[object, ...] = (
        border_return_path(entry.value, state.decimal_residue(10)),
        source,
        current,
        physical,
        odd_count,
        fields,
        width,
        tuple(runs),
        tuple(tails),
        returns,
        entry,
        exit_port,
    )
    macro = object.__new__(BorderReturnMacro)
    for name, value in zip(
        (
            "identity",
            "source",
            "endpoint",
            "physical_ticks",
            "odd_symbols",
            "fields",
            "width_blank",
            "parts",
            "zero_tails",
            "returns",
            "entry_port",
            "exit_port",
        ),
        binding,
        strict=True,
    ):
        object.__setattr__(macro, name, value)
    object.__setattr__(macro, "_binding", binding)
    object.__setattr__(macro, "_issuer", _ISSUER)
    validate_border_return_macro(macro)
    return macro


__all__ = [
    "BorderReturnMacro",
    "select_border_return_macro",
    "validate_border_return_macro",
]
