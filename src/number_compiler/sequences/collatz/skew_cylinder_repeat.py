"""Exact source-bound powering of one admitted Collatz parity word.

For ``A(x)=(a*x+b)/2**d`` with its issued source guard, put
``C=2**d-a`` and ``D(x)=C*x-b``. Then ``D(A(x))=a*D(x)/2**d``; the same
word repeats ``r`` times exactly when ``D(x)=0`` or ``v2(D(x))>=d*r``.
This certificate concerns that exact parity word, not any next named-family
guard. Full coefficients and endpoints are only produced by a budgeted call.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
    require_integer,
)
from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.source_closed_port_action import (
        SourceCongruence,
    )


def _valuation2(value: int) -> int:
    if value == 0:
        raise ValueError("zero has infinite 2-adic valuation")
    absolute = abs(value)
    return (absolute & -absolute).bit_length() - 1


def _guard_work(action: DyadicTerminalFieldAction, source: int) -> tuple[int, int]:
    coefficient_bits = max(
        action.steps + 1,
        action.gain.bit_length(),
        abs(action.offset).bit_length(),
        1,
    )
    source_bits = source.bit_length()
    work_units = max(1, source_bits * coefficient_bits)
    storage_bits = 2 * source_bits + 2 * coefficient_bits + 8
    return work_units, storage_bits


@dataclass(frozen=True, slots=True, init=False)
class RepeatedWordMooreCylinder:
    """Minimal unary future class for repeating one source-admitted word."""

    source: int
    normalized_steps: int
    gain: int
    offset: int
    fixed_point_denominator: int
    defect: int
    remaining_repetitions: int | None
    _issuer: object = field(repr=False, compare=False)
    _binding: tuple[object, ...] = field(repr=False, compare=False)

    def __init__(self) -> None:
        raise TypeError("repeat cylinders require source-certified admission")

    @classmethod
    def _issue(
        cls,
        action: DyadicTerminalFieldAction,
        source: int,
        denominator: int,
        defect: int,
        remaining: int | None,
    ) -> RepeatedWordMooreCylinder:
        cylinder = object.__new__(cls)
        values = (
            source,
            action.steps,
            action.gain,
            action.offset,
            denominator,
            defect,
            remaining,
        )
        for name, value in zip(
            (
                "source",
                "normalized_steps",
                "gain",
                "offset",
                "fixed_point_denominator",
                "defect",
                "remaining_repetitions",
            ),
            values,
            strict=True,
        ):
            object.__setattr__(cylinder, name, value)
        object.__setattr__(cylinder, "_issuer", cylinder)
        object.__setattr__(
            cylinder,
            "_binding",
            (
                source,
                action,
                action.coefficient_snapshot(),
                cylinder.publication_snapshot(),
            ),
        )
        return cylinder

    def publication_snapshot(self) -> tuple[object, ...]:
        return (
            self.source,
            self.normalized_steps,
            self.gain,
            self.offset,
            self.fixed_point_denominator,
            self.defect,
            self.remaining_repetitions,
        )

    @classmethod
    def from_action(
        cls,
        action: DyadicTerminalFieldAction,
        source: int,
        *,
        evaluator: GrowthArithmeticEvaluator | None = None,
        preflight: Callable[[int], None] | None = None,
    ) -> RepeatedWordMooreCylinder:
        """Build the exact defect class inside a caller-owned work budget.

        Supply either the arithmetic evaluator or a storage preflight callback.
        The latter is used by the live executor's existing run workspace.
        """
        if (
            type(action) is not DyadicTerminalFieldAction
            or not action.producer_issued
            or action.steps <= 0
        ):
            raise ValueError("repeat guard requires a nonempty issued parity action")
        source = require_integer(source, "repeated-word source", 1)
        if (evaluator is None) == (preflight is None):
            raise TypeError("repeat-guard construction requires one work owner")
        work_units, storage_bits = _guard_work(action, source)
        if evaluator is not None:
            if type(evaluator) is not GrowthArithmeticEvaluator:
                raise TypeError("repeat-guard evaluator has another owner")
            with evaluator.charge_work(
                work_units,
                0,
                source.bit_length()
                + action.steps
                + action.gain.bit_length()
                + abs(action.offset).bit_length(),
                storage_bits=storage_bits,
            ):
                return cls._from_admitted_action(action, source)
        assert preflight is not None
        preflight(storage_bits)
        return cls._from_admitted_action(action, source)

    @classmethod
    def _from_admitted_action(
        cls, action: DyadicTerminalFieldAction, source: int
    ) -> RepeatedWordMooreCylinder:
        if not action.certifies(source):
            raise ValueError(
                "repeat guard source is outside the issued parity cylinder"
            )
        denominator = (1 << action.steps) - action.gain
        defect = denominator * source - action.offset
        remaining = None if defect == 0 else _valuation2(defect) // action.steps
        if remaining is not None and remaining < 1:
            raise AssertionError("issued source does not admit its first parity word")
        return cls._issue(action, source, denominator, defect, remaining)

    def verify_for(self, action: DyadicTerminalFieldAction, source: int) -> None:
        """Validate this issued class against its original source/action cheaply."""
        binding = getattr(self, "_binding", None)
        if (
            type(self) is not RepeatedWordMooreCylinder
            or getattr(self, "_issuer", None) is not self
            or not is_exact_object_tuple(binding)
            or len(binding) != 4
            or type(action) is not DyadicTerminalFieldAction
            or not action.producer_issued
            or type(source) is not int
            or source <= 0
            or binding[0] != source
            or binding[1] is not action
            or binding[2] != action.coefficient_snapshot()
            or self.source != source
            or self.normalized_steps != action.steps
            or self.gain != action.gain
            or self.offset != action.offset
            or self.publication_snapshot() != binding[3]
        ):
            raise ValueError("repeated-word cylinder seal is invalid")

    def admits(self, repetitions: int) -> bool:
        require_integer(repetitions, "repeated parity-word count", 0)
        return self.remaining_repetitions is None or repetitions <= (
            self.remaining_repetitions
        )

    def after(self, repetitions: int) -> int | None:
        """Return the remaining unary acceptance class without endpoint work."""
        if not self.admits(repetitions):
            raise ValueError("parity-word repetition exceeds its source cylinder")
        return (
            None
            if self.remaining_repetitions is None
            else self.remaining_repetitions - repetitions
        )

    @property
    def exit_offset(self) -> int | None:
        """First differing normalized parity position after the last repeat.

        If v2(D)=d*R+r, the next word agrees on r initial bits and
        changes at position r.  The zero-defect fixed point has no exit.
        This is not a named decimal-border-family selection.
        """
        if self.defect == 0:
            return None
        return _valuation2(self.defect) % self.normalized_steps

    def exact_exit_source_guard(self) -> SourceCongruence | None:
        """Source congruence puncture fixing both lifetime and exit offset.

        (2**d-a)*x-b has valuation V precisely when it equals 2**V
        modulo 2**(V+1).  The coefficient is odd, hence invertible.
        Import the guard lazily to avoid a cycle with source-closed actions.
        """
        if self.defect == 0:
            return None
        from number_compiler.sequences.collatz.source_closed_port_action import (
            SourceCongruence,
        )

        v = _valuation2(self.defect)
        modulus = 1 << (v + 1)
        residue = (
            ((1 << v) + self.offset)
            * pow(self.fixed_point_denominator, -1, modulus)
            % modulus
        )
        guard = SourceCongruence(residue, modulus)
        if not guard.admits(self.source):
            raise AssertionError("exact displacement exit lost its original source")
        return guard

    @property
    def admits_square(self) -> bool:
        return self.admits(2)


__all__ = ["RepeatedWordMooreCylinder"]
