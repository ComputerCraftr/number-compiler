"""Independent bounded-leaf audit for saturated dyadic support."""

from __future__ import annotations

from operator import add, mul
from typing import TypeAlias

from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.hashlife.execution.dyadic_return_records import DyadicReturnLaw
from number_compiler.hashlife.execution.dyadic_return_transport import _low_bits
from number_compiler.resources.ledger import ResourceLedger


AuditEffect: TypeAlias = tuple[SkewTransfer[int], int, int, int]


def _balanced_saturated_audit(
    law: DyadicReturnLaw,
    source: int,
    width: int,
    ledger: ResourceLedger,
) -> tuple[SkewTransfer[int], int, int, int]:
    """Independently check a Collatz image by bounded leaves and balanced joins.

    The audit reads the authenticated source cylinder.  Each source bit is
    classified once in a leaf of at most 64 steps; joins operate on matching
    dyadic intervals.  This keeps the explicit audit's charged precision work
    below the old growing-prefix replay while still detecting a forged effect.
    """
    if width <= 0:
        raise ValueError("saturated audit needs a positive extent")

    # The audit has no ledger-owned retention: its short local postorder stack
    # is charged as transient work, and every classification/join is counted.
    stack: list[tuple[int, int, AuditEffect | None]] = []
    span, residue = width, _low_bits(source, width)
    while True:
        if span <= 64:
            state = residue
            transfer = SkewTransfer(1, 0, 1)
            odd = delta = minimum = 0
            for _ in range(span):
                bit = state & 1
                gain = law.gains[bit]
                shift = law.offsets[bit]
                next_numerator = gain * state + shift
                if next_numerator % 2:
                    raise ArithmeticError("audited dyadic leaf was not integral")
                state = next_numerator // 2
                transfer = transfer.then(
                    SkewTransfer(gain, shift, 2), multiply=mul, add=add
                )
                odd += bit
                delta += law.weights[bit]
                minimum = min(minimum, delta)
                ledger.bump("dyadic_payload_audit_branch_steps")
                ledger.bump(
                    "dyadic_payload_audit_operand_bits",
                    state.bit_length()
                    + transfer.upper.bit_length()
                    + abs(transfer.offset).bit_length()
                    + transfer.lower.bit_length(),
                )
            result: AuditEffect = (transfer, odd, delta, minimum)
        else:
            stack.append((span, residue, None))
            ledger.bump(
                "dyadic_payload_audit_operand_bits",
                span.bit_length() + residue.bit_length(),
            )
            span = 1 << ((span - 1).bit_length() - 1)
            residue = _low_bits(residue, span)
            continue

        while stack:
            parent_span, parent_residue, left = stack.pop()
            if left is None:
                stack.append((parent_span, parent_residue, result))
                ledger.bump(
                    "dyadic_payload_audit_operand_bits",
                    parent_span.bit_length()
                    + parent_residue.bit_length()
                    + sum(
                        abs(value).bit_length()
                        for value in (
                            result[0].upper,
                            result[0].offset,
                            result[0].lower,
                        )
                    ),
                )
                span = parent_span - (1 << ((parent_span - 1).bit_length() - 1))
                numerator = result[0].upper * parent_residue + result[0].offset
                if numerator % result[0].lower:
                    raise ArithmeticError("audited dyadic seam was not integral")
                residue = _low_bits(numerator // result[0].lower, span)
                break
            right = result
            transfer = left[0].then(right[0], multiply=mul, add=add)
            ledger.bump("dyadic_payload_audit_compositions")
            ledger.bump(
                "dyadic_payload_audit_operand_bits",
                sum(
                    abs(value).bit_length()
                    for value in (
                        parent_residue,
                        left[0].upper,
                        left[0].offset,
                        left[0].lower,
                        right[0].upper,
                        right[0].offset,
                        right[0].lower,
                    )
                ),
            )
            result = (
                transfer,
                left[1] + right[1],
                left[2] + right[2],
                min(left[3], left[2] + right[3]),
            )
        else:
            return result
