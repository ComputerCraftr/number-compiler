"""Authenticated block-level signed Fermat carry classes for Boolean adders.

This is a *spatial* action: for a supplied pair of operand words it transports
both possible incoming carries and the complete negacyclic digit-change
histogram, not just a sampled XOR stencil. It is suitable for source-proved
CONCAT/REPEAT grammars. It DOES NOT infer a temporal grammar for 3**(2**t).

For F=2**w+1 and binary digits source d_i and output e_i define

    C[r] = sum_{i == r (mod w)} (-1)**(i//w) * (e_i-d_i).

Then delta = sum_r C[r]*2**r (mod F). The class vector can be
composed through negacyclic rotation, including odd-width seam crossings.
WalshH5 is an independent observer and is threaded with exactly the same
incoming-carry context.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import lcm
from typing import Final

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.boolean_counter import (
    BinaryBooleanCarryAction,
)
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.fields.walsh import WalshH5
from number_compiler.sequences.power_numbers.three_dyadic_boolean_counter import (
    MAX_AUTHENTICATED_OPERAND_BITS,
    MAX_COUNTER_FOLD_WIDTH,
    BinaryCounterFoldAction,
)

SignedClasses = tuple[tuple[int, int], ...]
_SIGNED_COUNTER_WITNESS_ID: Final[str] = "signed-counter-witness-v1"


def _packed(values: dict[int, int]) -> SignedClasses:
    return tuple(
        sorted((position, count) for position, count in values.items() if count)
    )


def _rotated_negacyclic(
    classes: SignedClasses, shift: int, width: int
) -> SignedClasses:
    """Multiply a signed coefficient histogram by z**shift, z**w=-1."""
    result: dict[int, int] = {}
    phase = shift % (2 * width)
    for position, count in classes:
        target = position + phase
        new_position = target % width
        sign = -1 if (target // width) & 1 else 1
        result[new_position] = result.get(new_position, 0) + sign * count
    return _packed(result)


def _sum_classes(a: SignedClasses, b: SignedClasses) -> SignedClasses:
    total = dict(a)
    for position, count in b:
        total[position] = total.get(position, 0) + count
    return _packed(total)


@dataclass(frozen=True, slots=True)
class SignedCounterClassAction:
    """Complete signed positional-class action on both Boolean carry entries.

    The identity of this representation is intentionally *finer* than the
    residue-only Moore action: distinct positional vectors can evaluate to the
    same remainder. Use ``residue_action`` for the residue/H5 semantic key.
    """

    fermat_width: int
    length: int
    next_carries: tuple[int, int]
    signed_classes: tuple[SignedClasses, SignedClasses]
    harmonics: tuple[WalshH5, WalshH5]

    def __post_init__(self) -> None:
        w = require_integer(
            self.fermat_width, "Fermat fold width", 1, MAX_COUNTER_FOLD_WIDTH
        )
        length = require_integer(self.length, "Boolean counter block length", 0)
        if (
            type(self.next_carries) is not tuple
            or type(self.signed_classes) is not tuple
            or type(self.harmonics) is not tuple
            or any(
                len(item) != 2
                for item in (self.next_carries, self.signed_classes, self.harmonics)
            )
        ):
            raise TypeError("signed class action requires two exact carry contexts")
        for state, classes, harmonic in zip(
            self.next_carries, self.signed_classes, self.harmonics, strict=True
        ):
            require_integer(state, "outgoing binary carry", 0, 1)
            if type(classes) is not tuple or any(
                type(item) is not tuple or len(item) != 2 for item in classes
            ):
                raise TypeError(
                    "signed classes require sorted sparse position/count tuples"
                )
            if any(
                type(position) is not int
                or type(count) is not int
                or not 0 <= position < w
                or count == 0
                for position, count in classes
            ) or tuple(sorted({x[0] for x in classes})) != tuple(x[0] for x in classes):
                raise ValueError("invalid or noncanonical signed position classes")
            if type(harmonic) is not WalshH5 or harmonic.length_mod6 != length % 6:
                raise ValueError("signed class harmonic does not match block length")

    @property
    def modulus(self) -> int:
        return (1 << self.fermat_width) + 1

    @classmethod
    def identity(cls, fermat_width: int) -> SignedCounterClassAction:
        z = WalshH5.empty()
        return cls(fermat_width, 0, (0, 1), ((), ()), (z, z))

    @classmethod
    def digit(
        cls, source_bit: int, addend_bit: int, fermat_width: int
    ) -> SignedCounterClassAction:
        require_integer(source_bit, "source bit", 0, 1)
        require_integer(addend_bit, "addend bit", 0, 1)
        next_carries: list[int] = []
        classes: list[SignedClasses] = []
        harmonics: list[WalshH5] = []
        for carry in (0, 1):
            s = source_bit + addend_bit + carry
            output = s & 1
            change = output - source_bit
            next_carries.append(s >> 1)
            classes.append(((0, change),) if change else ())
            harmonics.append(WalshH5.from_mask(source_bit ^ output, 1))
        return cls(
            fermat_width,
            1,
            (next_carries[0], next_carries[1]),
            (classes[0], classes[1]),
            (harmonics[0], harmonics[1]),
        )

    def then(self, higher: SignedCounterClassAction) -> SignedCounterClassAction:
        """Compose adjacent low-then-high operand blocks with signed wrap."""
        if type(higher) is not SignedCounterClassAction:
            raise TypeError("signed class composition requires the same action type")
        if self.fermat_width != higher.fermat_width:
            raise ValueError("cannot compose different Fermat widths")
        next_carries: list[int] = []
        classes: list[SignedClasses] = []
        harmonics: list[WalshH5] = []
        for carry in (0, 1):
            middle = self.next_carries[carry]
            next_carries.append(higher.next_carries[middle])
            classes.append(
                _sum_classes(
                    self.signed_classes[carry],
                    _rotated_negacyclic(
                        higher.signed_classes[middle], self.length, self.fermat_width
                    ),
                )
            )
            harmonics.append(self.harmonics[carry].then(higher.harmonics[middle]))
        return SignedCounterClassAction(
            self.fermat_width,
            self.length + higher.length,
            (next_carries[0], next_carries[1]),
            (classes[0], classes[1]),
            (harmonics[0], harmonics[1]),
        )

    def repeat(self, copies: int) -> SignedCounterClassAction:
        """Binary-power only an authenticated, literally repeated pair block."""
        n = require_integer(copies, "certified block repetitions", 0)
        return binary_power(
            self,
            n,
            identity=self.identity(self.fermat_width),
            compose=SignedCounterClassAction.then,
        ).value

    def shifted_classes(self, incoming_carry: int, offset: int) -> SignedClasses:
        """Shift the block's complete class action to an absolute bit offset.

        Uses negacyclic sign when the shift passes the Fermat width. The
        result covers ONLY the represented source block, never omitted bits.
        """
        incoming = require_integer(incoming_carry, "incoming Boolean carry", 0, 1)
        shift = require_integer(offset, "absolute source offset", 0)
        return _rotated_negacyclic(
            self.signed_classes[incoming], shift, self.fermat_width
        )

    @property
    def residue_action(self) -> BinaryCounterFoldAction:
        """The coarser exact carry/remainder/H5 quotient (not a prime result)."""
        modulus = self.modulus
        deltas = (
            sum((1 << position) * count for position, count in self.signed_classes[0])
            % modulus,
            sum((1 << position) * count for position, count in self.signed_classes[1])
            % modulus,
        )
        return BinaryCounterFoldAction(
            self.fermat_width, self.length, self.next_carries, deltas, self.harmonics
        )

    @property
    def semantic_id(self) -> tuple[object, ...]:
        """Coarser observable right-congruence; the full classes are witnesses."""
        return self.residue_action.semantic_id

    @property
    def witness_id(self) -> tuple[object, ...]:
        """Optional exact signed-class witness, intentionally non-minimal."""
        return (
            _SIGNED_COUNTER_WITNESS_ID,
            self.fermat_width,
            self.length % lcm(2 * self.fermat_width, 6),
            self.next_carries,
            self.signed_classes,
            tuple((h.phi2, h.phi3_a, h.phi3_b) for h in self.harmonics),
        )

    def apply(self, carry: int = 0) -> tuple[int, SignedClasses, int, WalshH5]:
        incoming = require_integer(carry, "incoming Boolean carry", 0, 1)
        residue_action = self.residue_action
        return (
            self.next_carries[incoming],
            self.signed_classes[incoming],
            residue_action.deltas[incoming],
            self.harmonics[incoming],
        )

    @classmethod
    def from_words(
        cls,
        source_bits: int,
        addend_bits: int,
        length: int,
        fermat_width: int,
        *,
        fold_action: BinaryCounterFoldAction | None = None,
    ) -> SignedCounterClassAction:
        width = require_integer(
            length,
            "Boolean counter operand width",
            0,
            MAX_AUTHENTICATED_OPERAND_BITS,
        )
        selected_fermat_width = require_integer(
            fermat_width, "Fermat fold width", 1, MAX_COUNTER_FOLD_WIDTH
        )
        if (
            type(source_bits) is not int
            or type(addend_bits) is not int
            or source_bits < 0
            or addend_bits < 0
            or source_bits.bit_length() > width
            or addend_bits.bit_length() > width
        ):
            raise ValueError("counter operands must fit authenticated source width")
        core = BinaryBooleanCarryAction.from_words(
            source_bits,
            addend_bits,
            width,
            (1 << selected_fermat_width) + 1,
        )
        if fold_action is None:
            fold_action = BinaryCounterFoldAction(
                selected_fermat_width,
                width,
                core.next_carries,
                core.deltas,
                core.harmonics,
            )
        elif (
            type(fold_action) is not BinaryCounterFoldAction
            or fold_action.fermat_width != selected_fermat_width
            or fold_action.length != width
        ):
            raise ValueError("provided scalar action has incompatible source geometry")

        classes_by_carry: list[SignedClasses] = []
        for initial_carry in (0, 1):
            carry, output_bits, changed = core.apply_words(initial_carry)
            _core_carry, delta, harmonic = core.apply(initial_carry)
            if carry != _core_carry or fold_action.apply(initial_carry) != (
                carry,
                delta,
                harmonic,
            ):
                raise ArithmeticError("provided scalar action disagrees with block")
            classes: dict[int, int] = {}
            pending = changed
            while pending:
                bit = pending & -pending
                position = bit.bit_length() - 1
                source_bit = (source_bits >> position) & 1
                output_bit = (output_bits >> position) & 1
                change = output_bit - source_bit
                if change:
                    residue_class = position % selected_fermat_width
                    sign = -1 if (position // selected_fermat_width) & 1 else 1
                    classes[residue_class] = (
                        classes.get(residue_class, 0) + sign * change
                    )
                pending ^= bit
            normalized = _packed(classes)
            weighted = (
                sum((1 << residue_class) * count for residue_class, count in normalized)
                % fold_action.modulus
            )
            if weighted != delta or harmonic != fold_action.harmonics[initial_carry]:
                raise ArithmeticError(
                    "signed classes disagree with the scalar carry action"
                )
            classes_by_carry.append(normalized)

        return cls(
            selected_fermat_width,
            width,
            fold_action.next_carries,
            (classes_by_carry[0], classes_by_carry[1]),
            fold_action.harmonics,
        )


__all__ = ["SignedCounterClassAction"]
