"""Family-neutral exact two-carry actions for supplied binary blocks.

The action is spatial: it summarizes one fully specified pair of operands,
tracks both incoming carry contexts, and composes over least-significant-first
concatenation.  It does not authenticate a source sequence or predict a later
block.  Family owners supply that provenance separately.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Final

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.fields.walsh import WalshH5

MAX_BOOLEAN_BLOCK_BITS = 262_144
MAX_BOOLEAN_MODULUS_BITS = 262_145
MAX_BOOLEAN_LENGTH_BITS = 4_096
_BOOLEAN_ACTION_ID: Final[str] = "binary-boolean-carry-fold-h5-v1"


@dataclass(frozen=True, slots=True)
class BinaryBooleanCarryAction:
    """Two-port action of adding exact low-to-high binary operand blocks.

    ``deltas[c]`` is ``(output - source) mod modulus`` for incoming carry
    ``c``.  ``harmonics[c]`` is the length-aware H5 packet of the changed-bit
    mask. ``apply_words`` exposes the exact output of the same direct block
    addition when this value was made by ``from_words``. Composed and repeated
    actions retain only the compact carry/fold/H5 summary.
    """

    modulus: int
    length: int
    next_carries: tuple[int, int]
    deltas: tuple[int, int]
    harmonics: tuple[WalshH5, WalshH5]
    _output_words: tuple[int, int] | None = field(
        default=None, init=False, repr=False, compare=False
    )
    _xor_masks: tuple[int, int] | None = field(
        default=None, init=False, repr=False, compare=False
    )

    def __post_init__(self) -> None:
        modulus = require_integer(self.modulus, "Boolean fold modulus", 1)
        if modulus.bit_length() > MAX_BOOLEAN_MODULUS_BITS:
            raise ValueError("Boolean fold modulus exceeds the explicit bit budget")
        length = require_integer(self.length, "Boolean block length", 0)
        if length.bit_length() > MAX_BOOLEAN_LENGTH_BITS:
            raise ValueError("Boolean symbolic length exceeds its integer budget")
        if any(
            type(values) is not tuple or len(values) != 2
            for values in (self.next_carries, self.deltas, self.harmonics)
        ):
            raise TypeError("Boolean action requires exactly two carry contexts")
        for carry in self.next_carries:
            require_integer(carry, "outgoing Boolean carry", 0, 1)
        for delta in self.deltas:
            require_integer(delta, "Boolean fold correction", 0, modulus - 1)
        if any(
            type(harmonic) is not WalshH5 or harmonic.length_mod6 != length % 6
            for harmonic in self.harmonics
        ):
            raise ValueError("Boolean action H5 packet has the wrong block phase")

    @classmethod
    def _with_words(
        cls,
        modulus: int,
        length: int,
        next_carries: tuple[int, int],
        deltas: tuple[int, int],
        harmonics: tuple[WalshH5, WalshH5],
        outputs: tuple[int, int] | None,
        xors: tuple[int, int] | None,
    ) -> BinaryBooleanCarryAction:
        action = cls(modulus, length, next_carries, deltas, harmonics)
        if outputs is not None:
            object.__setattr__(action, "_output_words", outputs)
            object.__setattr__(action, "_xor_masks", xors)
        return action

    @classmethod
    def identity(cls, modulus: int) -> BinaryBooleanCarryAction:
        selected = require_integer(modulus, "Boolean fold modulus", 1)
        empty = WalshH5.empty()
        return cls._with_words(
            selected, 0, (0, 1), (0, 0), (empty, empty), (0, 0), (0, 0)
        )

    @classmethod
    def digit(
        cls, source_bit: int, addend_bit: int, modulus: int
    ) -> BinaryBooleanCarryAction:
        require_integer(source_bit, "source bit", 0, 1)
        require_integer(addend_bit, "addend bit", 0, 1)
        return cls.from_words(source_bit, addend_bit, 1, modulus)

    @classmethod
    def from_words(
        cls, source_bits: int, addend_bits: int, length: int, modulus: int
    ) -> BinaryBooleanCarryAction:
        width = require_integer(
            length, "Boolean operand width", 0, MAX_BOOLEAN_BLOCK_BITS
        )
        selected_modulus = require_integer(modulus, "Boolean fold modulus", 1)
        if selected_modulus.bit_length() > MAX_BOOLEAN_MODULUS_BITS:
            raise ValueError("Boolean fold modulus exceeds the explicit bit budget")
        if type(source_bits) is not int or type(addend_bits) is not int:
            raise TypeError("Boolean operand blocks must be exact integers")
        mask = (1 << width) - 1
        if not 0 <= source_bits <= mask or not 0 <= addend_bits <= mask:
            raise ValueError("Boolean operand blocks do not fit their declared width")

        next_carries: list[int] = []
        deltas: list[int] = []
        harmonics: list[WalshH5] = []
        outputs: list[int] = []
        xors: list[int] = []
        for incoming in (0, 1):
            total = source_bits + addend_bits + incoming
            output = total & mask
            xor_mask = source_bits ^ output
            next_carries.append(total >> width)
            deltas.append((output - source_bits) % selected_modulus)
            harmonics.append(WalshH5.from_mask(xor_mask, width))
            outputs.append(output)
            xors.append(xor_mask)
        return cls._with_words(
            selected_modulus,
            width,
            (next_carries[0], next_carries[1]),
            (deltas[0], deltas[1]),
            (harmonics[0], harmonics[1]),
            (outputs[0], outputs[1]),
            (xors[0], xors[1]),
        )

    def then(self, higher: BinaryBooleanCarryAction) -> BinaryBooleanCarryAction:
        """Compose adjacent low-then-high blocks without replaying their bits."""
        if type(higher) is not BinaryBooleanCarryAction:
            raise TypeError("Boolean action composition requires the same action type")
        if self.modulus != higher.modulus:
            raise ValueError("Boolean actions use different fold moduli")
        length = self.length + higher.length
        if length.bit_length() > MAX_BOOLEAN_LENGTH_BITS:
            raise ValueError("composed Boolean length exceeds its integer budget")
        multiplier = pow(2, self.length, self.modulus)
        carries: list[int] = []
        deltas: list[int] = []
        harmonics: list[WalshH5] = []
        for incoming in (0, 1):
            middle = self.next_carries[incoming]
            carries.append(higher.next_carries[middle])
            deltas.append(
                (self.deltas[incoming] + multiplier * higher.deltas[middle])
                % self.modulus
            )
            harmonics.append(self.harmonics[incoming].then(higher.harmonics[middle]))
        # Composition preserves the compact carry/fold/H5 summary only.
        # Exact words are available on a direct from_words action, where the
        # supplied operands were read once.  Reconstructing a large composed
        # output here would materialize a value most consumers never demand.
        return self._with_words(
            self.modulus,
            length,
            (carries[0], carries[1]),
            (deltas[0], deltas[1]),
            (harmonics[0], harmonics[1]),
            None,
            None,
        )

    def repeat(self, copies: int) -> BinaryBooleanCarryAction:
        """Binary-power an explicitly supplied block summary."""
        count = require_integer(copies, "Boolean block repetitions", 0)
        if count.bit_length() > MAX_BOOLEAN_LENGTH_BITS:
            raise ValueError("Boolean repetition count exceeds its integer budget")
        if (
            self.length
            and count
            and (self.length * count).bit_length() > MAX_BOOLEAN_LENGTH_BITS
        ):
            raise ValueError("repeated Boolean length exceeds its integer budget")
        return binary_power(
            self,
            count,
            identity=self.identity(self.modulus),
            compose=BinaryBooleanCarryAction.then,
        ).value

    def apply(self, incoming_carry: int = 0) -> tuple[int, int, WalshH5]:
        incoming = require_integer(incoming_carry, "incoming Boolean carry", 0, 1)
        return (
            self.next_carries[incoming],
            self.deltas[incoming],
            self.harmonics[incoming],
        )

    def apply_words(self, incoming_carry: int = 0) -> tuple[int, int, int]:
        """Return carry, emitted word and XOR mask from the same block read."""
        incoming = require_integer(incoming_carry, "incoming Boolean carry", 0, 1)
        if self._output_words is None or self._xor_masks is None:
            raise ValueError(
                "exact emitted word was not retained for this composed action"
            )
        return (
            self.next_carries[incoming],
            self._output_words[incoming],
            self._xor_masks[incoming],
        )

    def structural_snapshot(
        self,
    ) -> tuple[
        int,
        int,
        tuple[int, int],
        tuple[int, int],
        tuple[WalshH5, WalshH5],
        tuple[int, int] | None,
        tuple[int, int] | None,
    ]:
        """Expose the complete immutable action for source-integrity audits."""
        return (
            self.modulus,
            self.length,
            self.next_carries,
            self.deltas,
            self.harmonics,
            self._output_words,
            self._xor_masks,
        )

    @property
    def semantic_id(self) -> tuple[object, ...]:
        """Exact right-congruence key for carry, signed-fold and H5 outputs."""
        return (
            _BOOLEAN_ACTION_ID,
            self.modulus,
            pow(2, self.length, self.modulus),
            self.length % 6,
            self.next_carries,
            self.deltas,
            tuple((h.phi2, h.phi3_a, h.phi3_b) for h in self.harmonics),
        )

    @property
    def moore_carry_classes(self) -> int:
        return (
            1
            if self.next_carries[0] == self.next_carries[1]
            and self.deltas[0] == self.deltas[1]
            and self.harmonics[0] == self.harmonics[1]
            else 2
        )


__all__ = [
    "MAX_BOOLEAN_BLOCK_BITS",
    "MAX_BOOLEAN_LENGTH_BITS",
    "BinaryBooleanCarryAction",
]
