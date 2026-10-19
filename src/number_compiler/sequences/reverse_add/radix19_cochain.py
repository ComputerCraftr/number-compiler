"""Source-bound radix-19 coefficient carry cochain for decimal reverse/add.

Symmetric decimal pair sums form a redundant coefficient alphabet 0..18;
they are not digits of a radix-19 reversal.  This module folds their exact
decimal carry correction over the issued source SLP, including CONCAT and
REPEAT, without materializing a successor or expanding a repeated word.

The resulting polynomial is an exact one-step spatial projection. It does
not authorize an unknown temporal growth word or a complete future integer.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.slp_interval import fold_slp_dag
from number_compiler.arithmetic.fields.decimal_pair_partition import (
    DECIMAL_PAIR_BAND_NAMES,
    DecimalPairBand,
    decimal_pair_band,
)
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

if TYPE_CHECKING:
    from .q19_occurrence import ReversePairOutputOccurrence
    from .q19_output import ReversePairQ19OutputOwner


@dataclass(frozen=True, slots=True)
class Radix19CarryBlock:
    """Polynomial and two-ingress carry summaries for one coefficient block."""

    length: int
    shift: int
    pairs: int
    carry: tuple[int, int]
    reverse_carry: tuple[int, int]
    reverse_tail: tuple[int, int]
    exits: tuple[int, int]
    z: int
    modulus: int

    @classmethod
    def identity(cls, z: int, modulus: int) -> Radix19CarryBlock:
        if type(z) is not int or type(modulus) is not int or modulus < 2:
            raise ValueError("cochain ring requires integer z and modulus >= 2")
        return cls(
            0, 1 % modulus, 0, (0, 0), (0, 0), (0, 0), (0, 1), z % modulus, modulus
        )

    @classmethod
    def atom(cls, symbol: int, z: int, modulus: int) -> Radix19CarryBlock:
        if type(symbol) is not int or not 0 <= symbol <= 18:
            raise ValueError("radix-19 pair coefficient must be in 0..18")
        if type(z) is not int or type(modulus) is not int or modulus < 2:
            raise ValueError("cochain ring requires integer z and modulus >= 2")
        exits = (int(symbol >= 10), int(symbol >= 9))
        return cls(
            1,
            z % modulus,
            symbol % modulus,
            exits,
            exits,
            (0, 0),
            exits,
            z % modulus,
            modulus,
        )

    def then(
        self,
        upper: Radix19CarryBlock,
        *,
        on_compose: Callable[[], None] | None = None,
    ) -> Radix19CarryBlock:
        """Append the more significant coefficients with correlated ingress."""
        if type(upper) is not Radix19CarryBlock or (self.z, self.modulus) != (
            upper.z,
            upper.modulus,
        ):
            raise ValueError("carry blocks require the same polynomial ring")
        if not self.length:
            return upper
        if not upper.length:
            return self
        if on_compose is not None:
            on_compose()
        m, z = self.modulus, self.z
        upper_ingress = self.exits
        exits: tuple[int, int] = (
            upper.exits[upper_ingress[0]],
            upper.exits[upper_ingress[1]],
        )
        carry: tuple[int, int] = (
            (self.carry[0] + self.shift * upper.carry[upper_ingress[0]]) % m,
            (self.carry[1] + self.shift * upper.carry[upper_ingress[1]]) % m,
        )
        reverse_carry: tuple[int, int] = (
            (
                upper.shift * self.reverse_carry[0]
                + upper.reverse_carry[upper_ingress[0]]
            )
            % m,
            (
                upper.shift * self.reverse_carry[1]
                + upper.reverse_carry[upper_ingress[1]]
            )
            % m,
        )
        # Drop the terminal carry coefficient without dividing by z.
        reverse_tail: tuple[int, int] = (
            (
                upper.reverse_tail[upper_ingress[0]]
                + pow(z, upper.length - 1, m) * self.reverse_carry[0]
            )
            % m,
            (
                upper.reverse_tail[upper_ingress[1]]
                + pow(z, upper.length - 1, m) * self.reverse_carry[1]
            )
            % m,
        )
        return Radix19CarryBlock(
            self.length + upper.length,
            self.shift * upper.shift % m,
            (self.pairs + self.shift * upper.pairs) % m,
            carry,
            reverse_carry,
            reverse_tail,
            exits,
            z,
            m,
        )

    def repeat(
        self, count: int, *, on_compose: Callable[[], None] | None = None
    ) -> Radix19CarryBlock:
        if type(count) is not int or count < 0:
            raise ValueError("cochain repetition count must be nonnegative")
        return binary_power(
            self,
            count,
            identity=self.identity(self.z, self.modulus),
            compose=lambda first, second: first.then(second, on_compose=on_compose),
        ).value

    def normalized_polynomial(self, ingress: int = 0) -> int:
        """Evaluate normalized decimal digits, including a terminal carry."""
        if type(ingress) is not int or ingress not in (0, 1):
            raise ValueError("incoming carry must be Boolean")
        return (
            self.pairs + ingress + (self.z - 10) * self.carry[ingress]
        ) % self.modulus

    def successor_pair_polynomial(self) -> int:
        """Evaluate every next symmetric pair from the physical zero ingress."""
        if self.length == 0:
            raise ValueError("empty pair tape has no decimal successor")
        growth = self.exits[0]
        reflected = (
            self.reverse_tail[0] - 10 * self.reverse_carry[0]
            if growth == 0
            else self.reverse_carry[0] - 10 * self.z * self.reverse_carry[0]
        )
        return (
            (1 + (self.z if growth else 1)) * self.pairs
            + (self.z - 10) * self.carry[0]
            + reflected
        ) % self.modulus


@dataclass(frozen=True, slots=True)
class _HalfSummary:
    forward: Radix19CarryBlock
    reverse: Radix19CarryBlock
    prefix_reverse: Radix19CarryBlock


def fold_source_pair_cochain(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    *,
    z: int,
    modulus: int,
) -> Radix19CarryBlock:
    """Fold the authenticated physical palindrome and its center once."""
    owner.validate(source)
    if type(z) is not int or type(modulus) is not int or modulus < 2:
        raise ValueError("integer evaluation and modulus >= 2 required")
    zero = Radix19CarryBlock.identity(z, modulus)
    identity = _HalfSummary(zero, zero, zero)

    def record_composition() -> None:
        owner.ledger.bump(_reverse_add_keys.REVERSE_RADIX19_COCHAIN_COMPOSITIONS)

    def terminal(symbol: int) -> _HalfSummary:
        if symbol in (19, 20, 21):
            return identity
        atom = Radix19CarryBlock.atom(symbol, z, modulus)
        return _HalfSummary(atom, atom, zero)

    def concatenate(left: _HalfSummary, right: _HalfSummary) -> _HalfSummary:
        prefix_reverse = (
            right.prefix_reverse.then(left.reverse, on_compose=record_composition)
            if right.forward.length
            else left.prefix_reverse
        )
        return _HalfSummary(
            left.forward.then(right.forward, on_compose=record_composition),
            right.reverse.then(left.reverse, on_compose=record_composition),
            prefix_reverse,
        )

    def repeat(value: _HalfSummary, count: int) -> _HalfSummary:
        if count == 0 or value.forward.length == 0:
            return identity
        return _HalfSummary(
            value.forward.repeat(count, on_compose=record_composition),
            value.reverse.repeat(count, on_compose=record_composition),
            value.prefix_reverse.then(
                value.reverse.repeat(count - 1, on_compose=record_composition),
                on_compose=record_composition,
            ),
        )

    node_count = len(owner.arena.nodes) + 1
    with owner.ledger.reservation(
        owner._scratch_owner, entries=3 * node_count, nodes=9 * node_count
    ):
        summaries = fold_slp_dag(
            owner.arena,
            source.root,
            empty_value=identity,
            terminal_value=terminal,
            concatenate=concatenate,
            repeat=repeat,
            on_pending=lambda _node: owner.ledger.bump(
                _reverse_add_keys.REVERSE_RADIX19_COCHAIN_NODE_VISITS
            ),
        )
        half = summaries[source.root]
        parity = owner._symbol_at(source.root, 0) - 19
        if parity not in (0, 1):
            raise ValueError("invalid Q19 parity tag")
        result = half.forward.then(
            half.prefix_reverse if parity else half.reverse,
            on_compose=record_composition,
        )
        if result.length != source.pair_width:
            raise AssertionError("carry cochain lost palindrome or center")
        if result.exits[0] != source.output_width - source.pair_width:
            raise AssertionError("cochain growth disagrees with issued source")
        return result


def source_walsh64_mod5(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    *,
    channel: str,
    start: int = 0,
) -> tuple[int, ...]:
    """Transform 64 authenticated source or conditional future Boolean lanes."""
    from number_compiler.arithmetic.fields.walsh import walsh64_mod5

    from .q19_conditional_stencil import GuardedPairStencil

    owner.validate_issued_occurrence(source)
    if type(start) is not int or start < 0:
        raise ValueError("Walsh lane start must be nonnegative")
    allowed = {
        *DECIMAL_PAIR_BAND_NAMES,
        "carry",
        "reflected_xor",
        "future_eq",
        "future_gt_high",
    }
    if channel not in allowed:
        raise ValueError("Walsh channel must name a certified Boolean pair port")
    stencil = GuardedPairStencil.from_occurrence(owner, source)
    width = (
        stencil.target_pair_width
        if channel.startswith("future_")
        else source.pair_width
    )
    if start + 64 > width:
        raise ValueError("Walsh64 exceeds the certified pair width")
    mask = 0
    for lane in range(64):
        index = start + lane
        if channel.startswith("future_"):
            symbol = stencil.cell_at(owner, index).coefficient
            expected = (
                DecimalPairBand.EQ
                if channel == "future_eq"
                else DecimalPairBand.GT_HIGH
            )
            bit = decimal_pair_band(symbol) is expected
        elif channel == "carry":
            bit = bool(stencil.carry_at(owner, index + 1))
        elif channel == "reflected_xor":
            bit = bool(
                stencil.carry_at(owner, index)
                ^ stencil.carry_at(owner, source.pair_width - 1 - index)
            )
        else:
            pair = owner._pair_value_at(source, index)
            bit = decimal_pair_band(pair) is DecimalPairBand(channel)
        mask |= int(bit) << lane
    return walsh64_mod5(mask)


__all__ = ["Radix19CarryBlock", "fold_source_pair_cochain", "source_walsh64_mod5"]
