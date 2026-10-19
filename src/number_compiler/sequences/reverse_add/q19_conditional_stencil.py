"""Q19 source-punctured one-step LT/EQ/GT/F5/XOR successor stencil.

The symbolic pair field already is the arithmetic source.  Its two-ended
carry ports determine *the next symmetric pair field*, not merely its border
width. This exact local coordinate action is source-authenticated, can demand
an arbitrary cell without converting either decimal integer, and is the
primitive conditional law available to bounded one-step kernels.

No fixed-radius halo is assumed across an arbitrary all-9 carry wire.
The carry at a demanded position is folded from the Q19 SLP's actual prefix.
A temporal REPEAT still needs a separately certified complete output action.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Protocol

from number_compiler.arithmetic.fields.decimal_pair_partition import decimal_pair_band

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.inward_bank_harmonics import (
        InwardBankSelection,
        InwardBankWindow,
    )
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairOutputOccurrence,
        ReversePairQ19OutputOwner,
    )
    from number_compiler.sequences.reverse_add.q19_uniform_cone import (
        CertifiedUniformCone,
    )


def joint_xor_response(
    next_carry: int, borrow_ports: tuple[int, int]
) -> tuple[int, int]:
    """Combine a certified next carry with the two signed-borrow ports."""
    if (
        type(next_carry) is not int
        or next_carry not in (0, 1)
        or any(type(port) is not int or port not in (0, 1) for port in borrow_ports)
    ):
        raise ValueError("carry and borrow ports must be bits")
    return next_carry ^ borrow_ports[0], next_carry ^ borrow_ports[1]


class _QuietBorrowAction(Protocol):
    def at(self, offset: int, /) -> int: ...

    def next_quiet_borrow_response(self, offset: int, /) -> tuple[int, int]: ...


def next_quiet_joint_xor_response(
    action: _QuietBorrowAction, offset: int
) -> tuple[int, int]:
    """Combine one issued temporal cell and its next quiet borrow ports."""
    borrow_ports = action.next_quiet_borrow_response(offset)
    next_carry = int(action.at(offset + 1) > 9)
    return joint_xor_response(next_carry, borrow_ports)


@dataclass(frozen=True, slots=True)
class ConditionalPairCell:
    """One emitted target pair with its authentic reflected carry ingresses."""

    coordinate: int
    coefficient: int
    low_carry: int | None
    reflected_carry: int | None
    reflected_xor: int | None
    eq_birth: bool
    border_birth: bool = False

    @property
    def five_band(self) -> str:
        """Exact normalized pair coefficient domain for this output cell."""
        return decimal_pair_band(self.coefficient).value

    @property
    def f5(self) -> int:
        return self.coefficient % 5

    def __post_init__(self) -> None:
        if not 0 <= self.coefficient <= 18:
            raise ValueError("conditional pair stencil produced invalid Q19 atom")
        if self.border_birth:
            # The new growth-edge pair is a width seam, not an interior cell
            # with genuine two-sided carry ingresses. Never fabricate them.
            if any(
                port is not None
                for port in (self.low_carry, self.reflected_carry, self.reflected_xor)
            ):
                raise ValueError("growth birth must have punctured exterior ports")
        else:
            if self.low_carry not in (0, 1) or self.reflected_carry not in (0, 1):
                raise ValueError("conditional stencil requires real carry ports")
            if self.reflected_xor != self.low_carry ^ self.reflected_carry:
                raise ValueError("conditional stencil lost its reflected XOR")
        if self.eq_birth != (self.coefficient == 9):
            raise ValueError("conditional EQ port does not match its source atom")


@dataclass(frozen=True, slots=True)
class GuardedPairStencil:
    """One-step pair-field function with an exact Q19 root and growth seam."""

    source: ReversePairOutputOccurrence
    source_width: int
    target_pair_width: int
    source_growth: int

    @classmethod
    def from_occurrence(
        cls,
        owner: ReversePairQ19OutputOwner,
        source: ReversePairOutputOccurrence,
    ) -> GuardedPairStencil:
        owner.validate(source)
        growth = source.output_width - source.pair_width
        if growth not in (0, 1):
            raise ValueError("Q19 source normalized width is not a carry bit")
        return cls(source, source.pair_width, source.output_width, growth)

    def _assert_owner(self, owner: ReversePairQ19OutputOwner) -> None:
        owner.validate(self.source)
        if (
            self.source_width != self.source.pair_width
            or self.target_pair_width != self.source.output_width
            or self.source_growth != self.target_pair_width - self.source_width
        ):
            raise ValueError("conditional pair stencil root/width seam was altered")

    def carry_at(self, owner: ReversePairQ19OutputOwner, boundary: int) -> int:
        """c[boundary] via SLP transfer, not a materialized carry word."""
        self._assert_owner(owner)
        w = self.source_width
        if type(boundary) is not int or not 0 <= boundary <= w:
            raise IndexError(boundary)
        if boundary == 0:
            return 0
        root = self.source.root
        half = owner._summaries[root].symbols
        if boundary <= half:
            summary = owner._range_summary(root, 0, boundary)
        else:
            summary = owner._range_summary(root, 0, half).then(
                owner._range_summary(root, w - boundary, w - half, reverse=True)
            )
        return int(summary.domain == 1)

    def cell_at(
        self, owner: ReversePairQ19OutputOwner, coordinate: int
    ) -> ConditionalPairCell:
        """Produce the next pair atom, using both reflected carry ingresses."""
        self._assert_owner(owner)
        w, g = self.source_width, self.source_growth
        if type(coordinate) is not int or not 0 <= coordinate < w + g:
            raise IndexError(coordinate)
        if g and coordinate in (0, w):
            s0 = owner._pair_value_at(self.source, 0)
            c1 = self.carry_at(owner, 1)
            target = s0 + 1 - 10 * c1
            # The growth border is an extra leading 1 on normalized X;
            # both symmetric target coefficients share the same value.
            return ConditionalPairCell(
                coordinate,
                target,
                None,
                None,
                None,
                target == 9,
                border_birth=True,
            )
        s = owner._pair_value_at(self.source, coordinate)
        c0 = self.carry_at(owner, coordinate)
        c1 = self.carry_at(owner, coordinate + 1)
        if g:
            # Growth shifts one reflected index and creates an outer pair.
            prior = owner._pair_value_at(self.source, coordinate - 1)
            reflected = self.carry_at(owner, w - coordinate)
            reflected_after = self.carry_at(owner, w - coordinate + 1)
            target = s + prior + c0 + reflected - 10 * (c1 + reflected_after)
        else:
            reflected = self.carry_at(owner, w - 1 - coordinate)
            reflected_after = self.carry_at(owner, w - coordinate)
            target = 2 * s + c0 + reflected - 10 * (c1 + reflected_after)
            # XOR supplies the parity selector, F5 the residue selector.
            if (target == 9) != (s % 5 == 4 and (c0 ^ reflected) == 1):
                raise AssertionError("non-growth F5/XOR EQ birth lost its port")
            gt_high = (
                s in (8, 18)
                or (s in (7, 17) and (c0 or reflected))
                or (s == 9 and not c0 and not reflected)
            )
            if (15 <= target <= 18) != bool(gt_high):
                raise AssertionError("non-growth GT-high Boolean birth lost its port")
        return ConditionalPairCell(
            coordinate,
            target,
            c0,
            reflected,
            c0 ^ reflected,
            target == 9,
        )

    def inward_bank_at(
        self,
        owner: ReversePairQ19OutputOwner,
        coordinate: int,
        *,
        inward_lookahead: int = 4,
    ) -> InwardBankSelection:
        """Demand the GT/EQ/LT mask forced by bilateral Q19 reset ports.

        The current root supplies the exact outer carry and a bounded inward
        coefficient probe. A result with several masks is intentionally a
        conditional port rather than a guessed future digit. The existing
        cell_at remains available when a complete exact cell is required.
        """
        from .inward_bank_harmonics import inward_bank_select

        self._assert_owner(owner)
        return inward_bank_select(
            width=self.source_width,
            coordinate=coordinate,
            growth=self.source_growth,
            pair_at=lambda i: owner._pair_value_at(self.source, i),
            low_carry=self.carry_at(owner, coordinate),
            high_border_carries=(self.carry_at(owner, self.source_width - 1),),
            inward_lookahead=inward_lookahead,
        )

    def inward_bank_window(
        self,
        owner: ReversePairQ19OutputOwner,
        *,
        start: int,
        count: int = 64,
        inward_lookahead: int = 4,
    ) -> InwardBankWindow:
        """Demand up to 64 next bank masks from this source, with F5 Walsh.

        Source-owned one-step observer only: a finite temporal return still
        needs an independently certified future border+interior action.
        """
        from .inward_bank_harmonics import InwardBankWindow

        self._assert_owner(owner)
        if (
            type(start) is not int
            or type(count) is not int
            or start < 0
            or not 1 <= count <= 64
            or start + count > self.source_width // 2
        ):
            raise ValueError("mask window must fit the protected source half")
        return InwardBankWindow(
            start,
            tuple(
                self.inward_bank_at(
                    owner,
                    i,
                    inward_lookahead=inward_lookahead,
                )
                for i in range(start, start + count)
            ),
        )

    def authorize_temporal_cell(
        self,
        owner: ReversePairQ19OutputOwner,
        *,
        steps: int,
        coordinate: int,
    ) -> CertifiedUniformCone:
        """Power a protected finite-state cell without executing a target."""
        self._assert_owner(owner)
        from number_compiler.sequences.reverse_add.q19_uniform_cone import (
            authorize_uniform_cone,
        )

        return authorize_uniform_cone(
            owner, self.source, steps=steps, coordinate=coordinate
        )

    def verify_target_at(
        self,
        owner: ReversePairQ19OutputOwner,
        target: ReversePairOutputOccurrence,
        coordinate: int,
    ) -> ConditionalPairCell:
        """Bind a predicted cell to a separately issued Q19 successor root."""
        self._assert_owner(owner)
        owner.validate(target)
        if target.temporal_steps != self.source.temporal_steps + 1:
            raise ValueError("conditional stencil needs an adjacent successor")
        if target.pair_width != self.target_pair_width:
            raise ValueError("conditional stencil growth width seam mismatch")
        cell = self.cell_at(owner, coordinate)
        if owner._pair_value_at(target, coordinate) != cell.coefficient:
            raise ValueError("issued Q19 output conflicts with conditional stencil")
        return cell


__all__ = ["ConditionalPairCell", "GuardedPairStencil"]
