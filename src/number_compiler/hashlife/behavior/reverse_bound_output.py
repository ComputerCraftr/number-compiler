"""Concrete active carry behavior for one authenticated reverse output interval."""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.arithmetic.carry.carry_monoid import apply_carry_fn
from number_compiler.arithmetic.carry.reverse_port_functions import (
    ReverseLeftTransfer,
    ReversePortCodec,
    ReverseRightTransfer,
)
from number_compiler.resources.ledger import ResourceLedger

_ISSUED_REVERSE_OUTPUT = object()


@dataclass(frozen=True, slots=True)
class ReverseBoundOutput:
    """Output transfer for one bound occurrence, excluding exact digit observation."""

    left: ReverseLeftTransfer
    right: ReverseRightTransfer
    _owner: object | None = field(default=None, kw_only=True, repr=False)

    def __post_init__(self) -> None:
        if type(self.left) is not ReverseLeftTransfer:
            raise TypeError("bound reverse output requires a left transfer")
        if type(self.right) is not ReverseRightTransfer:
            raise TypeError("bound reverse output requires a right transfer")
        self.left.__post_init__()
        self.right.__post_init__()
        if self.left.base != self.right.base:
            raise ValueError("bound reverse output changes radix")
        if self._owner is not _ISSUED_REVERSE_OUTPUT:
            raise ValueError("bound reverse output was not issued by its finite law")

    @classmethod
    def leaf(cls, base: int, symbol: int) -> ReverseBoundOutput:
        return cls(
            ReverseLeftTransfer.leaf(base, symbol),
            ReverseRightTransfer.leaf(base, symbol),
            _owner=_ISSUED_REVERSE_OUTPUT,
        )

    def then(
        self, after: ReverseBoundOutput, ledger: ResourceLedger
    ) -> ReverseBoundOutput:
        """Concatenate adjacent outputs in physical least-to-most order."""
        self.__post_init__()
        if type(after) is not ReverseBoundOutput:
            raise TypeError("bound reverse composition requires two exact summaries")
        after.__post_init__()
        return ReverseBoundOutput(
            self.left.then(after.left, ledger),
            after.right.then(self.right, ledger),
            _owner=_ISSUED_REVERSE_OUTPUT,
        )

    def apply(self, side: int, consumer_state: int) -> int:
        """Advance one primitive consumer state over the bound output interval."""
        self.__post_init__()
        if type(side) is not int or side not in (0, 1):
            raise ValueError("bound reverse output requires a directed side")
        codec = ReversePortCodec(self.left.base)
        if side:
            return codec.encode_right(
                self.right.apply(codec.decode_right(consumer_state))
            )
        return codec.encode_left(self.left.apply(codec.decode_left(consumer_state)))

    def apply_digit_normalize(self, side: int, consumer_state: int) -> int:
        """Advance the four-state digit terminal without reading output symbols."""
        self.__post_init__()
        if type(side) is not int or side not in (0, 1):
            raise ValueError("digit normalization requires a directed side")
        if type(consumer_state) is not int:
            raise TypeError("digit normalization requires an exact finite state")
        if side:
            if consumer_state != 0:
                raise ValueError("digit normalization has one right boundary state")
            return 0
        if not 0 <= consumer_state < 4:
            raise ValueError("digit normalization left state is outside its domain")
        if consumer_state == 3:
            return 3
        if self.left.sinks or (consumer_state == 2 and self.left.has_active):
            return 3
        if self.left.has_blank:
            return 2
        if not self.left.has_active:
            return consumer_state
        incoming = 1 if consumer_state == 1 else 0
        return apply_carry_fn(self.left.carry, incoming)

    @property
    def retained_slots(self) -> int:
        return 9


__all__ = ["ReverseBoundOutput"]
