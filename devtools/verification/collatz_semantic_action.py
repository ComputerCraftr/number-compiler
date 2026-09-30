"""Proof-only finite Collatz phases bound to exact tail occurrences.

Production Collatz powering uses the algebraic field-action runtime.  This
compatibility arena accepts an exact ``DyadicSpan`` and therefore belongs with
the exact forcing/orbit oracles rather than in the production package root.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.directed_field import DirectedTileTransducerArena
from number_compiler.arithmetic.fields.dyadic_tile import DyadicSpan


@dataclass(frozen=True, slots=True)
class CollatzBlockAction:
    """Universal accelerated-tail operator phase for proof compatibility.

    The arithmetic rule itself does not depend on the exact normalized tail:
    every non-fixed occurrence runs the same finite ``3*x+1`` digit transducer
    and then either performs or skips the one-bit structural shift.  Tail-
    specific incoming->outgoing carry behavior is already interned at the
    dyadic spatial-action layer and must not over-key the temporal operator.

    Exact tail digits remain occurrence payload because this operator is not a
    successor-closed state quotient.
    """

    action_id: int
    local_shift: int

    def __post_init__(self) -> None:
        if type(self.action_id) is not int:
            raise TypeError("Collatz action identity must be an exact integer")
        if self.action_id < 0:
            raise ValueError(
                "Collatz action identity must be a nonnegative exact integer"
            )
        if type(self.local_shift) is not int:
            raise TypeError("Collatz local shift must be an exact integer")
        if self.local_shift not in (0, 1):
            raise ValueError(self.local_shift)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz-block-operator", self.local_shift)


@dataclass(frozen=True, slots=True)
class CollatzBlockActionMetrics:
    requests: int
    hits: int
    actions: int
    aliases: int


class CollatzBlockActionArena:
    """Intern the two source-independent accelerated Collatz proof phases.

    ``DirectedTileTransducerArena`` remains the owner of source-specific finite
    boundary actions.  This arena deliberately does not duplicate those maps.
    """

    __slots__ = ("_actions", "aliases", "hits", "mul3", "requests")

    def __init__(self, mul3: DirectedTileTransducerArena) -> None:
        self.mul3 = mul3
        self._actions: dict[int, CollatzBlockAction] = {}
        self.requests = 0
        self.hits = 0
        self.aliases = 0

    def intern(self, tail: DyadicSpan, local_shift: int) -> CollatzBlockAction:
        if type(tail) is not DyadicSpan:
            raise TypeError("Collatz action occurrence requires an exact dyadic span")
        if type(local_shift) is not int:
            raise TypeError("Collatz local shift must be an exact integer")
        if tail.start != 0 or tail.length <= 0 or local_shift not in (0, 1):
            raise ValueError((tail.start, tail.length, local_shift))
        self.requests += 1
        # Charge/intern the exact spatial boundary programs separately.  They
        # are useful HashLife sub-actions but are not temporal operator identity.
        for chunk in tail.chunks:
            self.mul3.action_ref(chunk.tile)
        found = self._actions.get(local_shift)
        if found is not None:
            self.hits += 1
            self.aliases += 1
            return found
        out = CollatzBlockAction(len(self._actions), local_shift)
        self._actions[local_shift] = out
        return out

    def metrics(self) -> CollatzBlockActionMetrics:
        return CollatzBlockActionMetrics(
            self.requests,
            self.hits,
            len(self._actions),
            self.aliases,
        )


__all__ = ["CollatzBlockAction", "CollatzBlockActionArena", "CollatzBlockActionMetrics"]
