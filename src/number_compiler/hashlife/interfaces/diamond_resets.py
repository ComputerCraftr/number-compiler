"""Certified synchronization of complete right boundary states.

A radius r means that every word of length at least r erases the incoming
right boundary state. This is stronger than an output dependency halo.

For A followed by B, rA+rB suffices: A's right anchor forgets its input after
rA letters. B's final state depends only on its last rB output letters in reverse
scan order. Those output letters, nearest the left edge of the
word, depend on A's old right anchor only through suffixes of length at least
rA. Their complete functions of the free A-left port consequently agree.
Thus both the A anchor and the whole B continuation agree, not just emissions.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.interfaces.diamond_boundary import ImageBinding
from number_compiler.resources.ledger import OwnedMemo

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


@dataclass(frozen=True, slots=True)
class RightResetCertificate:
    action: ActionProgramID
    radius: int | None
    law: str = "complete-right-boundary-synchronization-v1"

    def __post_init__(self) -> None:
        if (
            type(self.action) is not ActionProgramID
            or self.action.kind != "diamond-action"
            or self.radius is not None
            and (type(self.radius) is not int or self.radius < 0)
            or self.law != "complete-right-boundary-synchronization-v1"
        ):
            raise ValueError("invalid complete right-state reset certificate")


class RightResetCertificates:
    def __init__(self, runtime: DiamondRuntime) -> None:
        self.runtime, self.ledger = runtime, runtime.ledger
        self.ledger.register_execution_root(self)
        owner = self.ledger.register(
            f"diamond-right-resets-{len(self.ledger.inventory())}",
            "right_reset_certificate",
        )
        self.certificates: OwnedMemo[ActionProgramID, RightResetCertificate] = (
            OwnedMemo(self.ledger, owner, nodes_per_entry=1)
        )

    def radius(self, action: ActionProgramID) -> int | None:
        actions = self.runtime.actions
        actions.resolve(action)
        pending = [(action, False)]
        visits = peak = 0
        while pending:
            visits += 1
            peak = max(peak, len(pending))
            current, ready = pending.pop()
            if current in self.certificates:
                self.ledger.bump("right_reset_certificate_hits")
                continue
            node = actions.resolve(current)
            if node.kind == "compose" and not ready:
                first, second = (
                    actions.reference(node.first),
                    actions.reference(node.second),
                )
                pending.extend(((current, True), (second, False), (first, False)))
                continue
            # The proof is required retained work. Reserve its slot and node
            # before kernel admission or transition inspection, including when
            # the budget is already exhausted. Publish through the same owned
            # store without charging a second time; a failed proof releases this
            # reservation, leaving no speculative certificate behind.
            owner = self.certificates.owner
            self.ledger.reserve(owner, entries=1, nodes=1)
            try:
                radius: int | None
                if node.kind == "identity":
                    radius = 0
                elif node.kind == "compose":
                    first, second = (
                        actions.reference(node.first),
                        actions.reference(node.second),
                    )
                    a, b = (
                        self.certificates[first].radius,
                        self.certificates[second].radius,
                    )
                    radius = None if a is None or b is None else a + b
                else:
                    radius = self._primitive_radius(current)
                self.certificates._data[current] = RightResetCertificate(
                    current, radius
                )
            except BaseException:
                self.ledger.release(owner, entries=1, nodes=1)
                raise
            self.ledger.bump("right_reset_certificate_evaluations")
        self.ledger.bump("right_reset_requests")
        self.ledger.bump("right_reset_dag_visits", visits)
        previous_peak = self.ledger.counters.get("right_reset_stack_peak", 0)
        self.ledger.bump("right_reset_stack_peak", max(0, peak - previous_peak))
        return self.certificates[action].radius

    def _primitive_radius(self, action: ActionProgramID) -> int | None:
        primitive = self.runtime.kernel(action)
        hooks = self.runtime.family_hooks
        if hooks is not None and hooks.owns_compatibility(primitive.effect):
            return hooks.compatibility_reset_radius(primitive.effect)
        if primitive.right_count == 1:
            return 0
        for symbol in range(primitive.blank + 1):
            target = primitive.advance(BoundarySide.RIGHT, 0, symbol)
            self.ledger.bump("right_reset_primitive_checks")
            for state in range(1, primitive.right_count):
                actual = primitive.advance(BoundarySide.RIGHT, state, symbol)
                self.ledger.bump("right_reset_primitive_checks")
                if actual != target:
                    return None
        return 1

    def can_reset(
        self, provider: ImageBinding, action: ActionProgramID, side: int
    ) -> bool:
        if type(side) is not int or side not in (0, 1):
            raise ValueError("invalid reset direction")
        self.runtime._validate_provider(provider)
        node = self.runtime.actions.resolve(action)
        source = self.runtime.cells.source_geometry._construction.source
        if node.kind != "identity" and (node.base, node.blank) != (
            source.base,
            source.blank,
        ):
            raise ValueError("reset action and source alphabets disagree")
        if side != 1:
            return False
        radius = self.radius(action)
        # Compare dyadic geometry without constructing a huge 2**level integer.
        return radius is not None and (
            radius == 0
            or self.runtime.cells.input_level(provider.cell)
            >= (radius - 1).bit_length()
        )
