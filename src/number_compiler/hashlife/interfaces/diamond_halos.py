"""Certified right dependency bounds for the complete primitive interfaces.

A right automaton with one state needs no suffix. If every letter resets that
automaton, one input cell suffices. Composition adds these geometric bounds;
an uncertified bound remains unknown rather than truncating the input.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.resources.ledger import OwnedMemo

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


@dataclass(frozen=True, slots=True)
class RightHalo:
    action: ActionProgramID
    radius: int | None


class CausalHaloArena:
    def __init__(self, runtime: DiamondRuntime) -> None:
        self.runtime, self.ledger = runtime, runtime.ledger
        self.ledger.register_execution_root(self)
        self.owner = self.ledger.register(
            f"diamond-halos-{len(self.ledger.inventory())}", "causal_geometry"
        )
        self._radii: OwnedMemo[ActionProgramID, RightHalo] = OwnedMemo(
            self.ledger, self.owner, nodes_per_entry=1
        )

    def right(self, action: ActionProgramID) -> int | None:
        actions = self.runtime.actions
        actions.resolve(action)
        self.ledger.bump("causal_halo_requests")
        found = self._radii.get(action)
        if found is not None:
            self.ledger.bump("causal_halo_cache_hits")
            return found.radius
        self.ledger.bump("causal_halo_query_evaluations")
        pending = [(action, False)]
        while pending:
            previous = self.ledger.counters.get("causal_halo_stack_peak", 0)
            self.ledger.bump("causal_halo_stack_peak", max(0, len(pending) - previous))
            current, ready = pending.pop()
            self.ledger.bump("causal_halo_dag_visits")
            if current in self._radii:
                self.ledger.bump("causal_halo_node_cache_hits")
                continue
            node = actions.resolve(current)
            radius: int | None
            if node.kind == "identity":
                radius = 0
            elif node.kind == "atom":
                primitive = self.runtime.kernel(current)
                hooks = self.runtime.family_hooks
                if hooks is not None and hooks.owns_compatibility(primitive.effect):
                    radius = hooks.compatibility_halo(primitive.effect)
                elif primitive.right_count == 1:
                    radius = 0
                else:
                    reset = True
                    for symbol in range(primitive.blank + 1):
                        expected = primitive.advance(BoundarySide.RIGHT, 0, symbol)
                        for state in range(1, primitive.right_count):
                            self.ledger.bump("causal_halo_kernel_checks")
                            if (
                                primitive.advance(BoundarySide.RIGHT, state, symbol)
                                != expected
                            ):
                                reset = False
                                break
                        if not reset:
                            break
                    radius = 1 if reset else None
            else:
                first, second = (
                    actions.reference(node.first),
                    actions.reference(node.second),
                )
                if not ready:
                    pending.extend(((current, True), (second, False), (first, False)))
                    continue
                a, b = self._radii[first].radius, self._radii[second].radius
                radius = None if a is None or b is None else a + b
            self._radii[current] = RightHalo(current, radius)
            self.ledger.bump("causal_halo_evaluations")
        return self._radii[action].radius
