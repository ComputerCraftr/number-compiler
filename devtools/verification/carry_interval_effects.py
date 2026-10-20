"""Extensional carry boundary functions; no history or emitted tape payloads.

The epimorphism sends a coefficient to CONST0, ID, or CONST1 and a spatial
word to their composition. Its image deliberately forgets the emitted carry
word, the coefficient word, and the word's length. Geometry belongs to the
caller. The output-complete reverse program remains a separate object: this
finite spatial quotient does not prove temporal successor closure.

Exact reset itineraries, slab certificates, and tape-valued scan oracles live
in ``devtools.verification`` and are not dependencies of this module.
"""

from __future__ import annotations

from collections.abc import Iterable, MutableMapping, MutableSequence
from dataclasses import dataclass
from typing import Literal, cast

from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
from number_compiler.arithmetic.functions.finite_port_action import (
    FinitePortActionArena,
    PortVariable,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.proof_payload_admission import (
    register_proof_geometry_fields,
)


@dataclass(frozen=True, slots=True)
class CarryIntervalEffect:
    """Both oriented boundary functions and a capped reset observation."""

    forward: TransferSummaryID
    backward: TransferSummaryID
    reset_count: Literal[0, 1, 2]

    def __post_init__(self) -> None:
        if (
            type(self.forward) is not TransferSummaryID
            or type(self.backward) is not TransferSummaryID
        ):
            raise TypeError("interval effects require scoped finite functions")
        self.forward.validate(self.backward.owner, "finite-port-function")
        self.backward.validate(self.forward.owner, "finite-port-function")
        if type(self.reset_count) is not int or self.reset_count not in (0, 1, 2):
            raise ValueError("reset observation must be a capped three-state count")


@dataclass(frozen=True, slots=True)
class CarryIntervalCompositionKey:
    """The complete input identity, available before evaluating composition."""

    before: TransferSummaryID
    after: TransferSummaryID
    port: PortVariable

    def __post_init__(self) -> None:
        if (
            type(self.before) is not TransferSummaryID
            or type(self.after) is not TransferSummaryID
        ):
            raise TypeError("interval composition requires scoped transfer IDs")
        self.before.validate(self.after.owner, "carry-interval-effect")
        self.after.validate(self.before.owner, "carry-interval-effect")
        if type(self.port) is not PortVariable:
            raise TypeError("interval composition requires a symbolic port")


class CarryActionQuotientArena(FinitePortActionArena):
    """Canonical finite port effects, using only ledger-owned decision nodes.

    There is no source-word interner, output tape, or inverse row projection.
    Equal functions receive equal scoped IDs even when their preimages have
    different lengths and different interior carry rows.
    """

    def __init__(self, ledger: ResourceLedger | None = None) -> None:
        super().__init__(ledger)
        prefix = f"carry-interval-{len(self.ledger.inventory())}"
        self._interval_owner = self.ledger.register(
            prefix + "-effects", "canonical_transfer"
        )
        self._interval_key_owner = self.ledger.register(
            prefix + "-interner", "transfer_interner"
        )
        self._intervals: MutableSequence[CarryIntervalEffect] = self.ledger.make_list(
            self._interval_owner
        )
        self._interval_ids: MutableMapping[CarryIntervalEffect, int] = (
            self.ledger.make_dict(self._interval_key_owner)
        )
        composition_owner = self.ledger.register(prefix + "-compositions", "query_memo")
        self._interval_compositions: OwnedMemo[
            CarryIntervalCompositionKey, TransferSummaryID
        ] = OwnedMemo(
            self.ledger,
            composition_owner,
            evictable=True,
            composition_entries=True,
        )
        literal_owner = self.ledger.register(prefix + "-literals", "query_memo")
        reflection_owner = self.ledger.register(prefix + "-reflections", "query_memo")
        self._interval_literals: OwnedMemo[TransferSummaryID, TransferSummaryID] = (
            OwnedMemo(
                self.ledger,
                literal_owner,
                evictable=True,
            )
        )
        self._interval_reflections: OwnedMemo[TransferSummaryID, TransferSummaryID] = (
            OwnedMemo(
                self.ledger,
                reflection_owner,
                evictable=True,
            )
        )

    def carry_code(
        self, function: TransferSummaryID, port: PortVariable
    ) -> Literal[0, 1, 2]:
        """Classify an already canonical CONST0/ID/CONST1 without applying it.

        This inspects the finite kernel node, never a source occurrence or a
        table of emitted carries. Unknown ports and non-monotone maps reject.
        """
        index = self.resolve_index(function)
        if type(port) is not PortVariable:
            raise TypeError("carry classification requires a symbolic port")
        self.ledger.bump("reverse_carry_function_classifications")
        if index < 2:
            return 0 if index == 0 else 2
        node = self._nodes[index]
        if node.variable == port and node.low == 0 and node.high == 1:
            return 1
        raise ValueError("function is not a carry reset or identity on this port")

    def interval_effect(self, action: TransferSummaryID) -> CarryIntervalEffect:
        """Resolve a complete effect only after checking its owner and kind."""
        if type(action) is not TransferSummaryID:
            raise TypeError("expected a scoped interval transfer ID")
        action.validate(self.owner, "carry-interval-effect", size=len(self._intervals))
        return self._intervals[action.local_id]

    def intern_interval(self, effect: CarryIntervalEffect) -> TransferSummaryID:
        self.resolve_index(effect.forward)
        self.resolve_index(effect.backward)
        found = self._interval_ids.get(effect)
        if found is None:
            self.ledger.reserve_many(
                ((self._interval_owner, 1, 1), (self._interval_key_owner, 1, 0))
            )
            found = len(self._intervals)
            self._intervals.append(effect)
            self._interval_ids[effect] = found
            self.ledger.bump("interval_effect_intern_misses")
        else:
            self.ledger.bump("interval_effect_intern_hits")
        return TransferSummaryID(self.owner, "carry-interval-effect", found)

    def reflect_interval(self, action: TransferSummaryID) -> TransferSummaryID:
        """An exact orientation change, requiring no source or carry scan."""
        effect = self.interval_effect(action)
        self.ledger.bump("interval_reflection_requests")
        if effect.forward == effect.backward:
            self.ledger.bump("interval_reflection_identity_hits")
            return action
        found = self._interval_reflections.get(action)
        if found is not None:
            self.ledger.bump("interval_reflection_cache_hits")
            return found
        self.ledger.bump("interval_reflection_evaluations")
        result = self.intern_interval(
            CarryIntervalEffect(effect.backward, effect.forward, effect.reset_count)
        )
        self._interval_reflections[action] = result
        return result

    def _literal(
        self, function: TransferSummaryID, resets: Literal[0, 1]
    ) -> TransferSummaryID:
        # Only kernel-generated CONST0/ID/CONST1 functions enter here. Their
        # canonical IDs determine the whole one-cell effect before interning.
        self.ledger.bump("interval_literal_requests")
        found = self._interval_literals.get(function)
        if found is not None:
            self.ledger.bump("interval_literal_cache_hits")
            return found
        self.ledger.bump("interval_literal_evaluations")
        result = self.intern_interval(CarryIntervalEffect(function, function, resets))
        self._interval_literals[function] = result
        return result

    def interval_identity(self, port: PortVariable) -> TransferSummaryID:
        function = self.variable(port)
        return self._literal(function, 0)

    def interval_symbol(
        self, value: int, *, base: int, port: PortVariable
    ) -> TransferSummaryID:
        function = self.symbol(value, base=base, port=port)
        resets: Literal[0, 1] = 0 if value == base - 1 else 1
        return self._literal(function, resets)

    def compose_intervals(
        self,
        before: TransferSummaryID,
        after: TransferSummaryID,
        port: PortVariable,
    ) -> TransferSummaryID:
        """Compose complete interval effects entirely on canonical IDs.

        Forward carries cross the first interval then the second. Reflection
        reverses that composition order. Reset counts compose by capped sum;
        neither their locations nor any emitted interior values are retained.
        """
        first, second = self.interval_effect(before), self.interval_effect(after)
        key = CarryIntervalCompositionKey(before, after, port)
        self.ledger.bump("composition_requests")
        self.ledger.bump("joint_interval_composition_requests")
        found = self._interval_compositions.get(key)
        if found is not None:
            self.ledger.bump("composition_cache_hits")
            self.ledger.bump("joint_interval_composition_cache_hits")
            return found
        self.ledger.bump("composition_evaluations")
        self.ledger.bump("joint_interval_composition_evaluations")
        forward = self.compose(first.forward, second.forward, port)
        backward = self.compose(second.backward, first.backward, port)
        count = cast(Literal[0, 1, 2], min(2, first.reset_count + second.reset_count))
        result = self.intern_interval(CarryIntervalEffect(forward, backward, count))
        self._interval_compositions[key] = result
        return result

    def interval_word(
        self, values: Iterable[int], *, base: int, port: PortVariable
    ) -> TransferSummaryID:
        if type(base) is not int or base < 2:
            raise ValueError("carry effects require a radix of at least two")
        action = self.interval_identity(port)
        for value in values:
            symbol = self.interval_symbol(value, base=base, port=port)
            action = self.compose_intervals(action, symbol, port)
        return action

    def retained_entries(self) -> int:
        return (
            super().retained_entries()
            + len(self._intervals)
            + len(self._interval_ids)
            + len(self._interval_compositions)
            + len(self._interval_literals)
            + len(self._interval_reflections)
        )

    def interval_cache_sizes(self) -> tuple[int, int, int]:
        """Report composition, literal, and reflection memo entry counts."""
        return (
            len(self._interval_compositions),
            len(self._interval_literals),
            len(self._interval_reflections),
        )

    def symbol(self, value: int, *, base: int, port: PortVariable) -> TransferSummaryID:
        if type(base) is not int or base < 2:
            raise ValueError("carry effects require a radix of at least two")
        if type(value) is not int or not 0 <= value <= 2 * (base - 1):
            raise ValueError("coefficient is outside the reverse pair alphabet")
        if type(port) is not PortVariable:
            raise TypeError("carry effects require a symbolic boundary port")
        return self.unary(port, value >= base, value >= base - 1)

    def word(
        self,
        values: Iterable[int],
        *,
        base: int,
        port: PortVariable,
    ) -> TransferSummaryID:
        """Consume coefficients transiently and return only their exit action."""
        if type(base) is not int or base < 2:
            raise ValueError("carry effects require a radix of at least two")
        if type(port) is not PortVariable:
            raise TypeError("carry effects require a symbolic boundary port")
        action = self.variable(port)
        for value in values:
            action = self.compose(
                action, self.symbol(value, base=base, port=port), port
            )
        return action


register_proof_geometry_fields(
    {
        CarryIntervalEffect: frozenset(),
        CarryIntervalCompositionKey: frozenset(),
    }
)


__all__ = ["CarryActionQuotientArena", "CarryIntervalEffect"]
