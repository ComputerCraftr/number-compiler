"""Lazy fresh-prime wheel actions over a descriptor-only parent period.

One parent period ``W`` is a ``q``-port action.  At incoming phase ``a`` it
keeps the parent-wheel survivors ``x in [1,W]`` except those for which
``x+a`` lies in a requested forbidden class modulo the fresh prime ``q``.
Ports, descendants, and ranks are evaluated on demand; neither the parent gap
cycle nor a ``q``-entry port table is retained.
"""

from __future__ import annotations

from collections.abc import Hashable
from dataclasses import dataclass
from math import prod
from typing import cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG


@dataclass(frozen=True, slots=True)
class PrimeSuccessorActionDescriptor:
    parent_factors: tuple[int, ...]
    parent_period: int
    fresh_prime: int
    forbidden_residues: tuple[int, ...]

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "prime-successor-action-v1",
            self.parent_factors,
            self.parent_period,
            self.fresh_prime,
            self.forbidden_residues,
        )


@dataclass(frozen=True, slots=True)
class PrimeSuccessorActionNode:
    copies: int
    phase_shift: int
    before: PrimeSuccessorActionID | None
    after: PrimeSuccessorActionID | None

    @property
    def primitive(self) -> bool:
        return self.copies == 1

    @property
    def identity(self) -> bool:
        return self.copies == 0


@dataclass(frozen=True, slots=True)
class PrimeSuccessorPortEffect:
    entering_phase: int
    outgoing_phase: int
    parent_survivors: int
    deleted_survivors: int
    surviving_values: int


@dataclass(frozen=True, slots=True)
class PrimeSuccessorActionMetrics:
    action_nodes: int
    composition_entries: int
    demanded_ports: int
    progression_states: int
    work: int
    retained_entries: int
    retained_nodes: int
    parent_gap_positions_materialized: int = 0


@dataclass(frozen=True, slots=True)
class PrimeSuccessorActionID(ArenaHandle):
    """Arena-scoped action identity; foreign integer IDs cannot alias."""


@dataclass(frozen=True, slots=True)
class PrimeSuccessorDescriptorID(ArenaHandle):
    """Small source authority for an arena-interned parent descriptor."""


@dataclass(frozen=True, slots=True)
class PrimeSuccessorSource:
    descriptor: PrimeSuccessorDescriptorID
    entering_phase: int


@dataclass(frozen=True, slots=True)
class PrimeSuccessorImagePayload:
    descriptor: PrimeSuccessorDescriptorID
    action: PrimeSuccessorActionID
    entering_phase: int
    outgoing_phase: int
    parent_survivors: int
    deleted_survivors: int
    surviving_values: int


class PrimeSuccessorActionArena:
    """Own and evaluate one source-qualified fresh-prime action DAG.

    The supplied rank owner must contain a consecutive prime prefix.  Freshness
    is checked constructively: below ``q`` the parent wheel has only survivor
    ``1``, and adjoining ``q`` adds exactly that next survivor.
    """

    def __init__(
        self,
        rank: CoprimeRankDAG,
        fresh_prime: int,
        *,
        forbidden_residues: tuple[int, ...] = (0,),
        max_action_entries: int | None = None,
    ) -> None:
        if type(fresh_prime) is not int or fresh_prime < 2:
            raise ValueError("fresh prime must be an integer >= 2")
        if not rank.primes or fresh_prime <= rank.last_factor:
            raise ValueError("fresh prime must follow a nonempty parent prefix")
        if max_action_entries is not None and (
            type(max_action_entries) is not int or max_action_entries < 4
        ):
            raise ValueError("prime action budget must be at least four entries")
        raw_forbidden = tuple(forbidden_residues)
        if not raw_forbidden or any(type(value) is not int for value in raw_forbidden):
            raise ValueError("fresh-prime forbidden residues must be integers")
        q = fresh_prime
        forbidden = tuple(sorted({value % q for value in raw_forbidden}))
        # This authenticates the complete parent prefix and discharges
        # freshness from that admitted source.  No primality oracle participates.
        rank.validate_fresh_successor(q)

        self.rank = rank
        self._owner = ArenaToken("prime-successor-actions")
        self.descriptor = PrimeSuccessorActionDescriptor(
            rank.primes, prod(rank.primes), q, forbidden
        )
        self.descriptor_id = PrimeSuccessorDescriptorID(
            self._owner, "prime-successor-descriptor", 0
        )
        self.max_action_entries = max_action_entries
        ledger = rank.ledger
        node_owner = ledger.register(
            "prime.successor.nodes", "fresh-prime chronological action nodes"
        )
        composition_owner = ledger.register(
            "prime.successor.normal-forms", "fresh-prime action normal forms"
        )
        port_owner = ledger.register(
            "prime.successor.ports", "demanded fresh-prime port effects"
        )
        self._nodes: OwnedMemo[int, PrimeSuccessorActionNode] = OwnedMemo(
            ledger, node_owner, nodes_per_entry=1
        )
        self._normal_forms: OwnedMemo[int, PrimeSuccessorActionID] = OwnedMemo(
            ledger, composition_owner, composition_entries=True
        )
        self._ports: OwnedMemo[
            tuple[PrimeSuccessorActionID, int], PrimeSuccessorPortEffect
        ] = OwnedMemo(ledger, port_owner)
        self._next_node = 0
        self._closed = False
        self.identity = self._append_node(PrimeSuccessorActionNode(0, 0, None, None))
        self.base = self._append_node(
            PrimeSuccessorActionNode(1, self.descriptor.parent_period % q, None, None)
        )
        self._normal_forms[0] = self.identity
        self._normal_forms[1] = self.base

    def _check_open(self) -> None:
        if self._closed:
            raise RuntimeError("prime successor action arena is closed")
        depth = len(self.descriptor.parent_factors)
        if self.rank.primes[:depth] != self.descriptor.parent_factors:
            raise RuntimeError("prime successor action lost its parent source binding")

    def _check_budget(self, additional: int = 1) -> None:
        retained = len(self._nodes) + len(self._normal_forms) + len(self._ports)
        if (
            self.max_action_entries is not None
            and retained + additional > self.max_action_entries
        ):
            raise ValueError("prime action budget exceeded")

    def _append_node(self, node: PrimeSuccessorActionNode) -> PrimeSuccessorActionID:
        self._check_budget()
        node_id = self._next_node
        self._next_node += 1
        self._nodes[node_id] = node
        return PrimeSuccessorActionID(self._owner, "prime-successor-action", node_id)

    def node(self, action: PrimeSuccessorActionID) -> PrimeSuccessorActionNode:
        self._check_open()
        if type(action) is not PrimeSuccessorActionID:
            raise TypeError("expected a prime successor action ID")
        action.validate(self._owner, "prime-successor-action", size=len(self._nodes))
        return self._nodes[action.local_id]

    def validate_descriptor(self, descriptor: PrimeSuccessorDescriptorID) -> None:
        if type(descriptor) is not PrimeSuccessorDescriptorID:
            raise TypeError("expected a prime successor descriptor ID")
        descriptor.validate(self._owner, "prime-successor-descriptor", size=1)

    def compose(
        self, before: PrimeSuccessorActionID, after: PrimeSuccessorActionID
    ) -> PrimeSuccessorActionID:
        """Chronologically compose ``before`` and then ``after``."""
        left, right = self.node(before), self.node(after)
        self.rank.charge()
        if left.identity:
            return after
        if right.identity:
            return before
        copies = left.copies + right.copies
        try:
            return self._normal_forms[copies]
        except KeyError:
            pass
        self._check_budget(2)
        action = self._append_node(
            PrimeSuccessorActionNode(
                copies,
                (left.phase_shift + right.phase_shift) % self.descriptor.fresh_prime,
                before,
                after,
            )
        )
        self._normal_forms[copies] = action
        return action

    def power(self, copies: int) -> PrimeSuccessorActionID:
        """Build a binary-composed action without replaying parent periods."""
        self._check_open()
        if type(copies) is not int or copies < 0:
            raise ValueError("prime successor power must be a nonnegative integer")
        result, power, remaining = self.identity, self.base, copies
        while remaining:
            self.rank.charge()
            if remaining & 1:
                result = self.compose(result, power)
            remaining >>= 1
            if remaining:
                power = self.compose(power, power)
        return result

    def _base_rank(self, entering_phase: int, stop: int) -> int:
        """Survivors in the first ``stop`` offsets of one parent period."""
        W, q = self.descriptor.parent_period, self.descriptor.fresh_prime
        if not 0 <= stop <= W:
            raise ValueError("prime base rank lies outside its parent period")
        depth = len(self.descriptor.parent_factors)
        parent = self.rank.count(stop, depth)
        if entering_phase % q == 0 and self.descriptor.forbidden_residues == (0,):
            # Multiplication by fresh q is the exact ordinary zero-phase
            # deletion bijection.  This is also production's finite-horizon
            # path, and avoids building congruence states it does not need.
            return parent - self.rank.count(stop // q, depth)
        deleted = 0
        for forbidden in self.descriptor.forbidden_residues:
            residue = (forbidden - entering_phase) % q
            deleted += self.rank.count_progression_interval(
                1, stop + 1, q, residue, depth
            )
        return parent - deleted

    def _base_effect(self, entering_phase: int) -> PrimeSuccessorPortEffect:
        W, q = self.descriptor.parent_period, self.descriptor.fresh_prime
        depth = len(self.descriptor.parent_factors)
        parent = prod(factor - 1 for factor in self.descriptor.parent_factors)
        deleted = 0
        for forbidden in self.descriptor.forbidden_residues:
            residue = (forbidden - entering_phase) % q
            deleted += self.rank.count_progression_interval(1, W + 1, q, residue, depth)
        return PrimeSuccessorPortEffect(
            entering_phase,
            (entering_phase + W) % q,
            parent,
            deleted,
            parent - deleted,
        )

    def port_effect(
        self, action: PrimeSuccessorActionID, entering_phase: int
    ) -> PrimeSuccessorPortEffect:
        """Demand exactly one port through an explicit postorder traversal."""
        self._check_open()
        if type(entering_phase) is not int:
            raise TypeError("prime entering phase must be an integer")
        q = self.descriptor.fresh_prime
        phase = entering_phase % q
        root = (action, phase)
        try:
            return self._ports[root]
        except KeyError:
            pass
        stack = [(action, phase, False)]
        while stack:
            action_id, incoming, _ready = stack.pop()
            self.rank.charge()
            key = (action_id, incoming)
            if key in self._ports:
                continue
            node = self.node(action_id)
            if node.identity:
                effect = PrimeSuccessorPortEffect(incoming, incoming, 0, 0, 0)
            elif node.primitive:
                effect = self._base_effect(incoming)
            else:
                if node.before is None or node.after is None:
                    raise RuntimeError("composed prime action lost its children")
                before_key = (node.before, incoming)
                if before_key not in self._ports:
                    stack.append((action_id, incoming, True))
                    stack.append((node.before, incoming, False))
                    continue
                first = self._ports[before_key]
                after_key = (node.after, first.outgoing_phase)
                if after_key not in self._ports:
                    stack.append((action_id, incoming, True))
                    stack.append((node.after, first.outgoing_phase, False))
                    continue
                second = self._ports[after_key]
                effect = PrimeSuccessorPortEffect(
                    incoming,
                    second.outgoing_phase,
                    first.parent_survivors + second.parent_survivors,
                    first.deleted_survivors + second.deleted_survivors,
                    first.surviving_values + second.surviving_values,
                )
            self._check_budget()
            self._ports[key] = effect
        return self._ports[root]

    def rank_before(
        self, action: PrimeSuccessorActionID, entering_phase: int, stop: int
    ) -> int:
        """Count action survivors in the half-open offset prefix ``[0, stop)``."""
        node = self.node(action)
        W = self.descriptor.parent_period
        if type(stop) is not int or not 0 <= stop <= node.copies * W:
            raise ValueError("prime successor rank is outside its action")
        phase = entering_phase % self.descriptor.fresh_prime
        current, remaining, result = action, stop, 0
        while True:
            self.rank.charge()
            current_node = self.node(current)
            if current_node.identity or remaining == 0:
                return result
            if current_node.primitive:
                return result + self._base_rank(phase, remaining)
            if current_node.before is None or current_node.after is None:
                raise RuntimeError("composed prime action lost its children")
            before_node = self.node(current_node.before)
            split = before_node.copies * W
            if remaining <= split:
                current = current_node.before
                continue
            first = self.port_effect(current_node.before, phase)
            result += first.surviving_values
            phase = first.outgoing_phase
            remaining -= split
            current = current_node.after

    def select(
        self, action: PrimeSuccessorActionID, entering_phase: int, rank: int
    ) -> int:
        """Return the zero-based action offset of one surviving value."""
        if type(rank) is not int or rank < 0:
            raise ValueError("prime successor rank must be a nonnegative integer")
        total = self.port_effect(action, entering_phase).surviving_values
        if rank >= total:
            raise IndexError(rank)
        W = self.descriptor.parent_period
        phase = entering_phase % self.descriptor.fresh_prime
        current, offset, remaining_rank = action, 0, rank
        while True:
            self.rank.charge()
            node = self.node(current)
            if node.primitive:
                lo, hi = 1, W
                while lo < hi:
                    self.rank.charge()
                    mid = (lo + hi) // 2
                    if self._base_rank(phase, mid) > remaining_rank:
                        hi = mid
                    else:
                        lo = mid + 1
                return offset + lo - 1
            if node.before is None or node.after is None:
                raise RuntimeError("prime select reached an identity action")
            first = self.port_effect(node.before, phase)
            if remaining_rank < first.surviving_values:
                current = node.before
                continue
            remaining_rank -= first.surviving_values
            offset += self.node(node.before).copies * W
            phase = first.outgoing_phase
            current = node.after

    def metrics(self) -> PrimeSuccessorActionMetrics:
        return PrimeSuccessorActionMetrics(
            len(self._nodes),
            max(0, len(self._normal_forms) - 2),
            len(self._ports),
            len(self.rank.progression_memo),
            self.rank.work,
            self.rank.ledger.entries,
            self.rank.ledger.nodes,
        )

    def close(self) -> None:
        if self._closed:
            return
        self._ports.dispose()
        self._normal_forms.dispose()
        self._nodes.dispose()
        self._closed = True


class PrimeSuccessorImageAdapter(SourceBoundImageAdapter):
    """Connect fresh-prime actions to the shared chronological image owner."""

    family = "prime"
    semantic_version = "successor-wheel-v1"

    def __init__(self, arena: PrimeSuccessorActionArena) -> None:
        if type(arena) is not PrimeSuccessorActionArena:
            raise TypeError("prime image adapter requires its action arena")
        self.arena = arena
        self.ledger = arena.rank.ledger

    def validate_source(self, source: Hashable) -> None:
        if type(source) is not PrimeSuccessorSource:
            raise TypeError("prime successor image requires its exact source")
        try:
            self.arena.validate_descriptor(source.descriptor)
        except (TypeError, ValueError) as error:
            raise ValueError(
                "prime successor source belongs to another descriptor"
            ) from error
        if not 0 <= source.entering_phase < self.arena.descriptor.fresh_prime:
            raise ValueError("prime successor source phase is not canonical")

    def validate_action(self, action: Hashable) -> None:
        if type(action) is not PrimeSuccessorActionID:
            raise TypeError("prime successor image requires a scoped action")
        self.arena.node(action)

    def validate_payload(self, payload: Hashable) -> None:
        if type(payload) is not PrimeSuccessorImagePayload:
            raise TypeError("prime successor image has another payload sort")
        self.arena.validate_descriptor(payload.descriptor)
        self.arena.node(payload.action)
        q = self.arena.descriptor.fresh_prime
        if (
            not 0 <= payload.entering_phase < q
            or not 0 <= payload.outgoing_phase < q
            or min(
                payload.parent_survivors,
                payload.deleted_survivors,
                payload.surviving_values,
            )
            < 0
            or payload.deleted_survivors + payload.surviving_values
            != payload.parent_survivors
        ):
            raise ValueError("invalid prime successor image payload")

    def identity_action(self, source: Hashable) -> PrimeSuccessorActionID:
        self.validate_source(source)
        return self.arena.identity

    def action_children(
        self, action: Hashable
    ) -> tuple[PrimeSuccessorActionID, PrimeSuccessorActionID] | None:
        self.validate_action(action)
        node = self.arena.node(cast(PrimeSuccessorActionID, action))
        if node.before is None or node.after is None:
            return None
        return node.before, node.after

    def compose_actions(
        self, before: Hashable, after: Hashable
    ) -> PrimeSuccessorActionID:
        self.validate_action(before)
        self.validate_action(after)
        return self.arena.compose(
            cast(PrimeSuccessorActionID, before),
            cast(PrimeSuccessorActionID, after),
        )

    def admit_source(self, source: Hashable) -> SourceImageCandidate:
        self.validate_source(source)
        exact_source = cast(PrimeSuccessorSource, source)
        payload = PrimeSuccessorImagePayload(
            self.arena.descriptor_id,
            self.arena.identity,
            exact_source.entering_phase,
            exact_source.entering_phase,
            0,
            0,
            0,
        )
        return SourceImageCandidate(
            payload, 0, (exact_source.entering_phase, exact_source.entering_phase)
        )

    def apply_primitive(
        self, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate:
        self.validate_action(action)
        self.validate_payload(source.payload)
        payload = cast(PrimeSuccessorImagePayload, source.payload)
        exact_action = cast(PrimeSuccessorActionID, action)
        node = self.arena.node(exact_action)
        if not node.identity and not node.primitive:
            raise ValueError("shared scheduler must refine composite prime actions")
        effect = self.arena.port_effect(exact_action, payload.outgoing_phase)
        cumulative = self.arena.compose(payload.action, exact_action)
        result = PrimeSuccessorImagePayload(
            self.arena.descriptor_id,
            cumulative,
            payload.entering_phase,
            effect.outgoing_phase,
            payload.parent_survivors + effect.parent_survivors,
            payload.deleted_survivors + effect.deleted_survivors,
            payload.surviving_values + effect.surviving_values,
        )
        return SourceImageCandidate(
            result,
            source.binding.extent + node.copies * self.arena.descriptor.parent_period,
            (result.entering_phase, result.outgoing_phase),
        )

    def admitted_input_key(
        self, action: Hashable, source: SourceImageView
    ) -> tuple[PrimeSuccessorDescriptorID, int]:
        self.validate_action(action)
        self.validate_payload(source.payload)
        payload = cast(PrimeSuccessorImagePayload, source.payload)
        # The full incoming q-phase is the exact translation state for the
        # homogeneous parent-period action.  No cyclic/count summary replaces it.
        return payload.descriptor, payload.outgoing_phase

    def transport_reuse(
        self,
        action: Hashable,
        cached_source: SourceImageView,
        cached_result: SourceImageView,
        new_source: SourceImageView,
    ) -> SourceImageCandidate:
        self.validate_action(action)
        self.validate_payload(cached_source.payload)
        self.validate_payload(cached_result.payload)
        self.validate_payload(new_source.payload)
        old_source = cast(PrimeSuccessorImagePayload, cached_source.payload)
        old_result = cast(PrimeSuccessorImagePayload, cached_result.payload)
        new = cast(PrimeSuccessorImagePayload, new_source.payload)
        if old_source.outgoing_phase != new.outgoing_phase:
            raise ValueError("prime relative transfer has another incoming phase")
        exact_action = cast(PrimeSuccessorActionID, action)
        cumulative = self.arena.compose(new.action, exact_action)
        result = PrimeSuccessorImagePayload(
            self.arena.descriptor_id,
            cumulative,
            new.entering_phase,
            old_result.outgoing_phase,
            new.parent_survivors
            + old_result.parent_survivors
            - old_source.parent_survivors,
            new.deleted_survivors
            + old_result.deleted_survivors
            - old_source.deleted_survivors,
            new.surviving_values
            + old_result.surviving_values
            - old_source.surviving_values,
        )
        node = self.arena.node(exact_action)
        return SourceImageCandidate(
            result,
            new_source.binding.extent
            + node.copies * self.arena.descriptor.parent_period,
            (result.entering_phase, result.outgoing_phase),
        )

    def compose_chronological(
        self,
        action: Hashable,
        source: SourceImageView,
        before: SourceImageView,
        after: SourceImageView,
    ) -> SourceImageCandidate:
        self.validate_action(action)
        self.validate_payload(source.payload)
        self.validate_payload(before.payload)
        self.validate_payload(after.payload)
        source_payload = cast(PrimeSuccessorImagePayload, source.payload)
        after_payload = cast(PrimeSuccessorImagePayload, after.payload)
        effect = self.arena.port_effect(
            cast(PrimeSuccessorActionID, action), source_payload.outgoing_phase
        )
        if (
            after_payload.parent_survivors - source_payload.parent_survivors
            != effect.parent_survivors
            or after_payload.deleted_survivors - source_payload.deleted_survivors
            != effect.deleted_survivors
            or after_payload.surviving_values - source_payload.surviving_values
            != effect.surviving_values
        ):
            raise ValueError("prime chronological image disagrees with its action")
        return SourceImageCandidate(
            after_payload,
            after.binding.extent,
            (after_payload.entering_phase, after_payload.outgoing_phase),
        )

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
        self.validate_payload(image.payload)
        payload = cast(PrimeSuccessorImagePayload, image.payload)
        if demand.name == "effect" and not demand.parameters:
            return SourceImageProjection(
                self.arena.port_effect(payload.action, payload.entering_phase)
            )
        if demand.name == "rank-before" and len(demand.parameters) == 1:
            stop = demand.parameters[0]
            if type(stop) is not int:
                raise TypeError("prime rank demand must contain an integer stop")
            return SourceImageProjection(
                self.arena.rank_before(payload.action, payload.entering_phase, stop)
            )
        if demand.name == "select" and len(demand.parameters) == 1:
            rank = demand.parameters[0]
            if type(rank) is not int:
                raise TypeError("prime select demand must contain an integer rank")
            return SourceImageProjection(
                self.arena.select(payload.action, payload.entering_phase, rank)
            )
        raise ValueError("unsupported prime successor image demand")

    def first_failure(self, image: SourceImageView) -> None:
        self.validate_payload(image.payload)


__all__ = [
    "PrimeSuccessorActionArena",
    "PrimeSuccessorActionDescriptor",
    "PrimeSuccessorActionID",
    "PrimeSuccessorActionMetrics",
    "PrimeSuccessorActionNode",
    "PrimeSuccessorDescriptorID",
    "PrimeSuccessorImageAdapter",
    "PrimeSuccessorImagePayload",
    "PrimeSuccessorPortEffect",
    "PrimeSuccessorSource",
]
