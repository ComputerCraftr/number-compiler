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
    width: int
    phase_shift: int
    before: PrimeSuccessorActionID | None
    after: PrimeSuccessorActionID | None

    @property
    def primitive(self) -> bool:
        return self.width > 0 and self.before is None and self.after is None

    @property
    def identity(self) -> bool:
        return self.width == 0


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
        parent_depth: int | None = None,
        forbidden_residues: tuple[int, ...] = (0,),
        max_action_entries: int | None = None,
    ) -> None:
        if type(fresh_prime) is not int or fresh_prime < 2:
            raise ValueError("fresh prime must be an integer >= 2")
        factors = rank.primes
        if parent_depth is None:
            if not factors or fresh_prime <= rank.last_factor:
                raise ValueError("fresh prime must follow a nonempty parent prefix")
            parent_depth = len(factors)
            rank.validate_fresh_successor(fresh_prime)
            admitted_successor = False
        elif (
            type(parent_depth) is not int
            or not 0 <= parent_depth < len(factors)
            or factors[parent_depth] != fresh_prime
        ):
            raise ValueError("fresh prime must be the admitted successor stage")
        else:
            rank.validate_consecutive_prefix(parent_depth + 1)
            admitted_successor = True
        if max_action_entries is not None and (
            type(max_action_entries) is not int or max_action_entries < 4
        ):
            raise ValueError("prime action budget must be at least four entries")
        raw_forbidden = tuple(forbidden_residues)
        if not raw_forbidden or any(type(value) is not int for value in raw_forbidden):
            raise ValueError("fresh-prime forbidden residues must be integers")
        q = fresh_prime
        forbidden = tuple(sorted({value % q for value in raw_forbidden}))
        self.rank = rank
        self._rank_authority = rank, rank.ledger, rank._factor_store_authority
        # Constructor admission checked this immutable prefix. Later arena
        # publications mutate unrelated stores, not the factor authority.
        self._prefix_stamp = rank._factor_store_authority.mutation_stamp
        self._parent_depth = parent_depth
        self._admitted_successor = admitted_successor
        self._owner = ArenaToken("prime-successor-actions")
        self.descriptor = PrimeSuccessorActionDescriptor(
            factors[:parent_depth], prod(factors[:parent_depth]), q, forbidden
        )
        self._descriptor_authority = (
            self.descriptor,
            self.descriptor.parent_factors,
            self.descriptor.parent_period,
            self.descriptor.fresh_prime,
            self.descriptor.forbidden_residues,
        )
        self.descriptor_id = PrimeSuccessorDescriptorID(
            self._owner, "prime-successor-descriptor", 0
        )
        self.max_action_entries = max_action_entries
        ledger = rank.ledger
        prefix = f"prime.successor-{ledger.owner_count}"
        node_owner = ledger.register(
            prefix + ".nodes", "fresh-prime chronological action nodes"
        )
        composition_owner = ledger.register(
            prefix + ".normal-forms", "fresh-prime action normal forms"
        )
        port_owner = ledger.register(
            prefix + ".ports", "demanded fresh-prime port effects"
        )
        nodes: OwnedMemo[int, PrimeSuccessorActionNode] | None = None
        normal_forms: OwnedMemo[int, PrimeSuccessorActionID] | None = None
        ports: (
            OwnedMemo[tuple[PrimeSuccessorActionID, int], PrimeSuccessorPortEffect]
            | None
        ) = None
        try:
            nodes = OwnedMemo(ledger, node_owner, nodes_per_entry=1)
            normal_forms = OwnedMemo(
                ledger, composition_owner, composition_entries=True
            )
            ports = OwnedMemo(ledger, port_owner)
            self._nodes = nodes
            self._normal_forms = normal_forms
            self._ports = ports
            self._next_node = 0
            self._closed = False
            self._check_budget(4)
            self.identity = self._append_node(
                PrimeSuccessorActionNode(0, 0, 0, None, None)
            )
            self.base = self._append_node(
                PrimeSuccessorActionNode(
                    1,
                    self.descriptor.parent_period,
                    self.descriptor.parent_period % q,
                    None,
                    None,
                )
            )
            self._normal_forms[0] = self.identity
            self._normal_forms[self.descriptor.parent_period] = self.base
        except BaseException:
            for memo in (ports, normal_forms, nodes):
                if memo is not None:
                    memo.dispose()
            self._closed = True
            raise

    def _check_open(self) -> None:
        if self._closed:
            raise RuntimeError("prime successor action arena is closed")
        descriptor, parent, period, fresh, forbidden = self._descriptor_authority
        if self.descriptor is not descriptor or (
            descriptor.parent_factors,
            descriptor.parent_period,
            descriptor.fresh_prime,
            descriptor.forbidden_residues,
        ) != (parent, period, fresh, forbidden):
            raise ValueError("prime successor descriptor lost its source authority")
        rank, ledger, factors = self._rank_authority
        if (
            self.rank is not rank
            or self.rank.ledger is not ledger
            or self.rank._factor_store_authority is not factors
        ):
            raise ValueError("prime successor action lost its source authority")
        try:
            stamp = factors.mutation_stamp
        except (AttributeError, TypeError) as error:
            raise ValueError(
                "prime successor action lost its source authority"
            ) from error
        if not factors.append_only:
            raise ValueError("prime successor action lost its append-only authority")
        if stamp == self._prefix_stamp:
            return
        self.rank.validate_bound_factor_prefix(
            self.descriptor.parent_factors,
            self.descriptor.fresh_prime if self._admitted_successor else None,
        )
        self._prefix_stamp = stamp

    def _check_budget(self, additional: int = 1) -> None:
        retained = len(self._nodes) + len(self._normal_forms) + len(self._ports)
        request_retained = self.rank.ledger.entries - self.rank.factor_count
        if (
            self.rank.max_states is not None
            and request_retained + additional > self.rank.max_states
        ):
            raise ValueError("prime state budget exceeded (--max-prime-states)")
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
        width = left.width + right.width
        try:
            return self._normal_forms[width]
        except KeyError:
            pass
        self._check_budget(2)
        W = self.descriptor.parent_period
        action = self._append_node(
            PrimeSuccessorActionNode(
                width // W if width % W == 0 else -1,
                width,
                (left.phase_shift + right.phase_shift) % self.descriptor.fresh_prime,
                before,
                after,
            )
        )
        self._normal_forms[width] = action
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

    def prefix(self, width: int) -> PrimeSuccessorActionID:
        """Build a binary admitted integer prefix without enumerating its leaves."""
        self._check_open()
        if type(width) is not int or width < 0:
            raise ValueError("prime successor prefix width must be nonnegative")
        found = self._normal_forms.get(width)
        if found is not None:
            return found
        unit = self._normal_forms.get(1)
        if unit is None:
            self._check_budget(2)
            unit = self._append_node(
                PrimeSuccessorActionNode(
                    -1,
                    1,
                    1 % self.descriptor.fresh_prime,
                    None,
                    None,
                )
            )
            self._normal_forms[1] = unit
        result, power, remaining = self.identity, unit, width
        while remaining:
            self.rank.charge()
            if remaining & 1:
                result = self.compose(result, power)
            remaining >>= 1
            if remaining:
                power = self.compose(power, power)
        return result

    def _interval_effect(
        self, start: int, width: int, entering_phase: int
    ) -> PrimeSuccessorPortEffect:
        q = self.descriptor.fresh_prime
        phase = entering_phase % q
        depth = len(self.descriptor.parent_factors)
        parent = self.rank.count(start + width, depth) - self.rank.count(start, depth)
        if phase == start % q and self.descriptor.forbidden_residues == (0,):
            deleted = self.rank.count((start + width) // q, depth) - self.rank.count(
                start // q, depth
            )
            return PrimeSuccessorPortEffect(
                phase,
                (phase + width) % q,
                parent,
                deleted,
                parent - deleted,
            )
        deleted = 0
        for forbidden in self.descriptor.forbidden_residues:
            residue = (start + forbidden - phase) % q
            deleted += self.rank.count_progression_interval(
                start + 1, start + width + 1, q, residue, depth
            )
        return PrimeSuccessorPortEffect(
            phase,
            (phase + width) % q,
            parent,
            deleted,
            parent - deleted,
        )

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
        phase = entering_phase % q
        if phase == 0 and self.descriptor.forbidden_residues == (0,):
            surviving = self.rank.count(W, depth) - self.rank.count(W // q, depth)
            return PrimeSuccessorPortEffect(
                phase,
                W % q,
                parent,
                parent - surviving,
                surviving,
            )
        deleted = 0
        for forbidden in self.descriptor.forbidden_residues:
            residue = (forbidden - phase) % q
            deleted += self.rank.count_progression_interval(1, W + 1, q, residue, depth)
        return PrimeSuccessorPortEffect(
            phase,
            (phase + W) % q,
            parent,
            deleted,
            parent - deleted,
        )

    def _period_aligned_split(self, node: PrimeSuccessorActionNode) -> bool:
        """Whether the second child starts on the parent's wheel seam.

        A whole-period extent does not imply that its binary children split
        on a period seam. Off-seam intervals need the progression count owner;
        transporting only the fresh-prime phase would lose the parent offset.
        """
        if node.width % self.descriptor.parent_period:
            return False
        if node.before is None:
            return True
        return self.node(node.before).width % self.descriptor.parent_period == 0

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
        root_node = self.node(action)
        if not self._period_aligned_split(root_node):
            self._check_budget()
            self._ports[root] = self._interval_effect(0, root_node.width, phase)
            return self._ports[root]
        stack = [(action, phase, False)]
        while stack:
            action_id, incoming, _ready = stack.pop()
            self.rank.charge()
            key = (action_id, incoming)
            if key in self._ports:
                continue
            node = self.node(action_id)
            if not self._period_aligned_split(node):
                effect = self._interval_effect(0, node.width, incoming)
            elif node.identity:
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
        if type(stop) is not int or not 0 <= stop <= node.width:
            raise ValueError("prime successor rank is outside its action")
        phase = entering_phase % self.descriptor.fresh_prime
        if phase == 0 and self.descriptor.forbidden_residues == (0,):
            depth = len(self.descriptor.parent_factors)
            q = self.descriptor.fresh_prime
            return self.rank.count(stop, depth) - self.rank.count(stop // q, depth)
        if not self._period_aligned_split(node):
            return self._interval_effect(0, stop, phase).surviving_values
        current, remaining, result = action, stop, 0
        while True:
            self.rank.charge()
            current_node = self.node(current)
            if current_node.identity or remaining == 0:
                return result
            if not self._period_aligned_split(current_node):
                return (
                    result + self._interval_effect(0, remaining, phase).surviving_values
                )
            if current_node.primitive:
                return result + self._base_rank(phase, remaining)
            if current_node.before is None or current_node.after is None:
                raise RuntimeError("composed prime action lost its children")
            before_node = self.node(current_node.before)
            split = before_node.width
            if remaining <= split:
                current = current_node.before
                continue
            first = self.port_effect(current_node.before, phase)
            result += first.surviving_values
            phase = first.outgoing_phase
            remaining -= split
            current = current_node.after

    def _select_interval(
        self, action: PrimeSuccessorActionID, phase: int, rank: int
    ) -> int:
        """Descend exact interval ranks where a binary edge crosses a seam."""
        lo, hi = 1, self.node(action).width
        while lo < hi:
            self.rank.charge()
            mid = (lo + hi) // 2
            if self.rank_before(action, phase, mid) > rank:
                hi = mid
            else:
                lo = mid + 1
        return lo - 1

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
        root_node = self.node(action)
        if not self._period_aligned_split(root_node):
            return self._select_interval(action, entering_phase, rank)
        phase = entering_phase % self.descriptor.fresh_prime
        current, offset, remaining_rank = action, 0, rank
        while True:
            self.rank.charge()
            node = self.node(current)
            if not self._period_aligned_split(node):
                return offset + self._select_interval(current, phase, remaining_rank)
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
            offset += self.node(node.before).width
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
    semantic_version = "successor-wheel-v2"

    def __init__(self, arena: PrimeSuccessorActionArena) -> None:
        if type(arena) is not PrimeSuccessorActionArena:
            raise TypeError("prime image adapter requires its action arena")
        self.arena = arena
        self.ledger = arena.rank.ledger

    def _charge(self) -> None:
        self.arena._check_open()
        self.arena.rank.charge()
        self.ledger.bump("prime_successor_scheduler_work")

    def _check_capacity(self, additional: int) -> None:
        maximum = self.arena.rank.max_states
        retained = self.ledger.entries - self.arena.rank.factor_count
        if maximum is not None and retained + additional > maximum:
            raise ValueError("prime state budget exceeded (--max-prime-states)")

    def validate_source(self, source: Hashable) -> None:
        self._charge()
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
        self._charge()
        if type(action) is not PrimeSuccessorActionID:
            raise TypeError("prime successor image requires a scoped action")
        self.arena.node(action)

    def validate_payload(self, payload: Hashable) -> None:
        self._charge()
        if type(payload) is not PrimeSuccessorImagePayload:
            raise TypeError("prime successor image has another payload sort")
        self.arena.validate_descriptor(payload.descriptor)
        node = self.arena.node(payload.action)
        q = self.arena.descriptor.fresh_prime
        if (
            any(
                type(value) is not int
                for value in (
                    payload.entering_phase,
                    payload.outgoing_phase,
                    payload.parent_survivors,
                    payload.deleted_survivors,
                    payload.surviving_values,
                )
            )
            or not 0 <= payload.entering_phase < q
            or not 0 <= payload.outgoing_phase < q
            or payload.outgoing_phase != (payload.entering_phase + node.width) % q
            or payload.parent_survivors > node.width
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
        self._check_capacity(3)
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
        if (
            node.width == self.arena.descriptor.parent_period
            and source.binding.extent % self.arena.descriptor.parent_period == 0
        ):
            effect = self.arena.port_effect(exact_action, payload.outgoing_phase)
        else:
            effect = self.arena._interval_effect(
                source.binding.extent, node.width, payload.outgoing_phase
            )
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
        if node.primitive:
            self.ledger.bump("prime_partial_successor_filters")
        self._check_capacity(4)
        return SourceImageCandidate(
            result,
            source.binding.extent + node.width,
            (result.entering_phase, result.outgoing_phase),
        )

    def apply_composite(
        self,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None:
        """Admit the exact zero-phase fresh-prime specialization as one image."""
        self.validate_action(action)
        self.validate_payload(source.payload)
        payload = cast(PrimeSuccessorImagePayload, source.payload)
        exact_action = cast(PrimeSuccessorActionID, action)
        node = self.arena.node(exact_action)
        if (
            demand is None
            or node.primitive
            or node.identity
            or payload.outgoing_phase != 0
            or self.arena.descriptor.forbidden_residues != (0,)
            or demand.name != "rank-before"
            or len(demand.parameters) != 1
        ):
            return None
        width = node.width
        effect = self.arena._interval_effect(
            source.binding.extent, width, payload.outgoing_phase
        )
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
        self.ledger.bump("prime_partial_successor_filters")
        self._check_capacity(4)
        return SourceImageCandidate(
            result,
            source.binding.extent + width,
            (result.entering_phase, result.outgoing_phase),
        )

    def admitted_input_key(
        self, action: Hashable, source: SourceImageView
    ) -> tuple[PrimeSuccessorDescriptorID, int, int]:
        self.validate_action(action)
        self.validate_payload(source.payload)
        payload = cast(PrimeSuccessorImagePayload, source.payload)
        # Arbitrary admitted prefixes need both translation coordinates.  Equal
        # fresh-prime phase alone does not determine which parent-wheel slots
        # survive when the source extent is not parent-period aligned.
        return (
            payload.descriptor,
            payload.outgoing_phase,
            source.binding.extent % self.arena.descriptor.parent_period,
        )

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
        parent_period = self.arena.descriptor.parent_period
        if (
            old_source.outgoing_phase != new.outgoing_phase
            or cached_source.binding.extent % parent_period
            != new_source.binding.extent % parent_period
        ):
            raise ValueError("prime relative transfer has another incoming state")
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
        self._check_capacity(3)
        return SourceImageCandidate(
            result,
            new_source.binding.extent + node.width,
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
        exact_action = cast(PrimeSuccessorActionID, action)
        node = self.arena.node(exact_action)
        if source.binding.extent % self.arena.descriptor.parent_period:
            effect = self.arena._interval_effect(
                source.binding.extent, node.width, source_payload.outgoing_phase
            )
        else:
            effect = self.arena.port_effect(exact_action, source_payload.outgoing_phase)
        if (
            after.binding.extent != source.binding.extent + node.width
            or after_payload.outgoing_phase != effect.outgoing_phase
            or after_payload.parent_survivors - source_payload.parent_survivors
            != effect.parent_survivors
            or after_payload.deleted_survivors - source_payload.deleted_survivors
            != effect.deleted_survivors
            or after_payload.surviving_values - source_payload.surviving_values
            != effect.surviving_values
        ):
            raise ValueError("prime chronological image disagrees with its action")
        self._check_capacity(4)
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
            self._check_capacity(2)
            self.ledger.bump("prime_successor_image_effect_projections")
            return SourceImageProjection(
                PrimeSuccessorPortEffect(
                    payload.entering_phase,
                    payload.outgoing_phase,
                    payload.parent_survivors,
                    payload.deleted_survivors,
                    payload.surviving_values,
                )
            )
        if demand.name == "rank-before" and len(demand.parameters) == 1:
            stop = demand.parameters[0]
            if type(stop) is not int:
                raise TypeError("prime rank demand must contain an integer stop")
            self._check_capacity(2)
            # The scheduler authenticates this image's publication before
            # calling the adapter. Its whole-extent rank is already part of
            # the admitted support; only interior queries need count descent.
            width = self.arena.node(payload.action).width
            if stop == 0 or stop == width:
                self.ledger.bump("prime_successor_image_endpoint_rank_projections")
                return SourceImageProjection(
                    0 if stop == 0 else payload.surviving_values
                )
            return SourceImageProjection(
                self.arena.rank_before(payload.action, payload.entering_phase, stop)
            )
        if demand.name == "select" and len(demand.parameters) == 1:
            rank = demand.parameters[0]
            if type(rank) is not int:
                raise TypeError("prime select demand must contain an integer rank")
            self._check_capacity(2)
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
