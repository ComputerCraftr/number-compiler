"""Lazy fresh-prime wheel actions over a descriptor-only parent period.

One parent period ``W`` is a ``q``-port action.  At incoming phase ``a`` it
keeps the parent-wheel survivors ``x in [1,W]`` except those for which
``x+a`` lies in a requested forbidden class modulo the fresh prime ``q``.
Ports, descendants, and ranks are evaluated on demand; neither the parent gap
cycle nor a ``q``-entry port table is retained.
"""

from __future__ import annotations

from collections.abc import Mapping
from math import prod
from typing import cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
from number_compiler.sequences.prime.successor_action_contracts import (
    PrimeSuccessorActionAuditSnapshot,
    PrimeSuccessorActionDescriptor,
    PrimeSuccessorActionID,
    PrimeSuccessorActionMetrics,
    PrimeSuccessorActionNode,
    PrimeSuccessorDescriptorID,
    PrimeSuccessorPortEffect,
)


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
        factor_source = rank.factor_source_identity()
        self._rank_authority = rank, rank.ledger, factor_source
        # Constructor admission checked this immutable prefix. Later arena
        # publications mutate unrelated stores, not the factor authority.
        self._prefix_stamp = factor_source.mutation_stamp
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
        self._registered_node_owner = node_owner
        self._registered_normal_form_owner = composition_owner
        self._registered_port_owner = port_owner
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
            self._audit_nodes = nodes.audit_snapshot().container
            self._audit_normal_forms = normal_forms.audit_snapshot().container
            self._audit_ports = ports.audit_snapshot().container
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
            from number_compiler.sequences.prime.payload_audit import (
                register_prime_action_audit,
            )

            register_prime_action_audit(self)
        except BaseException:
            for memo in (ports, normal_forms, nodes):
                if memo is not None:
                    memo.dispose()
            self._closed = True
            raise

    def check_open(self) -> None:
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
        rank, ledger, source_identity = self._rank_authority
        if self.rank is not rank or self.rank.ledger is not ledger:
            raise ValueError("prime successor action lost its source authority")
        try:
            stamp = self.rank.factor_source_mutation_stamp(source_identity)
        except (TypeError, ValueError) as error:
            raise ValueError(
                "prime successor action lost its source authority"
            ) from error
        if stamp == self._prefix_stamp:
            return
        self.rank.validate_bound_factor_prefix(
            self.descriptor.parent_factors,
            self.descriptor.fresh_prime if self._admitted_successor else None,
        )
        self._prefix_stamp = stamp

    def validate_open(self) -> None:
        """Validate source and lifecycle authority for a shared adapter."""
        self.check_open()

    def audit_snapshot(self) -> PrimeSuccessorActionAuditSnapshot:
        """Return fresh immutable rows and exact backing-identity evidence."""
        rank: object = self.rank
        rank_ledger: object = None
        if type(rank) is CoprimeRankDAG:
            rank_ledger = rank.ledger
        authority = self._rank_authority
        factor_source: object = None
        recorded_ledger: object = None
        if type(authority) is tuple and len(authority) == 3:
            recorded_ledger, factor_source = authority[1], authority[2]
        if (
            type(self._nodes) is not OwnedMemo
            or type(self._normal_forms) is not OwnedMemo
            or type(self._ports) is not OwnedMemo
        ):
            return PrimeSuccessorActionAuditSnapshot(
                rank_ledger,
                rank,
                recorded_ledger,
                factor_source,
                authority,
                self.descriptor,
                self._descriptor_authority,
                self._parent_depth,
                self._admitted_successor,
                self.descriptor_id,
                self._closed,
                False,
                self._registered_node_owner,
                self._registered_normal_form_owner,
                self._registered_port_owner,
                (),
                (),
                (),
                self._next_node,
                self.identity,
                self.base,
            )
        nodes = self._nodes.audit_snapshot()
        normal_forms = self._normal_forms.audit_snapshot()
        ports = self._ports.audit_snapshot()
        stores_valid = (
            self._audit_nodes is nodes.container
            and self._audit_normal_forms is normal_forms.container
            and self._audit_ports is ports.container
            and nodes.ledger is rank_ledger
            and normal_forms.ledger is rank_ledger
            and ports.ledger is rank_ledger
            and nodes.owner == self._registered_node_owner
            and normal_forms.owner == self._registered_normal_form_owner
            and ports.owner == self._registered_port_owner
        )
        return PrimeSuccessorActionAuditSnapshot(
            rank_ledger,
            rank,
            recorded_ledger,
            factor_source,
            authority,
            self.descriptor,
            self._descriptor_authority,
            self._parent_depth,
            self._admitted_successor,
            self.descriptor_id,
            self._closed,
            stores_valid,
            self._registered_node_owner,
            self._registered_normal_form_owner,
            self._registered_port_owner,
            tuple(
                cast(Mapping[int, PrimeSuccessorActionNode], nodes.container).items()
            ),
            tuple(
                cast(
                    Mapping[int, PrimeSuccessorActionID], normal_forms.container
                ).items()
            ),
            tuple(
                cast(
                    Mapping[
                        tuple[PrimeSuccessorActionID, int], PrimeSuccessorPortEffect
                    ],
                    ports.container,
                ).items()
            ),
            self._next_node,
            self.identity,
            self.base,
        )

    def validate_action_handle(
        self, action: PrimeSuccessorActionID, *, size: int
    ) -> None:
        """Check an action handle against this arena without exposing its token."""
        if type(action) is not PrimeSuccessorActionID:
            raise TypeError("expected a prime successor action ID")
        action.validate(self._owner, "prime-successor-action", size=size)

    def audit_action_node(
        self, action: PrimeSuccessorActionID
    ) -> PrimeSuccessorActionNode | None:
        """Resolve one canonical action for read-only image auditing."""
        if self._closed or type(action) is not PrimeSuccessorActionID:
            return None
        try:
            action.validate(
                self._owner, "prime-successor-action", size=len(self._nodes)
            )
            node = self._nodes[action.local_id]
        except (KeyError, TypeError, ValueError, IndexError):
            return None
        if (
            type(node) is not PrimeSuccessorActionNode
            or self._normal_forms.get(node.width) is not action
        ):
            return None
        return node

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
        self.check_open()
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

    def _charged_power(
        self, power: PrimeSuccessorActionID, remaining: int
    ) -> PrimeSuccessorActionID:
        result = self.identity
        while remaining:
            self.rank.charge()
            if remaining & 1:
                result = self.compose(result, power)
            remaining >>= 1
            if remaining:
                power = self.compose(power, power)
        return result

    def power(self, copies: int) -> PrimeSuccessorActionID:
        """Build a binary-composed action without replaying parent periods."""
        self.check_open()
        if type(copies) is not int or copies < 0:
            raise ValueError("prime successor power must be a nonnegative integer")
        return self._charged_power(self.base, copies)

    def prefix(self, width: int) -> PrimeSuccessorActionID:
        """Build a binary admitted integer prefix without enumerating its leaves."""
        self.check_open()
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
        return self._charged_power(unit, width)

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

    def interval_effect(
        self, start: int, width: int, phase: int
    ) -> PrimeSuccessorPortEffect:
        """Public checked interval evaluator for source-image adapters."""
        self.check_open()
        return self._interval_effect(start, width, phase)

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
        self.check_open()
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
        self.rank.ledger.remove_payload_audit_contract(self, "prime")
        self._ports.dispose()
        self._normal_forms.dispose()
        self._nodes.dispose()
        self._closed = True


__all__ = ["PrimeSuccessorActionArena"]
