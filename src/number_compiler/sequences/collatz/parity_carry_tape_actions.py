"""Ledger-accounted AVL tape actions and incremental construction.

All retained and transient *tape* objects belong to one query ledger. This
module does not certify full guarded source/bridge joins: those transactions
must separately account for the CRT, digit bridges and affine seam buffers.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Self

from number_compiler.resources.reference_delta import TemporaryRootLease
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.parity_carry_tape import (
    ParityCarryTape,
    prefix_units_scratch_envelope,
)

_TEMPORARY_ROOT_LEASE_NODE_CHARGE = 16

if TYPE_CHECKING:
    from number_compiler.resources.ledger import (
        LedgerReservation,
        OwnedMemo,
        ResourceLedger,
    )
    from number_compiler.sequences.collatz.guarded_port_join import GuardedPortJoin
    from number_compiler.sequences.collatz.named_border_carry_matrix import (
        UnitsCarryMatrix,
    )
    from number_compiler.sequences.collatz.parity_carry_tape_retention import (
        ParityCarryTapeRetention,
    )


class LedgeredParityTapeActions:
    """Explicitly owned reusable affine summaries of an immutable parity DAG.

    Each retained memo row holds the *actual* node and its authenticated action.
    The dynamic charge includes the node, structural references, the action
    header and all seven unbounded coefficients (charged by their limb sizes).
    A temporary ledger reservation is acquired before each arithmetic step;
    its retained portion is transferred into OwnedMemo only after validation.
    This is a tape-action owner, not a globally resource-certified port join:
    source/bridge creation belongs to a separate transaction.
    """

    __slots__ = (
        "__weakref__",
        "ledger",
        "owner",
        "scratch_owner",
        "_actions",
        "_closed",
        "_failed",
        "compositions",
        "cache_hits",
        "edge_visits",
        "discovery_edge_visits",
        "published_edge_references",
        "retirement_node_visits",
        "retirement_edge_visits",
        "_live",
        "_root",
        "_live_owner",
        "_plan_owner",
        "_lease_owner",
        "_join_owner",
        "_retained_records",
    )

    def __init__(self, ledger: ResourceLedger) -> None:
        from number_compiler.resources.ledger import OwnedMemo, ResourceLedger

        if type(ledger) is not ResourceLedger:
            raise TypeError("parity tape cache requires its exact query ledger")
        self.ledger = ledger
        self._closed = False
        self._failed = False
        self.compositions = 0
        self.cache_hits = 0
        self.edge_visits = 0
        self.discovery_edge_visits = 0
        self.published_edge_references = 0
        self.retirement_node_visits = 0
        self.retirement_edge_visits = 0
        prefix = f"collatz-parity-slp-{ledger.owner_count}"
        owner_names = (
            prefix + "-actions",
            prefix + "-references",
            prefix + "-scratch",
            prefix + "-root-plan",
            prefix + "-root-leases",
            prefix + "-joined-ports",
        )
        ledger.require_fresh_owner_names(owner_names)
        self.owner = -1
        self._live_owner = -1
        self.scratch_owner = -1
        self._plan_owner = -1
        self._lease_owner = -1
        self._join_owner = -1
        self._root: ParityCarryTape | None = None
        self._retained_records: ParityCarryTapeRetention | None = None
        self._actions: (
            OwnedMemo[int, tuple[ParityCarryTape, DyadicTerminalFieldAction]] | None
        ) = None
        self._live: OwnedMemo[int, tuple[ParityCarryTape, int]] | None = None
        registered: list[int] = []
        try:
            self.owner = ledger.register(owner_names[0], "query_memo")
            registered.append(self.owner)
            self._live_owner = ledger.register(owner_names[1], "action_program")
            registered.append(self._live_owner)
            self.scratch_owner = ledger.register(owner_names[2], "execution_stack")
            registered.append(self.scratch_owner)
            self._plan_owner = ledger.register(owner_names[3], "execution_stack")
            registered.append(self._plan_owner)
            self._lease_owner = ledger.register(owner_names[4], "query_memo")
            registered.append(self._lease_owner)
            self._join_owner = ledger.register(owner_names[5], "query_memo")
            registered.append(self._join_owner)
            from number_compiler.sequences.collatz.parity_carry_tape_retention import (
                ParityCarryTapeRetention,
                parity_action_node_cost,
            )

            self._retained_records = ParityCarryTapeRetention(
                ledger, self._lease_owner, self._join_owner
            )
            self._actions = OwnedMemo(
                ledger, self.owner, node_cost=parity_action_node_cost
            )
            self._live = OwnedMemo(ledger, self._live_owner, nodes_per_entry=4)
            ledger.register_execution_root(self)
        except BaseException:
            from number_compiler.resources.lifecycle import cleanup_all

            cleanups = (
                tuple(
                    memo.dispose
                    for memo in (self._actions, self._live)
                    if memo is not None
                )
                + (
                    ()
                    if self._retained_records is None
                    else (self._retained_records.dispose,)
                )
                + tuple(
                    lambda owner=owner: ledger.retire_unpublished_owner(owner)
                    for owner in reversed(registered)
                )
            )
            cleanup_all(cleanups)
            raise

    @staticmethod
    def _construction_bound(node: ParityCarryTape) -> int:
        # Upper bound in 64-bit ledger units for the affine fields and
        # temporary multiply/add operands, including intermediate powers.
        # Coefficients of an s-step word have O(s) bits. For a repeated
        # block, s is the *expanded* extent, so huge unmaterializable powers
        # are refused by finite node budgets before computing their integers.
        s = node.steps
        o = node.odds
        # At most 12 simultaneous coefficients/intermediates of <=
        # 4*(s+2*o+8) bits; charge 64-bit words, with a fixed header budget.
        # The SLP word tuple can retain one Python integer object per input
        # letter. Reserve those objects explicitly; the affine bound below
        # accounts only for the action coefficients and arithmetic scratch.
        word_nodes = 4 * len(node.word)
        return word_nodes + 160 + 12 * ((4 * (s + 2 * o + 8) + 63) // 64)

    def _check(self) -> None:
        if self._closed:
            raise RuntimeError("disposed parity tape action owner")
        if self._failed:
            raise RuntimeError("failed parity tape action owner is unusable")
        if any(
            owner < 0
            for owner in (
                self.owner,
                self._live_owner,
                self.scratch_owner,
                self._plan_owner,
                self._lease_owner,
                self._join_owner,
            )
        ):
            raise RuntimeError("parity tape action owner was not fully initialized")
        if any(
            self.ledger.account_status(owner).disposed
            for owner in (
                self.owner,
                self._live_owner,
                self.scratch_owner,
                self._plan_owner,
                self._lease_owner,
                self._join_owner,
            )
        ):
            self._failed = True
            raise RuntimeError(
                "parity tape action owner has been revoked by its ledger"
            )
        if (
            self._actions is None
            or self._live is None
            or self._retained_records is None
        ):
            raise RuntimeError("parity tape action stores are unavailable")

    def __enter__(self) -> Self:
        self._check()
        return self

    def __exit__(self, *_args: object) -> None:
        self.dispose()

    def dispose(self) -> None:
        if self._closed:
            return
        from number_compiler.resources.lifecycle import cleanup_all

        assert (
            self._actions is not None
            and self._live is not None
            and self._retained_records is not None
        )
        try:
            cleanup_all(
                (
                    self._retained_records.dispose,
                    self._actions.dispose,
                    self._live.dispose,
                )
            )
            if not self.ledger.account_status(self._plan_owner).disposed:
                entries, nodes = self.ledger.account_usage(self._plan_owner)
                if entries or nodes:
                    self.ledger.release(self._plan_owner, entries=entries, nodes=nodes)
                self.ledger.mark_disposed(self._plan_owner)
            if not self.ledger.account_status(self.scratch_owner).disposed:
                self.ledger.mark_disposed(self.scratch_owner)
        except BaseException:
            # Disposal may be retried to finish reclaiming a partially cleared
            # store, but no action lookup is permitted in the meantime.
            self._failed = True
            raise
        self._root = None
        self._closed = True

    @property
    def retained_entries(self) -> int:
        self._check()
        assert self._actions is not None
        return len(self._actions)

    @property
    def live_entries(self) -> int:
        self._check()
        assert self._live is not None
        return len(self._live)

    def is_current_root(self, root: ParityCarryTape | None) -> bool:
        """Check exact root identity, including while auditing a failed owner."""
        return root is self._root

    def fail_closed(self) -> None:
        """Revoke action use after an incomplete transactional cleanup."""
        self._failed = True

    def _transfer_temporary_plan(
        self, reservation: LedgerReservation, nodes: int
    ) -> None:
        if self.ledger.account_usage(self._plan_owner) != (0, 0):
            raise RuntimeError("root delta workspace was not empty")
        try:
            reservation.transfer_to(self._plan_owner, nodes=nodes)
        except BaseException as error:
            try:
                self._release_temporary_plan()
            except BaseException as rollback_error:
                self._failed = True
                raise rollback_error from error
            raise

    def _release_temporary_plan(self) -> None:
        remaining = self.ledger.account_usage(self._plan_owner)[1]
        if remaining:
            self.ledger.release(self._plan_owner, nodes=remaining)

    def temporary_root_pin(
        self, root: ParityCarryTape
    ) -> TemporaryRootLease[ParityCarryTape]:
        """Keep one already-authenticated root alive across a root switch.

        This is a scoped staging primitive for binary SLP composition. The
        cached action row and its existing live reference must be present;
        arbitrary tapes cannot be pinned or used to mint an action.
        """
        from number_compiler.resources.ledger import LedgerReservation
        from number_compiler.resources.reference_delta import (
            plan_root_reference_changes,
        )

        self._check()
        if type(root) is not ParityCarryTape:
            raise TypeError("temporary pin requires an immutable parity tape")
        key = id(root)
        actions, refs = self._actions, self._live
        assert actions is not None and refs is not None
        cached = actions.get(key)
        live = refs.get(key)
        if (
            cached is None
            or cached[0] is not root
            or not cached[1].producer_issued
            or cached[1].steps != root.steps
            or live is None
            or live[0] is not root
            or live[1] < 1
        ):
            raise RuntimeError("temporary pin requires a live authenticated root")

        lease: TemporaryRootLease[ParityCarryTape] | None = None
        lease_charge_held = False
        lease_listed = False
        plan_held = False
        try:
            with LedgerReservation(self.ledger, self.scratch_owner) as reservation:
                reservation.reserve(entries=1, nodes=_TEMPORARY_ROOT_LEASE_NODE_CHARGE)
                lease = TemporaryRootLease(self, root)
                plan = plan_root_reference_changes(
                    (root,),
                    (),
                    lookup=refs.get,
                    children=lambda node: node.children,
                    reservation=reservation,
                )
                plan.validate_current(refs.get)
                if plan.reserved_entries:
                    raise RuntimeError("temporary pin found an uncached reference root")
                self._transfer_temporary_plan(reservation, plan.reserved_nodes)
                plan_held = True
                assert self._retained_records is not None
                self._retained_records.add_lease(lease, reservation)
                lease_charge_held = True
                lease_listed = True
            plan.validate_current(refs.get)
            assert lease is not None
            target = next(change for change in plan.changes if change.key == key)
            if target.before != live[1] or target.after != live[1] + 1:
                raise RuntimeError("temporary root pin plan changed an unexpected row")
            refs[key] = (root, target.after)
            self.ledger.release(self._plan_owner, nodes=plan.reserved_nodes)
            plan_held = False
            self.edge_visits += plan.visited_nodes + plan.visited_edges
            assert lease is not None
            lease.activate()
            return lease
        except BaseException as error:
            try:
                current = refs.get(key)
                if current is not None and current[0] is root:
                    if current[1] == live[1] + 1:
                        refs[key] = live
                    elif current[1] != live[1]:
                        raise RuntimeError(
                            "temporary root pin rollback found a changed row"
                        )
                if plan_held:
                    self._release_temporary_plan()
                if lease_listed and lease is not None:
                    assert self._retained_records is not None
                    self._retained_records.forget_lease(lease)
                    lease_listed = False
                    lease_charge_held = False
                if lease_charge_held:
                    self.ledger.release(
                        self._lease_owner,
                        entries=1,
                        nodes=_TEMPORARY_ROOT_LEASE_NODE_CHARGE,
                    )
                    lease_charge_held = False
            except BaseException as rollback_error:
                self._failed = True
                raise rollback_error from error
            raise

    def release_temporary_root(self, root: ParityCarryTape) -> None:
        from number_compiler.resources.ledger import LedgerReservation
        from number_compiler.resources.reference_delta import (
            plan_root_reference_changes,
        )

        self._check()
        refs = self._live
        assert refs is not None
        key = id(root)
        current = refs.get(key)
        if current is None or current[0] is not root or current[1] < 2:
            raise RuntimeError("temporary parity root no longer has a protected owner")
        plan_held = False
        changed = False
        target_before: int | None = None
        target_after: int | None = None
        try:
            with LedgerReservation(self.ledger, self.scratch_owner) as reservation:
                plan = plan_root_reference_changes(
                    (),
                    (root,),
                    lookup=refs.get,
                    children=lambda node: node.children,
                    reservation=reservation,
                )
                plan.validate_current(refs.get)
                target = next(change for change in plan.changes if change.key == key)
                if target.before != current[1] or target.after != current[1] - 1:
                    raise RuntimeError(
                        "temporary root release plan changed unexpectedly"
                    )
                if target.after < 1:
                    raise RuntimeError(
                        "temporary root release would retire its parent row"
                    )
                target_after = target.after
                target_before = target.before
                self._transfer_temporary_plan(reservation, plan.reserved_nodes)
                plan_held = True
            plan.validate_current(refs.get)
            refs[key] = (root, target.after)
            changed = True
            self.ledger.release(self._plan_owner, nodes=plan.reserved_nodes)
            plan_held = False
            self.edge_visits += plan.visited_nodes + plan.visited_edges
        except BaseException as error:
            try:
                if changed:
                    if target_after is None or target_before is None:
                        raise RuntimeError(
                            "temporary root rollback lost its admitted target count"
                        )
                    latest = refs.get(key)
                    if latest is not None and latest[0] is root:
                        if latest[1] == target_after:
                            refs[key] = (root, target_before)
                        elif latest[1] != target_before:
                            raise RuntimeError(
                                "temporary root release rollback found a changed row"
                            )
                if plan_held:
                    self._release_temporary_plan()
            except BaseException as rollback_error:
                self._failed = True
                raise rollback_error from error
            raise

    def forget_temporary_root_lease(
        self, lease: TemporaryRootLease[ParityCarryTape]
    ) -> None:
        retained = self._retained_records
        if retained is None:
            raise RuntimeError("parity retained-record store is unavailable")
        retained.forget_lease(lease)

    def retain_guarded_join(self, joined: GuardedPortJoin, *, nodes: int) -> None:
        """Retain a fully checked composed port until this query owner closes."""
        from number_compiler.sequences.collatz.guarded_port_join import (
            GuardedPortJoin,
        )

        self._check()
        if type(joined) is not GuardedPortJoin:
            raise TypeError("joined-port owner requires its exact guarded result")
        if type(nodes) is not int or nodes < 1:
            raise ValueError("joined-port retention requires a positive node charge")
        tape = joined.parity_tape
        if type(tape) is not ParityCarryTape or tape is not self._root:
            raise ValueError("joined-port retention requires the current action root")
        joined.parity_tape_for_action()
        actions = self._actions
        assert actions is not None
        action = actions.get(id(tape))
        if (
            action is None
            or action[0] is not tape
            or action[1].coefficient_snapshot()
            != joined.port.action.coefficient_snapshot()
        ):
            raise ValueError("joined-port retention lost its exact cached action")
        retained = self._retained_records
        if retained is None:
            raise RuntimeError("parity retained-record store is unavailable")
        retained.retain_join(joined, nodes, scratch_owner=self.scratch_owner)

    def _retain_reference(
        self,
        node: ParityCarryTape,
        *,
        journal: list[tuple[int, ParityCarryTape, int | None]],
        workspace: LedgerReservation,
    ) -> None:
        """Charge one root or parent edge, never walking its descendants."""
        key = id(node)
        refs = self._live
        assert refs is not None
        prior = refs.get(key)
        if prior is not None and prior[0] is not node:
            raise RuntimeError("recycled reference identity in tape DAG")
        workspace.reserve(nodes=2)
        old = None if prior is None else prior[1]
        journal.append((key, node, old))
        try:
            refs[key] = (node, 1 if old is None else old + 1)
        except BaseException:
            journal.pop()
            raise

    def _restore_references(
        self, journal: list[tuple[int, ParityCarryTape, int | None]]
    ) -> None:
        refs = self._live
        assert refs is not None
        for key, node, old in reversed(journal):
            if old is None:
                del refs[key]
            else:
                refs[key] = (node, old)

    def _pin(self, root: ParityCarryTape) -> None:
        """Atomically publish a root switch through a preflighted delta plan."""
        if root is self._root:
            return
        from number_compiler.resources.ledger import LedgerReservation
        from number_compiler.resources.lifecycle import cleanup_all
        from number_compiler.resources.reference_delta import (
            AtomicRootDeltaPlan,
            plan_root_reference_changes,
        )

        actions, refs = self._actions, self._live
        assert actions is not None and refs is not None
        root_key = id(root)
        cached = actions.get(root_key)
        if (
            cached is None
            or cached[0] is not root
            or not cached[1].producer_issued
            or cached[1].steps != root.steps
        ):
            raise RuntimeError("cannot pin an unauthenticated parity action root")
        old_root = self._root
        plan: AtomicRootDeltaPlan[ParityCarryTape] | None = None
        dead_actions: dict[int, tuple[ParityCarryTape, DyadicTerminalFieldAction]] = {}
        plan_held = False
        root_entry_charge: tuple[int, int] | None = None
        root_live_usage_before: tuple[int, int] | None = None
        workspace: LedgerReservation | None = None
        rollback_workspace: LedgerReservation | None = None

        def release_root_entry_charge(mismatch_message: str) -> None:
            nonlocal root_entry_charge
            if root_entry_charge is None:
                return
            if root_live_usage_before is None:
                raise RuntimeError("root reservation lost its prior live usage")
            live_usage = self.ledger.account_usage(self._live_owner)
            charged_usage = (
                root_live_usage_before[0] + root_entry_charge[0],
                root_live_usage_before[1] + root_entry_charge[1],
            )
            if live_usage == charged_usage:
                self.ledger.release(
                    self._live_owner,
                    entries=root_entry_charge[0],
                    nodes=root_entry_charge[1],
                )
            elif live_usage != root_live_usage_before:
                raise RuntimeError(mismatch_message)
            root_entry_charge = None

        try:
            workspace = LedgerReservation(self.ledger, self.scratch_owner)
            with workspace:
                plan = plan_root_reference_changes(
                    (root,),
                    () if old_root is None else (old_root,),
                    lookup=refs.get,
                    children=lambda node: node.children,
                    reservation=workspace,
                )
                plan.validate_current(refs.get)
                if self.ledger.account_usage(self._plan_owner) != (0, 0):
                    raise RuntimeError("root delta workspace was not empty")
                for change in plan.changes:
                    if change.after != 0:
                        continue
                    action = actions.get(change.key)
                    if action is None or action[0] is not change.node:
                        raise RuntimeError(
                            "planned dead parity node has no exact action row"
                        )
                    dead_actions[change.key] = action
                if plan.reserved_entries:
                    root_live_usage_before = self.ledger.account_usage(self._live_owner)
                    root_entry_charge = (
                        plan.reserved_entries,
                        4 * plan.reserved_entries,
                    )
                    workspace.transfer_to(
                        self._live_owner,
                        entries=plan.reserved_entries,
                        nodes=4 * plan.reserved_entries,
                    )
                plan_held = True
                workspace.transfer_to(self._plan_owner, nodes=plan.reserved_nodes)
        except BaseException as error:

            def release_preflight_plan() -> None:
                if plan_held and plan is not None:
                    entries, nodes = self.ledger.account_usage(self._plan_owner)
                    if entries or nodes not in (0, plan.reserved_nodes):
                        raise RuntimeError("root preflight plan charge is inconsistent")
                    if nodes:
                        self.ledger.release(self._plan_owner, nodes=nodes)

            def close_preflight_scratch() -> None:
                if workspace is not None:
                    self.ledger.close_reservation(workspace)

            try:
                cleanup_all(
                    (
                        release_preflight_plan,
                        lambda: release_root_entry_charge(
                            "root preflight rollback changed live reference charges"
                        ),
                        close_preflight_scratch,
                    )
                )
            except BaseException as rollback_error:
                self._failed = True
                raise rollback_error from error
            raise

        assert plan is not None
        self.retirement_node_visits += plan.visited_nodes
        self.retirement_edge_visits += plan.visited_edges
        self.edge_visits += plan.visited_nodes + plan.visited_edges

        # Reserve exact restoration capacity on the existing root-plan owner
        # before the first destructive store write. A failed __delitem__ may
        # mutate then raise, so rollback must republish rows from this scoped
        # plan reservation without an unbudgeted insertion.
        restore_reference_rows = sum(
            1 for change in plan.changes if change.before > 0 and change.after == 0
        )
        restore_action_nodes = sum(
            actions.entry_nodes(key, payload) for key, payload in dead_actions.items()
        )
        rollback_workspace = LedgerReservation(self.ledger, self._plan_owner)
        try:
            rollback_workspace.reserve(
                entries=len(dead_actions) + restore_reference_rows,
                nodes=restore_action_nodes + 4 * restore_reference_rows,
            )
        except BaseException as error:
            try:
                rollback_workspace.close()
                if plan_held:
                    remaining_plan_nodes = self.ledger.account_usage(self._plan_owner)[
                        1
                    ]
                    if remaining_plan_nodes:
                        self.ledger.release(
                            self._plan_owner, nodes=remaining_plan_nodes
                        )
                    plan_held = False
                release_root_entry_charge(
                    "root reservation refusal changed live reference charges"
                )
            except BaseException as rollback_error:
                self._failed = True
                raise rollback_error from error
            raise

        try:
            # Every reference row is rechecked before the first retained write.
            plan.validate_current(refs.get)
            target = next(change for change in plan.changes if change.key == root_key)
            if target.after != target.before:
                if target.before == 0:
                    if root_entry_charge is None:
                        raise RuntimeError("new root row lost its reserved charge")
                    refs.publish_reserved(root_key, (root, target.after))
                else:
                    refs[root_key] = (root, target.after)
            for change in plan.changes:
                if change.key == root_key or change.before == change.after:
                    continue
                if change.after == 0:
                    del refs[change.key]
                    del actions[change.key]
                else:
                    refs[change.key] = (change.node, change.after)
            self.ledger.release(self._plan_owner, nodes=plan.reserved_nodes)
            plan_held = False
        except BaseException as error:
            # Restore action rows before reference rows so every live reference
            # regains its exact action. The old root pointer is still published.
            try:
                for key, payload in dead_actions.items():
                    if actions.get(key) is None:
                        actions.adopt_reserved(key, payload, rollback_workspace)
                for change in reversed(plan.changes):
                    current = refs.get(change.key)
                    if change.before == 0:
                        if current is not None:
                            del refs[change.key]
                    elif current is None:
                        rollback_workspace.transfer_to(
                            self._live_owner, entries=1, nodes=4
                        )
                        refs.publish_reserved(change.key, (change.node, change.before))
                    elif current[0] is not change.node or current[1] != change.before:
                        refs[change.key] = (change.node, change.before)
                release_root_entry_charge(
                    "root rollback changed live reference charges"
                )
                rollback_workspace.close()
                rollback_workspace = None
                if plan_held:
                    remaining = self.ledger.account_usage(self._plan_owner)[1]
                    if remaining:
                        self.ledger.release(self._plan_owner, nodes=remaining)
                    plan_held = False
            except BaseException as rollback_error:
                self._failed = True
                try:
                    if rollback_workspace is not None:
                        rollback_workspace.close()
                        rollback_workspace = None
                    remaining = self.ledger.account_usage(self._plan_owner)[1]
                    if remaining:
                        self.ledger.release(self._plan_owner, nodes=remaining)
                    plan_held = False
                except BaseException as cleanup_error:
                    raise cleanup_error from rollback_error
                raise rollback_error from error
            raise

        try:
            rollback_workspace.close()
            rollback_workspace = None
        except BaseException:
            # All reference/action mutations have committed but the root pointer
            # has not moved. Fail closed so disposal, rather than a partial
            # cache hit, owns this exceptional cleanup case.
            self._failed = True
            raise

        # This is the transaction's final operation; there is no deferred
        # retirement work after the externally visible root switch.
        self._root = root

    def start(self, bits: tuple[int, ...]) -> ParityCarryTape:
        """Admit a new source-free leaf before publishing its tape owner."""
        from number_compiler.resources.ledger import LedgerReservation

        self._check()
        if self._root is not None:
            raise ValueError("parity tape arena already has a live root")
        if (
            type(bits) is not tuple
            or not 1 <= len(bits) <= 64
            or any(type(bit) is not int or bit not in (0, 1) for bit in bits)
        ):
            raise ValueError("SLP leaf requires 1..64 certified parity bits")
        with LedgerReservation(self.ledger, self.scratch_owner) as creation:
            creation.reserve(nodes=128)
            root = ParityCarryTape.letters(bits)
        # Publish only after the construction reservation has closed. This
        # keeps a reservation-close failure from leaving a pinned root behind.
        self.action(root)
        return root

    def append(self, root: ParityCarryTape, bits: tuple[int, ...]) -> ParityCarryTape:
        """Budgeted AVL append, including transient rotations and new letter.

        The construction reservation accounts for intermediate rotation
        nodes at peak. It closes before the exact new-root action and pin
        transaction; failures leave the prior root current.
        """
        from number_compiler.resources.ledger import LedgerReservation

        self._check()
        if type(root) is not ParityCarryTape or root is not self._root:
            raise ValueError("SLP append requires the owner's current charged root")
        if (
            type(bits) is not tuple
            or not 1 <= len(bits) <= 64
            or any(type(bit) is not int or bit not in (0, 1) for bit in bits)
        ):
            raise ValueError("SLP append requires 1..64 certified parity bits")
        with LedgerReservation(self.ledger, self.scratch_owner) as creation:
            # Charge the leaf, its bit tuple and its integer metadata before
            # allocating any retained structure. 128 nodes is an upper bound
            # for 64 one-byte (or small-integer) input symbols and headers.
            creation.reserve(nodes=128)
            leaf = ParityCarryTape.letters(bits)

            def preallocate(left: ParityCarryTape, right: ParityCarryTape) -> None:
                width = (left.steps + right.steps).bit_length()
                # Parent and child tuple, step/odds integers and temporary
                # immutable tuple/object construction, incl. rotation nodes.
                creation.reserve(nodes=48 + (width + 63) // 64)

            joined = ParityCarryTape.sequence((root, leaf), on_node=preallocate)
        # The immutable nodes are not externally observable between their
        # construction and the exact persistent charge/pin in action().
        self.action(joined)
        return joined

    def action(self, root: ParityCarryTape) -> DyadicTerminalFieldAction:
        """Fold only uncached DAG nodes; a cache hit does no compositions.

        The iterative stack is locally charged as it grows; a per-node
        reservation covers all retained/temporary affine allocations until
        the exact payload is adopted. A failed admission leaves no new row.
        """
        from number_compiler.resources.ledger import LedgerReservation

        self._check()
        if type(root) is not ParityCarryTape:
            raise TypeError("parity action expects an immutable parity tape")
        memo = self._actions
        assert memo is not None
        root_key = id(root)
        existing = memo.get(root_key)
        if existing is not None:
            if existing[0] is not root:
                raise RuntimeError("parity memo identity was recycled")
            self._pin(root)
            self.cache_hits += 1
            return existing[1]
        # Root publication is deliberately outside this fold transaction.
        # Otherwise a failing reservation close could leave the root pointer
        # switched even though the request itself failed.
        pending: list[tuple[ParityCarryTape, bool]] = []
        published: list[int] = []
        edge_journal: list[tuple[int, ParityCarryTape, int | None]] = []
        node: ParityCarryTape | None = None
        result: DyadicTerminalFieldAction | None = None
        try:
            # A single reservation owns the traversal stack and intermediate
            # row construction. Cached rows retain their exact payload charge.
            with LedgerReservation(self.ledger, self.scratch_owner) as scope:

                def push(node: ParityCarryTape, ready: bool) -> None:
                    scope.reserve(nodes=4)
                    pending.append((node, ready))

                push(root, False)
                while pending:
                    node, ready = pending.pop()
                    scope.release(nodes=4)
                    key = id(node)
                    if key in memo:
                        if memo[key][0] is not node:
                            raise RuntimeError("parity memo identity was recycled")
                        self.cache_hits += 1
                        continue
                    if not ready and node.children:
                        push(node, True)
                        for child in reversed(node.children):
                            self.edge_visits += 1
                            self.discovery_edge_visits += 1
                            if id(child) not in memo:
                                push(child, False)
                        continue
                    # Acquire a conservative high-water reservation before
                    # making *any* unbounded affine arithmetic object.
                    bound = self._construction_bound(node)
                    scope.reserve(entries=1, nodes=bound)
                    if node.kind == "word":
                        result = DyadicTerminalFieldAction.identity()
                        for bit in node.word:
                            result = result.then(
                                DyadicTerminalFieldAction.one_run(1)
                                if bit
                                else DyadicTerminalFieldAction.zero_run(1)
                            )
                            self.compositions += 1
                    elif node.kind == "repeat":
                        result = memo[id(node.children[0])][1].power(
                            node.repetitions,
                            on_compose=lambda _a, _b: self._bump_compose(),
                        )
                    else:
                        result = DyadicTerminalFieldAction.identity()
                        for child in node.children:
                            result = result.then(memo[id(child)][1])
                            self.compositions += 1
                    # The leaf letters are issued individually; concat and
                    # repeat preserve the gain=3^odds invariant inductively.
                    # Recomputing 3^odds at every parent would itself restore
                    # the large-operand quadratic regression.
                    if not result.producer_issued or result.steps != node.steps:
                        raise ArithmeticError(
                            "affine node lost its authenticated parity action"
                        )
                    payload = (node, result)
                    actual = memo.entry_nodes(key, payload)
                    if actual > bound:
                        raise RuntimeError(
                            "parity affine construction exceeded its reserved envelope"
                        )
                    scope.reserve(nodes=2)  # the rollback journal slot
                    published.append(key)
                    try:
                        memo.adopt_reserved(key, payload, scope)
                    except BaseException:
                        published.pop()
                        scope.release(nodes=2)
                        raise
                    # Retained charge was transferred, scratch remainder is
                    # no longer needed. A failed publication returns both.
                    scope.release(nodes=bound - actual)
                    for child in node.children:
                        self.edge_visits += 1
                        self.published_edge_references += 1
                        self._retain_reference(
                            child,
                            journal=edge_journal,
                            workspace=scope,
                        )
                    result = None
            final = memo[root_key]
            if final[0] is not root:
                raise RuntimeError("parity owner lost its exact root")
            # The fold reservation has closed successfully. Pinning is now a
            # separate small transaction; its own commit point is after its
            # reservation closes, and it does no fallible work afterward.
            self._pin(root)
            return final[1]
        except BaseException as error:
            # No failed request may strand newly published child summaries.
            # Existing cached rows and the former root remain unchanged.
            if not self._failed:
                try:
                    self._restore_references(edge_journal)
                    for key in reversed(published):
                        del memo[key]
                except BaseException as rollback_error:
                    self._failed = True
                    raise rollback_error from error
            raise
        finally:
            pending.clear()
            published.clear()
            edge_journal.clear()
            node = None
            result = None

    def prefix_units(self, root: ParityCarryTape, time: int) -> UnitsCarryMatrix:
        """Fold an issued weighted prefix under a preflighted scratch reservation."""
        from number_compiler.resources.ledger import LedgerReservation

        self._check()
        if type(root) is not ParityCarryTape:
            raise TypeError("weighted prefix requires an immutable parity tape")
        if type(time) is not int or not 0 <= time <= root.steps:
            raise ValueError("weighted prefix lies outside its certified parity word")
        actions, refs = self._actions, self._live
        assert actions is not None and refs is not None
        key = id(root)
        action_row = actions.get(key)
        reference_row = refs.get(key)
        if (
            action_row is None
            or action_row[0] is not root
            or not action_row[1].producer_issued
            or action_row[1].steps != root.steps
            or reference_row is None
            or reference_row[0] is not root
            or reference_row[1] < 1
        ):
            raise RuntimeError("weighted prefix needs a live issued tape action")
        live_nodes = len(refs)
        scratch_entries, scratch_nodes = prefix_units_scratch_envelope(root, live_nodes)
        with LedgerReservation(self.ledger, self.scratch_owner) as reservation:
            reservation.reserve(entries=scratch_entries, nodes=scratch_nodes)
            return root.prefix_units(time)

    def _bump_compose(self) -> None:
        self.compositions += 1
