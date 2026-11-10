"""Ledger-accounted AVL tape actions and incremental construction.

All retained and transient *tape* objects belong to one query ledger. This
module does not certify full guarded source/bridge joins: those transactions
must separately account for the CRT, digit bridges and affine seam buffers.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Self

from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.parity_carry_tape import ParityCarryTape

if TYPE_CHECKING:
    from number_compiler.resources.ledger import (
        LedgerReservation,
        OwnedMemo,
        ResourceLedger,
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
        "_retired_root",
        "_live_owner",
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
        )
        ledger.require_fresh_owner_names(owner_names)
        self.owner = -1
        self._live_owner = -1
        self.scratch_owner = -1
        self._root: ParityCarryTape | None = None
        self._retired_root: ParityCarryTape | None = None
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
            self._actions = OwnedMemo(
                ledger, self.owner, node_cost=self._action_node_cost
            )
            self._live = OwnedMemo(ledger, self._live_owner, nodes_per_entry=4)
            ledger.register_execution_root(self)
        except BaseException:
            from number_compiler.resources.lifecycle import cleanup_all

            cleanups = tuple(
                memo.dispose for memo in (self._actions, self._live) if memo is not None
            ) + tuple(
                lambda owner=owner: ledger.retire_unpublished_owner(owner)
                for owner in reversed(registered)
            )
            cleanup_all(cleanups)
            raise

    @staticmethod
    def _action_node_cost(
        _key: int, payload: tuple[ParityCarryTape, DyadicTerminalFieldAction]
    ) -> int:
        from sys import getsizeof

        node, action = payload
        # Size accounting is in the ledger's logical 64-bit node units, not
        # CPython's object count. Include referenced tuple/word and all
        # independently retained integer limbs, not just the action pointer.
        byte_count = (
            getsizeof(node)
            + getsizeof(node[0])
            + getsizeof(node.children)
            + getsizeof(node.word)
            + getsizeof(node.kind)
            + getsizeof(action)
            + getsizeof(action.coefficient_snapshot())
            + getsizeof(payload)
        )
        # Integral fields may alias by identity. Charging once per occurrence
        # is conservative and never omits actual retained coefficient bytes.
        byte_count += sum(getsizeof(value) for value in action.coefficient_snapshot())
        byte_count += (
            getsizeof(node.steps)
            + getsizeof(node.odds)
            + getsizeof(node.repetitions)
            + getsizeof(node.height)
            + getsizeof(node.traversal_depth)
        )
        byte_count += sum(getsizeof(v) for v in node.word)
        return max(1, (byte_count + 7) // 8)

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
        return 160 + 12 * ((4 * (s + 2 * o + 8) + 63) // 64)

    def _check(self) -> None:
        if self._closed:
            raise RuntimeError("disposed parity tape action owner")
        if self._failed:
            raise RuntimeError("failed parity tape action owner is unusable")
        if self.owner < 0 or self._live_owner < 0 or self.scratch_owner < 0:
            raise RuntimeError("parity tape action owner was not fully initialized")
        if any(
            self.ledger.account_status(owner).disposed
            for owner in (self.owner, self._live_owner, self.scratch_owner)
        ):
            self._failed = True
            raise RuntimeError(
                "parity tape action owner has been revoked by its ledger"
            )
        if self._actions is None or self._live is None:
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

        assert self._actions is not None and self._live is not None
        try:
            cleanup_all((self._actions.dispose, self._live.dispose))
            if self.ledger.account_status(self.scratch_owner).disposed is False:
                self.ledger.mark_disposed(self.scratch_owner)
        except BaseException:
            # Disposal may be retried to finish reclaiming a partially cleared
            # store, but no action lookup is permitted in the meantime.
            self._failed = True
            raise
        self._root = None
        self._retired_root = None
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

    @property
    def retirement_pending(self) -> bool:
        """Snapshot whether one former root awaits bounded reclamation.

        Reading this status never traverses or mutates the owner.
        """
        return self._retired_root is not None

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

    def _release_reference(
        self,
        root: ParityCarryTape,
        workspace: LedgerReservation,
    ) -> None:
        """Release one edge and reclaim only rows whose last edge disappeared."""
        refs = self._live
        actions = self._actions
        assert refs is not None and actions is not None
        if not workspace.belongs_to(self.ledger):
            raise RuntimeError("root release reservation belongs to another ledger")
        stack: list[ParityCarryTape] = [root]
        while stack:
            node = stack.pop()
            self.edge_visits += 1
            self.retirement_node_visits += 1
            key = id(node)
            entry = refs.get(key)
            if entry is None or entry[0] is not node or entry[1] < 1:
                raise RuntimeError("parity SLP reference graph lost an owned edge")
            if entry[1] > 1:
                refs[key] = (node, entry[1] - 1)
                continue
            cached = actions.get(key)
            if cached is None or cached[0] is not node:
                raise RuntimeError("parity reference has no exact cached action")
            del refs[key]
            del actions[key]
            for child in node.children:
                self.edge_visits += 1
                self.retirement_edge_visits += 1
                if len(stack) >= root.traversal_depth + 2:
                    raise RuntimeError("parity release frontier exceeds grammar depth")
                stack.append(child)

    def _discard_retired_root(self) -> None:
        """Release a previous root after the current root has committed."""
        retired = self._retired_root
        if retired is None:
            return
        from number_compiler.arithmetic.contracts.block_effect import (
            BlockContextBudgetExceeded,
        )
        from number_compiler.resources.ledger import LedgerReservation

        try:
            with LedgerReservation(self.ledger, self.scratch_owner) as workspace:
                workspace.reserve(nodes=4 * (retired.traversal_depth + 2) + 8)
                self._release_reference(retired, workspace)
        except BlockContextBudgetExceeded:
            # The old pin and its rows are intact when preflight refuses the
            # reservation, so a later request may retry after its own work.
            raise
        except BaseException:
            # Release or reservation-close failure can leave an uncertain
            # reference graph. Keep the old root pointer for audit/teardown,
            # but make the owner unusable until disposal retries cleanup.
            self._failed = True
            raise
        self._retired_root = None

    def _pin(self, root: ParityCarryTape) -> None:
        """Publish a new root only after all charged work has closed."""
        if root is self._root:
            self._discard_retired_root()
            return
        if root is self._retired_root:
            refs = self._live
            actions = self._actions
            if refs is None or actions is None:
                raise RuntimeError("parity root swap has no live memo stores")
            key = id(root)
            reference = refs.get(key)
            cached = actions.get(key)
            if (
                reference is None
                or reference[0] is not root
                or reference[1] < 1
                or cached is None
                or cached[0] is not root
                or not cached[1].producer_issued
                or cached[1].steps != root.steps
            ):
                raise RuntimeError("retired parity root lost its retained action pin")
            former = self._root
            if former is None:
                raise RuntimeError("retired parity root has no current peer")
            # Both roots already own one reference. Swap their roles without
            # releasing the requested root and without discovering children.
            self._root = root
            self._retired_root = former
            return
        from number_compiler.resources.ledger import LedgerReservation

        assert self._actions is not None and self._live is not None
        key = id(root)
        cached = self._actions.get(key)
        if (
            cached is None
            or cached[0] is not root
            or not cached[1].producer_issued
            or cached[1].steps != root.steps
        ):
            raise RuntimeError("cannot pin an unauthenticated parity action root")
        existing_reference = self._live.get(key)
        extra_entries = 0 if existing_reference is not None else 1
        journal: list[tuple[int, ParityCarryTape, int | None]] = []
        try:
            # Pin the requested root before pruning the retired DAG. A cached
            # descendant may be reachable only through that DAG; pruning first
            # would delete the very action this cache hit is meant to use.
            with LedgerReservation(self.ledger, self.scratch_owner) as workspace:
                workspace.reserve(entries=extra_entries, nodes=8)
                self._retain_reference(root, journal=journal, workspace=workspace)
        except BaseException as error:
            try:
                self._restore_references(journal)
            except BaseException as rollback_error:
                self._failed = True
                raise rollback_error from error
            raise
        from number_compiler.arithmetic.contracts.block_effect import (
            BlockContextBudgetExceeded,
        )

        try:
            self._discard_retired_root()
        except BlockContextBudgetExceeded:
            # Preflight refusal leaves the retired tree untouched; undo the
            # temporary root pin so all previous root roles remain intact.
            try:
                self._restore_references(journal)
            except BaseException as rollback_error:
                self._failed = True
                raise rollback_error
            raise
        former = self._root
        # The temporary target pin becomes the new current-root pin, while the
        # previous current pin becomes the single deferred retirement pin.
        self._root = root
        self._retired_root = former

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

    def _bump_compose(self) -> None:
        self.compositions += 1
