"""Bounded, query-owned caches for certified conditional scheduler work."""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import (
    LedgerReservation,
    OwnedMemo,
    ResourceLedger,
)
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.metric_keys import collatz as _collatz_keys

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.conditional_scheduler_adapter import (
        CertifiedSchedulerCandidate,
    )


class ConditionalSchedulerMemo:
    """Retain guarded actions and exact-source misses inside one query ledger."""

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("conditional scheduler memo needs its query ledger")
        self.ledger = ledger
        self._ports: OwnedMemo[tuple[int, ...], object] | None = None
        self._misses: OwnedMemo[tuple[int, ...], bool] | None = None
        self._lookup_workspace_owner: int | None = None
        self._closed = False
        self._cleanup_complete = False

    def check_open(self) -> None:
        if self._closed:
            raise RuntimeError("conditional scheduler memo is closed")

    def _port_memo(self) -> OwnedMemo[tuple[int, ...], object]:
        self.check_open()
        if self._ports is None:

            def cost(_key: tuple[int, ...], candidate: object) -> int:
                from number_compiler.sequences.collatz.conditional_scheduler_adapter import (
                    CertifiedSchedulerCandidate,
                )

                if type(candidate) is not CertifiedSchedulerCandidate:
                    raise ValueError("conditional memo needs an issued source action")
                return 16 + (candidate.verification_operand_bits(0) + 63) // 64

            owner = self.ledger.register(
                f"collatz-dyadic-{self.ledger.owner_count}-conditional-ports",
                "query_memo",
            )
            try:
                self._ports = OwnedMemo(
                    self.ledger, owner, node_cost=cost, evictable=True
                )
            except BaseException:
                self.ledger.mark_disposed(owner)
                raise
        return self._ports

    def _ensure_lookup_workspace_owner(self) -> int:
        """Return this memo's private owner for temporary hit validation."""
        self.check_open()
        if self._lookup_workspace_owner is None:
            # The current owner count makes the name unique among memos that
            # share a ledger. Keep one scratch account per memo; each lookup
            # still registers and closes its own reservation against it.
            self._lookup_workspace_owner = self.ledger.register(
                f"collatz-dyadic-{self.ledger.owner_count}-conditional-port-lookup",
                "conditional_cache_lookup_workspace",
            )
        return self._lookup_workspace_owner

    def lookup_port(
        self,
        source: int,
        returns: int,
        demand: int,
        coefficient_budget: int,
        control_bits: int,
    ) -> CertifiedSchedulerCandidate | None:
        """Preflight each retained guard at its exact verification size."""
        self.check_open()
        memo = self._ports
        if memo is None:
            return None
        values = (source, returns, demand, coefficient_budget, control_bits)
        if any(type(value) is not int for value in values):
            raise ValueError("conditional port lookup request is malformed")
        if (
            source <= 0
            or returns <= 0
            or demand < 0
            or coefficient_budget < 32
            or control_bits < 0
        ):
            raise ValueError("conditional port lookup request is malformed")
        from number_compiler.sequences.collatz.conditional_scheduler_adapter import (
            CertifiedSchedulerCandidate,
        )

        candidates: list[tuple[CertifiedSchedulerCandidate, int]] = []
        for (r, d, budget, _residue, _modulus, _minimum), candidate in memo.items():
            if (r, d, budget) != (returns, demand, coefficient_budget):
                continue
            if type(candidate) is not CertifiedSchedulerCandidate:
                raise ValueError("conditional port cache is malformed")
            candidate.verify_memo_issued()
            bits = candidate.verification_operand_bits(
                control_bits, source_override=source
            )
            candidates.append((candidate, 16 + (bits + 63) // 64))
        if not candidates:
            return None

        owner = self._ensure_lookup_workspace_owner()
        reservation = LedgerReservation(self.ledger, owner)
        try:
            with reservation:
                reservation.reserve(nodes=max(nodes for _, nodes in candidates))
                for candidate, _ in candidates:
                    candidate.verify_memo_issued()
                    candidate.port.verify_issued()
                    if candidate.port.admits(source):
                        return candidate
        except BlockContextBudgetExceeded:
            self.ledger.bump(_collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_CACHE_BYPASSES)
        return None

    def remember_port(
        self,
        candidate: object,
        demand: int,
        coefficient_budget: int,
    ) -> None:
        """Retain one verified guarded action in a bounded query-owned memo."""
        self.check_open()
        from number_compiler.sequences.collatz.conditional_scheduler_adapter import (
            CertifiedSchedulerCandidate,
        )

        if (
            type(candidate) is not CertifiedSchedulerCandidate
            or type(demand) is not int
            or demand < 0
            or type(coefficient_budget) is not int
            or coefficient_budget < 32
        ):
            raise ValueError("conditional source action or demand is malformed")
        candidate.seal_for_memo()
        guard = candidate.port.guard
        key = (
            candidate.return_count,
            demand,
            coefficient_budget,
            guard.residue,
            guard.modulus,
            guard.minimum_source,
        )
        memo = self._port_memo()
        if key in memo:
            return
        if len(memo) >= 32:
            del memo[next(iter(memo))]
        try:
            memo[key] = candidate
        except BlockContextBudgetExceeded:
            self.ledger.bump(_collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_CACHE_BYPASSES)

    def _miss_memo(self) -> OwnedMemo[tuple[int, ...], bool]:
        self.check_open()
        if self._misses is None:
            owner = self.ledger.register(
                f"collatz-dyadic-{self.ledger.owner_count}-conditional-misses",
                "query_memo",
            )
            try:
                self._misses = OwnedMemo(
                    self.ledger, owner, nodes_per_entry=2, evictable=True
                )
            except BaseException:
                self.ledger.mark_disposed(owner)
                raise
        return self._misses

    def has_miss(self, key: tuple[int, ...]) -> bool:
        self.check_open()
        return self._misses is not None and key in self._misses

    def remember_miss(self, key: tuple[int, ...]) -> None:
        """Remember proof misses, never precision or temporary budget refusal."""
        self.check_open()
        if type(key) is not tuple or any(type(value) is not int for value in key):
            raise TypeError("conditional miss key must contain exact integers")
        memo = self._miss_memo()
        if key in memo:
            return
        if len(memo) >= 64:
            del memo[next(iter(memo))]
        try:
            memo[key] = True
        except BlockContextBudgetExceeded:
            self.ledger.bump(_collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_CACHE_BYPASSES)

    def close(self) -> None:
        if self._cleanup_complete:
            return
        self._closed = True
        disposals: list[Callable[[], None]] = []
        if self._misses is not None:
            disposals.append(self._misses.dispose)
        if self._ports is not None:
            disposals.append(self._ports.dispose)
        if self._lookup_workspace_owner is not None:
            owner = self._lookup_workspace_owner
            disposals.append(lambda: self.ledger.mark_disposed(owner))
        cleanup_all(disposals)
        self._misses = None
        self._ports = None
        self._lookup_workspace_owner = None
        self._cleanup_complete = True


class ConditionalSchedulerMemoOwner:
    """Mixin exposing a lazily created memo tied to a query-scoped owner."""

    ledger: ResourceLedger

    def check_open(self) -> None:
        raise NotImplementedError("memo owner must enforce its own lifecycle")

    def _scheduler_memo(self) -> ConditionalSchedulerMemo:
        self.check_open()
        memo = getattr(self, "_conditional_scheduler_memo", None)
        if memo is None:
            memo = ConditionalSchedulerMemo(self.ledger)
            self._conditional_scheduler_memo = memo
        return memo

    def lookup_conditional_port(
        self,
        source: int,
        returns: int,
        demand: int,
        coefficient_budget: int,
        control_bits: int,
    ) -> CertifiedSchedulerCandidate | None:
        return self._scheduler_memo().lookup_port(
            source, returns, demand, coefficient_budget, control_bits
        )

    def remember_conditional_port(
        self, candidate: object, demand: int, coefficient_budget: int
    ) -> None:
        self._scheduler_memo().remember_port(candidate, demand, coefficient_budget)

    def was_conditional_miss(self, key: tuple[int, ...]) -> bool:
        self.check_open()
        memo = getattr(self, "_conditional_scheduler_memo", None)
        return memo is not None and memo.has_miss(key)

    def remember_conditional_miss(self, key: tuple[int, ...]) -> None:
        self._scheduler_memo().remember_miss(key)

    def close_conditional_scheduler_memo(self) -> None:
        memo = getattr(self, "_conditional_scheduler_memo", None)
        if memo is not None:
            memo.close()
