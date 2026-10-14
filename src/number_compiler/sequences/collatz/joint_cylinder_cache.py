"""Bounded reuse for authenticated endpoint and normalized-sum cylinders.

The joint action is keyed by its finite source cylinder and temporal width.
An endpoint-only occurrence never supplies its prefix-sum fields: lookup is
issued separately and production must cross-check it against the endpoint
macro before consuming either result.
"""

from __future__ import annotations

from typing import Self, cast

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.process_cache import (
    MISSING,
    CacheRecordIssuerMismatch,
    get_process_cache,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)

_JOINT_ACTION_ISSUER = object()


class JointCertifiedMacroCache:
    """Ledger-owned local and process cache for complete affine field actions."""

    VERSION = "collatz-joint-source-cylinder-v1"
    LIMIT = 256
    MAX_INTERIOR = 64
    MAX_WIDTH = 256

    def __init__(self, ledger: ResourceLedger, *, shared_cache: bool) -> None:
        if type(ledger) is not ResourceLedger or type(shared_cache) is not bool:
            raise TypeError("joint macro cache requires a ledger and Boolean policy")
        self.ledger = ledger
        self.shared_cache = shared_cache
        self._closed = False
        self._cleanup_complete = False
        self._interior_records = 0

        def make_store(
            name: str,
            role: str,
            *,
            nodes_per_entry: int,
            evictable: bool = False,
        ) -> OwnedMemo[object, object]:
            owner = ledger.register(name, role)
            try:
                return OwnedMemo(
                    ledger,
                    owner,
                    nodes_per_entry=nodes_per_entry,
                    evictable=evictable,
                )
            except BaseException:
                ledger.mark_disposed(owner)
                raise

        frontier = make_store(
            f"collatz-joint-macro-frontier-{ledger.owner_count}",
            "execution_stack",
            nodes_per_entry=20,
        )
        try:
            actions = make_store(
                f"collatz-joint-macros-{ledger.owner_count}",
                "query_memo",
                nodes_per_entry=20,
                evictable=True,
            )
        except BaseException:
            cleanup_all((frontier.dispose,))
            raise
        self.frontier: OwnedMemo[
            int, tuple[int, DyadicTerminalFieldAction, int, int]
        ] = cast(
            OwnedMemo[int, tuple[int, DyadicTerminalFieldAction, int, int]], frontier
        )
        self.actions: OwnedMemo[
            tuple[int, int], tuple[DyadicTerminalFieldAction, int, int]
        ] = cast(
            OwnedMemo[tuple[int, int], tuple[DyadicTerminalFieldAction, int, int]],
            actions,
        )
        try:
            for name in (
                "lookups",
                "local_hits",
                "process_hits",
                "exact_hits",
                "transported_hits",
                "misses",
                "publications",
                "applied_hits",
                "parent_joins",
                "evictions",
                # ``bypasses`` is the legacy capacity lane consumed by the
                # diagnostics projection. Other refusal reasons stay
                # disjoint so the projection can sum each request once.
                "bypasses",
                "disabled_bypasses",
                "policy_bypasses",
                "invalid_records",
                "key_operand_bits",
                "gain_check_operand_bits",
                "source_admission_operand_bits",
                "endpoint_crosscheck_operand_bits",
                "validation_operand_bits",
            ):
                self._bump(name, 0)
            ledger.register_execution_root(self)
        except BaseException:
            cleanup_all((self.actions.dispose, self.frontier.dispose))
            raise

    def __enter__(self) -> Self:
        self._check_open()
        return self

    def __exit__(self, *_args: object) -> None:
        self.close()

    def close(self) -> None:
        if self._cleanup_complete:
            return
        self._closed = True
        cleanup_all((self.actions.dispose, self.frontier.dispose))
        self._cleanup_complete = True

    def _check_open(self) -> None:
        if self._closed:
            raise RuntimeError("joint macro cache is closed")

    def _bump(self, name: str, amount: int = 1) -> None:
        self.ledger.bump(f"collatz_hashlife_joint_{name}", amount)

    @classmethod
    def _key(cls, source: int, width: int) -> tuple[int, int]:
        source = require_integer(source, "joint macro source", 1)
        width = require_integer(width, "joint macro width", 16, cls.MAX_WIDTH)
        if width & (width - 1):
            raise ValueError("joint macro width must be dyadic")
        mask = (1 << width) - 1
        residue = source & mask
        return width, residue

    @staticmethod
    def _fiber(source: int, width: int) -> int:
        """Compute high-fiber occurrence data only after a record is found."""
        return source >> width

    @staticmethod
    def _payload(
        action: DyadicTerminalFieldAction, odd_symbols: int, publisher_fiber: int
    ) -> tuple[int, ...]:
        return (
            action.gain,
            action.offset,
            action.sum_gain,
            action.sum_offset,
            action.previous_gain,
            action.previous_offset,
            odd_symbols,
            publisher_fiber,
        )

    @staticmethod
    def _restore(
        width: int, payload: object
    ) -> tuple[DyadicTerminalFieldAction, int, int]:
        if (
            type(payload) is not tuple
            or len(payload) != 8
            or any(type(value) is not int for value in payload)
        ):
            raise ValueError("joint macro cache payload is malformed")
        action = DyadicTerminalFieldAction._restore_issued(width, payload[:6])
        odd_symbols, publisher_fiber = payload[6:]
        if not 0 <= odd_symbols <= width or publisher_fiber < 0:
            raise ValueError("joint macro cache clock is malformed")
        return action, odd_symbols, publisher_fiber

    def _validate(
        self,
        action: DyadicTerminalFieldAction,
        odd_symbols: int,
        source: int,
        width: int,
        residue: int,
    ) -> None:
        if (
            type(action) is not DyadicTerminalFieldAction
            or not action.producer_issued
            or action.steps != width
            or not 0 <= odd_symbols <= width
            or type(residue) is not int
            or not 0 <= residue < 1 << width
        ):
            raise ValueError("joint macro does not match its source cylinder")
        self._bump(
            "gain_check_operand_bits", action.gain.bit_length() + 2 * odd_symbols + 1
        )
        if action.gain != 3**odd_symbols:
            raise ValueError("joint macro gain differs from its odd count")
        self._bump(
            "source_admission_operand_bits",
            width + source.bit_length() + action.offset.bit_length(),
        )
        if action.source_residue != residue or not action.certifies(source):
            raise ValueError("joint macro source cylinder does not match its key")
        self._bump(
            "validation_operand_bits",
            sum(
                max(1, value.bit_length())
                for value in (
                    action.gain,
                    action.offset,
                    action.sum_gain,
                    action.sum_offset,
                    action.previous_gain,
                    action.previous_offset,
                )
            ),
        )

    def lookup(
        self, source: int, width: int
    ) -> tuple[DyadicTerminalFieldAction, int] | None:
        self._check_open()
        key = self._key(source, width)
        self._bump("lookups")
        self._bump("key_operand_bits", source.bit_length() + width.bit_length())
        local = self.actions.get(key)
        if local is not None:
            if (
                type(local) is not tuple
                or len(local) != 3
                or type(local[0]) is not DyadicTerminalFieldAction
                or any(type(value) is not int for value in local[1:])
            ):
                self._bump("invalid_records")
                raise ValueError("local joint macro record is malformed")
            action, odd_symbols, publisher_fiber = local
            self._validate(action, odd_symbols, source, width, key[1])
            fiber = self._fiber(source, width)
            self._classify_hit(fiber, publisher_fiber, "local_hits")
            return action, odd_symbols
        if not self.shared_cache:
            self._bump("policy_bypasses")
            self._bump("misses")
            return None
        cache = get_process_cache()
        if not cache.enabled:
            self._bump("disabled_bypasses")
            self._bump("misses")
            return None
        try:
            lease = cache.acquire("collatz-joint-action", self.VERSION, key)
        except BlockContextBudgetExceeded:
            self._bump("bypasses")
            self._bump("misses")
            return None
        with lease:
            try:
                payload = lease.get_issued(("action",), _JOINT_ACTION_ISSUER)
            except CacheRecordIssuerMismatch:
                self._bump("invalid_records")
                raise
        if payload is MISSING:
            self._bump("misses")
            return None
        try:
            action, odd_symbols, publisher_fiber = self._restore(width, payload)
            self._validate(action, odd_symbols, source, width, key[1])
            if publisher_fiber < 0:
                raise ValueError("joint macro publisher fiber is invalid")
        except (TypeError, ValueError):
            self._bump("invalid_records")
            raise
        if len(self.actions) < self.LIMIT:
            self.actions[key] = (action, odd_symbols, publisher_fiber)
        fiber = self._fiber(source, width)
        self._classify_hit(fiber, publisher_fiber, "process_hits")
        return action, odd_symbols

    def _classify_hit(
        self, receiving_fiber: int, publisher_fiber: int, location: str
    ) -> None:
        self._bump(location)
        kind = (
            "exact_hits" if receiving_fiber == publisher_fiber else "transported_hits"
        )
        self._bump(kind)

    def remember(
        self,
        source: int,
        action: DyadicTerminalFieldAction,
        odd_symbols: int,
    ) -> bool:
        self._check_open()
        if type(action) is not DyadicTerminalFieldAction or not action.producer_issued:
            raise ValueError("joint cache publication requires a producer action")
        key = self._key(source, action.steps)
        odd_symbols = require_integer(
            odd_symbols, "joint macro odd count", 0, action.steps
        )
        self._validate(action, odd_symbols, source, action.steps, key[1])
        existing = self.actions.get(key)
        if existing is not None:
            if (
                type(existing) is not tuple
                or len(existing) != 3
                or type(existing[0]) is not DyadicTerminalFieldAction
                or type(existing[1]) is not int
                or type(existing[2]) is not int
            ):
                self._bump("invalid_records")
                raise ValueError("local joint macro record is malformed")
            if existing[0] != action or existing[1] != odd_symbols:
                raise ValueError("conflicting joint actions for one source cylinder")
            return False
        if len(self.actions) >= self.LIMIT:
            self._bump("bypasses")
            return False
        publisher_fiber = self._fiber(source, action.steps)
        record = (action, odd_symbols, publisher_fiber)
        self.actions[key] = record
        if self.shared_cache:
            cache = get_process_cache()
            if cache.enabled:
                try:
                    lease = cache.acquire("collatz-joint-action", self.VERSION, key)
                except BlockContextBudgetExceeded:
                    self._bump("bypasses")
                else:
                    with lease:
                        payload = self._payload(action, odd_symbols, publisher_fiber)
                        if not lease.put_issued(
                            ("action",), payload, _JOINT_ACTION_ISSUER
                        ):
                            self._bump("bypasses")
            else:
                self._bump("disabled_bypasses")
        else:
            self._bump("policy_bypasses")
        self._bump("publications")
        return True

    def observe(
        self,
        source: int,
        action: DyadicTerminalFieldAction,
        odd_symbols: int,
        endpoint: int,
        *,
        anchor: int,
    ) -> None:
        """Store useful root/interior dyadic blocks emitted by the live run."""
        self._check_open()
        width = action.steps
        if width < 8 or width & (width - 1) or width > self.MAX_WIDTH:
            self.frontier.clear()
            return
        if width < 16 and width != 8:
            self.frontier.clear()
            return
        if not action.producer_issued:
            raise ValueError("joint macro cache accepts only producer actions")
        if width == 8:
            if (
                not 0 <= odd_symbols <= width
                or action.steps != width
                or action.gain != 3**odd_symbols
                or not action.certifies(source)
            ):
                raise ValueError("D8 joint producer differs from its source")
        else:
            self._validate(
                action, odd_symbols, source, width, source & ((1 << width) - 1)
            )
        if action.endpoint(source) != endpoint:
            raise ValueError("observed joint endpoint differs from current producer")
        if any(previous_width < width for previous_width in self.frontier):
            self.frontier.clear()
        joined = False
        while True:
            root_prefix = source == anchor
            useful_join = (
                joined
                and not root_prefix
                and self._interior_records < self.MAX_INTERIOR
            )
            if (
                (root_prefix or useful_join)
                and 16 <= width <= min(self.MAX_WIDTH, source.bit_length())
                and self.remember(source, action, odd_symbols)
            ):
                self._interior_records += int(useful_join)
            left = self.frontier.pop(width, None)
            if left is None:
                if endpoint > 2:
                    try:
                        self.frontier[width] = (source, action, odd_symbols, endpoint)
                    except BlockContextBudgetExceeded:
                        self.frontier.clear()
                        self._bump("bypasses")
                else:
                    self.frontier.clear()
                return
            left_source, left_action, left_odd, left_endpoint = left
            if left_endpoint != source:
                self.frontier.clear()
                raise ValueError("adjacent joint macro producer endpoints do not meet")
            action = left_action.then(action)
            source = left_source
            endpoint = action.endpoint(source)
            odd_symbols += left_odd
            width = action.steps
            joined = True
            self._bump("parent_joins")

    def applied(self) -> None:
        self._check_open()
        self._bump("applied_hits")


__all__ = ["JointCertifiedMacroCache"]
