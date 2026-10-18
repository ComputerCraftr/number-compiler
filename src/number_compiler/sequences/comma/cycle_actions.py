"""Normalized interior-cycle actions, separate from future branch authority.

The cached payload has no source value, index, headroom or local arena handle.
Every receiving occurrence still checks its phase and strict seam guard. This
owner implements the closed repeated-period law, not a future Moore quotient.
"""

from __future__ import annotations

from collections.abc import Callable
from math import gcd
from typing import Final, cast

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import comma as _comma_keys
from number_compiler.resources.process_cache import (
    MISSING,
    CacheLease,
    get_process_cache,
)
from number_compiler.sequences.comma.arithmetic import cycle_transfer

CYCLE_CACHE_VERSION: Final[str] = "comma-interior-cycle-v2-phase-coset"
_CYCLE_PUBLISHER = object()
CycleSummary = tuple[int, int, int]


def normalized_cycle(leading: int, digit: int, copies: int) -> CycleSummary:
    """(literal steps, displacement, strict guard), for positive copies.

    HOL: comma_normalized_cycle_refines. No tree or represented iteration is
    constructed. The identity case belongs to the action arena, not this law.
    """
    if type(copies) is not int or copies < 1:
        raise ValueError("powered comma cycle count must be positive")
    transfer = cycle_transfer(leading, digit)
    displacement = copies * transfer.displacement
    return (
        copies * transfer.period,
        displacement,
        displacement + int(leading < 9),
    )


class CycleActionReuse:
    """Optional bounded process reuse of source-independent normalized actions.

    Query-local action IDs remain in CommaActionArena. A lease exists only for
    the duration of a lookup/publication transaction; no foreign ID is retained.
    """

    def __init__(
        self,
        ledger: ResourceLedger,
        charge: Callable[[int], None],
        charge_bits: Callable[[int], None],
        *,
        shared: bool,
    ) -> None:
        self.ledger = ledger
        self.charge = charge
        self.charge_bits = charge_bits
        self.shared = shared
        for name in (
            "lookups",
            "exact_hits",
            "transported_hits",
            "local_hits",
            "process_hits",
            "misses",
            "publications",
            "bypasses",
            "admission_rejections",
            "applied_hits",
            "applied_parent_hits",
            "key_operand_bits",
        ):
            self.count(name, 0)
        for name in (
            "cold_child_discoveries",
            "coefficient_compositions",
            "failed_work",
            "capacity_bypasses",
        ):
            ledger.bump("comma_hashlife_" + name, 0)

    def count(self, suffix: str, amount: int = 1) -> None:
        self.ledger.bump("comma_hashlife_semantic_" + suffix, amount)

    def request(self, leading: int, digit: int, copies: int) -> None:
        if (
            type(leading) is not int
            or not 1 <= leading <= 9
            or type(digit) is not int
            or not 0 <= digit <= 9
            or type(copies) is not int
            or copies < 1
        ):
            raise ValueError("invalid comma cycle action key")
        self.charge(1)
        bits = leading.bit_length() + digit.bit_length() + copies.bit_length()
        self.charge_bits(bits)
        self.count("key_operand_bits", bits)
        self.count("lookups")

    def _cold(self, leading: int, digit: int, copies: int) -> CycleSummary:
        self.charge(8)
        self.charge_bits(8 * copies.bit_length() + 640)
        result = normalized_cycle(leading, digit, copies)
        self.ledger.bump(_comma_keys.COMMA_TRANSFER_CONSTRUCTIONS)
        self.ledger.bump(_comma_keys.COMMA_CYCLE_RULE_EVALUATIONS)
        self.ledger.bump(_comma_keys.COMMA_HASHLIFE_COEFFICIENT_COMPOSITIONS)
        return result

    def _lookup(
        self,
        lease: CacheLease,
        key: tuple[int, int, int],
    ) -> tuple[CycleSummary, bool]:
        try:
            value = lease.get_issued(key, _CYCLE_PUBLISHER)
            if value is not MISSING:
                if type(value) is not tuple or len(value) != 3:
                    raise ValueError("malformed comma cycle action")
                fields = cast(CycleSummary, value)
                if any(type(field) is not int or field <= 0 for field in fields):
                    raise ValueError("malformed comma cycle action")
                if any(
                    field.bit_length() > key[2].bit_length() + 10 for field in fields
                ):
                    raise ValueError("malformed comma cycle action")
                self.charge(1)
                self.charge_bits(sum(field.bit_length() for field in fields))
                # The process key is already the canonical (leading, phase
                # coset, copies) semantic action. Source transport is reported
                # by the source-image application lane after admission.
                self.count("exact_hits")
                self.count("process_hits")
                return fields, True
        except Exception:
            self.count("admission_rejections")
            raise
        self.count("misses")
        result = self._cold(*key)
        # Publication failure cannot invalidate the freshly constructed action.
        self.charge(1)
        try:
            published = lease.put_issued(key, result, _CYCLE_PUBLISHER)
        except BlockContextBudgetExceeded:
            published = False
        self.count("publications" if published else "bypasses")
        if not published:
            self.ledger.bump(_comma_keys.COMMA_HASHLIFE_CAPACITY_BYPASSES)
        return result, False

    def resolve(
        self, leading: int, digit: int, copies: int
    ) -> tuple[CycleSummary, bool]:
        """Called after the arena's complete local action lookup misses."""
        cache = get_process_cache() if self.shared else None
        if cache is not None and cache.enabled:
            try:
                lease = cache.acquire(
                    "comma-cycle-action", CYCLE_CACHE_VERSION, (10, "strict-interior")
                )
            except BlockContextBudgetExceeded:
                self.count("bypasses")
                self.ledger.bump(_comma_keys.COMMA_HASHLIFE_CAPACITY_BYPASSES)
            else:
                with lease:
                    # Complete phase rotations have the same duration, sum and
                    # strict guard. The arena retains the actual entering digit
                    # coset as the semantic ID and checks the receiving
                    # occurrence against that coset independently. HOL:
                    # comma_normalized_cycle_gcd_normalization.
                    self.charge(1)
                    phase = digit % gcd(leading, 10)
                    return self._lookup(
                        lease,
                        (leading, phase, copies),
                    )
        else:
            self.count("bypasses")
        self.count("misses")
        return self._cold(leading, digit, copies), False
