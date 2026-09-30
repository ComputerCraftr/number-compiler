"""Finite branch observers shared by source-bound consumers and research.

These observers do not select source events or authorize successor merges.
Every exact lane transition consumes one common caller-admitted exponent.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger

PhaseFamily = Literal["mahler", "collatz"]

# Same finite bank as the supplied observer; not a primality oracle.
PRIME_BANK = (
    5,
    7,
    11,
    13,
    17,
    19,
    23,
    29,
    31,
    37,
    41,
    43,
    47,
    53,
    59,
    61,
    67,
    71,
    73,
    79,
)


@dataclass(frozen=True, slots=True)
class BranchChoiceSuffix:
    """Exact six-choice observer imported from the Mahler diamond research.

    Choices are one-based sibling indices, not q exponents. A caller must
    establish the legal menu and chosen edge separately. Neither this observer
    nor equality of its keys admits a source event or a safety verdict.
    """

    length: int = 0
    code: int = 0

    def __post_init__(self) -> None:
        if (
            type(self.length) is not int
            or type(self.code) is not int
            or not 0 <= self.length <= 6
            or not 0 <= self.code < 3**self.length
        ):
            raise ValueError("invalid bounded branch suffix")

    def then(self, later: BranchChoiceSuffix) -> BranchChoiceSuffix:
        """Chronological concatenation, keeping only the last six choices."""
        if type(later) is not BranchChoiceSuffix:
            raise TypeError("branch suffix composition requires the same observer")
        self.__post_init__()
        later.__post_init__()
        return BranchChoiceSuffix(
            min(6, self.length + later.length),
            (self.code * 3**later.length + later.code) % 729,
        )

    def append(self, choice: int) -> BranchChoiceSuffix:
        if type(choice) is not int or not 1 <= choice <= 3:
            raise ValueError("branch choice must be 1, 2 or 3")
        return self.then(BranchChoiceSuffix(1, choice - 1))

    def choices(self) -> tuple[int, ...]:
        self.__post_init__()
        return tuple(
            1 + (self.code // 3**position) % 3
            for position in reversed(range(self.length))
        )


def _validate_lane(family: PhaseFamily, prime: int) -> None:
    if type(family) is not str or family not in ("mahler", "collatz"):
        raise ValueError("unknown prime phase family")
    if type(prime) is not int or prime not in PRIME_BANK:
        raise ValueError("prime must belong to the declared finite observer bank")


def prime_lane_after(family: PhaseFamily, prime: int, before: int, q: int) -> int:
    """Exact lane of one supplied event; q is not independently chosen per lane."""
    _validate_lane(family, prime)
    if type(before) is not int or not 0 <= before < prime:
        raise ValueError("prime lane must be canonical")
    if type(q) is not int or q < 1:
        raise ValueError("positive common event exponent required")
    inverse_two = pow(2, -1, prime)
    phase = (
        pow(3 * inverse_two % prime, q, prime)
        if family == "mahler"
        else 3 * pow(inverse_two, q, prime) % prime
    )
    return (phase * before - 1) % prime


def possibility_partition(
    family: PhaseFamily,
    prime: int,
    ledger: ResourceLedger,
    *,
    max_phase_work: int = 1_000_000,
) -> tuple[int, ...]:
    """Finite refinement; equality preserves possible outputs, not an exact q."""
    workspace = PrimeBucketWorkspace(ledger, max_phase_work=max_phase_work)
    try:
        return workspace.partition(family, prime)
    finally:
        workspace.close()


class PrimeBucketWorkspace:
    """Bounded, ledger-owned reuse separated by the complete phase law."""

    def __init__(
        self, ledger: ResourceLedger, *, max_phase_work: int = 1_000_000
    ) -> None:
        if type(max_phase_work) is not int or max_phase_work < 1:
            raise ValueError("positive prime phase work budget required")
        self.ledger = ledger
        self.max_phase_work = max_phase_work
        self.work = 0
        self._closed = False
        owner = ledger.register(
            f"prime-possibility-{ledger.owner_count}", "finite phase partitions"
        )
        self._partitions: OwnedMemo[tuple[PhaseFamily, int], tuple[int, ...]] = (
            OwnedMemo(ledger, owner, nodes_per_entry=max(PRIME_BANK) + 4)
        )
        self._scratch = ledger.register(
            f"prime-possibility-scratch-{ledger.owner_count}", "refinement workspace"
        )

    def partition(self, family: PhaseFamily, prime: int) -> tuple[int, ...]:
        if self._closed:
            raise ValueError("closed prime possibility workspace")
        _validate_lane(family, prime)
        key = (family, prime)
        cached = self._partitions.get(key)
        if cached is not None:
            self.ledger.bump(f"{family}_prime_partition_hits")
            return cached
        # Phases and current labels each retain at most ``prime`` entries.
        # Reserve them before computing the phase bank. Each refinement round
        # separately reserves its transient class map and outcome masks.
        base_nodes = 2 * prime + 8
        self.ledger.reserve(self._scratch, nodes=base_nodes)
        try:
            if self.work + prime - 1 > self.max_phase_work:
                self.ledger.bump("prime_partition_work_refusals")
                raise BlockContextBudgetExceeded("prime phase work budget exceeded")
            self.work += prime - 1
            self.ledger.bump(f"{family}_prime_phase_construction", prime - 1)
            phases = tuple(
                sorted(
                    {
                        (prime_lane_after(family, prime, 1, q) + 1) % prime
                        for q in range(1, prime)
                    }
                )
            )
            labels = tuple(int(u != 0) for u in range(prime))
            for _ in range(prime + 1):
                cost = prime * len(phases)
                if self.work + cost > self.max_phase_work:
                    self.ledger.bump("prime_partition_work_refusals")
                    raise BlockContextBudgetExceeded("prime phase work budget exceeded")
                self.work += cost
                self.ledger.bump(f"{family}_prime_phase_visits", cost)
                # Each old label has four exact (death,birth) ports. Encoding
                # the set of such ports as a bitmask preserves equality of the
                # sorted-tuple signature and its first-encounter class IDs.
                # Charge the mask limbs using this round's actual label range;
                # no O(p^2) tuple of pairwise outcomes is retained.
                label_count = max(labels) + 1
                mask_limbs = (4 * label_count + 63) // 64
                round_nodes = (6 + mask_limbs) * prime + 8
                self.ledger.reserve(self._scratch, nodes=round_nodes)
                classes: dict[tuple[int, int], int] = {}
                result: list[int] = []
                try:
                    for u in range(prime):
                        outcomes = 0
                        for phase in phases:
                            v = (phase * u - 1) % prime
                            port = (
                                4 * labels[v]
                                + 2 * int(u != 0 and v == 0)
                                + int(u == 0 and v != 0)
                            )
                            outcomes |= 1 << port
                        signature = (labels[u], outcomes)
                        result.append(classes.setdefault(signature, len(classes)))
                    refined = tuple(result)
                finally:
                    classes.clear()
                    result.clear()
                    self.ledger.release(self._scratch, nodes=round_nodes)
                self.ledger.bump(f"{family}_prime_refinement_rounds")
                if refined == labels:
                    self._partitions[key] = refined
                    return refined
                labels = refined
            raise ArithmeticError("finite prime refinement failed to stabilize")
        finally:
            self.ledger.release(self._scratch, nodes=base_nodes)

    def close(self) -> None:
        if not self._closed:
            self._partitions.dispose()
            self.ledger.mark_disposed(self._scratch)
            self._closed = True
