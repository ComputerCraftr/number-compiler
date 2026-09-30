"""Exact occurrence actions consumed during the admitted arithmetic traversal.

Finite deck/safety/harmonic aliases are not keys for these coefficients. A
complete source cylinder and pinned consumer law qualify every reusable node.
Cold discovery belongs to the shared arithmetic walker, not this consumer.
"""

from __future__ import annotations

from dataclasses import dataclass
from operator import add, lt, mul
from typing import TYPE_CHECKING, Literal, Self, cast

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational,
    SaturatingAffineAction,
    compose_increasing_minplus_values,
)
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicImageSummary,
    _SupportNode,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.process_cache import (
    MISSING,
    CacheLease,
    CacheRecordIssuerMismatch,
    ImmutableValue,
    get_process_cache,
)
from number_compiler.sequences.antihydra.machine import MACHINE_SHA256

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_records import DyadicReturnLaw


# Trusted producer-path marker only; domain action admission remains local.
_SOURCE_ACTION_PUBLISHER = object()


@dataclass(frozen=True, slots=True)
class MahlerSourceBoundSafetyAction:
    """min(C_hat/2^(R+2), (4*3^R*m+B_hat)/2^(R+2))."""

    extent: int = 0
    offset_hat: int = 0
    cap_hat: int | None = None

    def __post_init__(self) -> None:
        if type(self.extent) is not int or self.extent < 0:
            raise ValueError("Mahler action extent must be a natural integer")
        if type(self.offset_hat) is not int or (
            self.cap_hat is not None and type(self.cap_hat) is not int
        ):
            raise TypeError("Mahler normal form requires exact integer coefficients")
        if self.extent == 0:
            if self.offset_hat != 0 or self.cap_hat is not None:
                raise ValueError("zero-extent Mahler action must be identity")
        elif self.cap_hat is None:
            raise ValueError("nonempty Mahler source action requires a finite cap")

    def then_with_gain(
        self, after: MahlerSourceBoundSafetyAction, gain: int
    ) -> MahlerSourceBoundSafetyAction:
        if type(after) is not MahlerSourceBoundSafetyAction:
            raise TypeError("Mahler normal forms require their exact action sort")
        self.__post_init__()
        after.__post_init__()
        if type(gain) is not int or gain <= 0:
            raise ValueError("Mahler admitted downstream gain must be positive")
        offset, cap = compose_increasing_minplus_values(
            self.offset_hat,
            self.cap_hat,
            gain,
            after.offset_hat << self.extent,
            None if after.cap_hat is None else after.cap_hat << self.extent,
            multiply=mul,
            add=add,
            less=lt,
        )
        return MahlerSourceBoundSafetyAction(self.extent + after.extent, offset, cap)

    def to_action(self) -> SaturatingAffineAction:
        self.__post_init__()
        denominator = 1 << (self.extent + 2)
        return SaturatingAffineAction(
            ExactRational(3**self.extent, 1 << self.extent),
            ExactRational(self.offset_hat, denominator),
            None if self.cap_hat is None else ExactRational(self.cap_hat, denominator),
        )

    def wire(self) -> tuple[int, int, int | None]:
        self.__post_init__()
        return self.extent, self.offset_hat, self.cap_hat


class MahlerOccurrenceConsumer:
    """Owned transient results and bounded shared, complete occurrence records."""

    def __init__(
        self,
        ledger: ResourceLedger,
        law: DyadicReturnLaw,
        *,
        shared_cache: bool,
        counter_family: Literal["mahler", "antihydra"] = "mahler",
    ) -> None:
        if law.gains != (3, 3) or law.offsets != (0, -1):
            raise ValueError("Mahler consumer requires its pinned arithmetic law")
        if type(shared_cache) is not bool:
            raise TypeError("shared_cache must be a bool")
        if counter_family not in ("mahler", "antihydra"):
            raise ValueError("source-action counter family must be Mahler or Antihydra")
        self.ledger = ledger
        self.law = law
        self.counter_prefix = f"{counter_family}_hashlife_"
        for metric in (
            "source_action_lookups",
            "source_action_exact_hits",
            "source_action_transported_hits",
            "source_action_local_hits",
            "source_action_process_hits",
            "source_action_misses",
            "source_action_publications",
            "source_action_applied_hits",
            "source_action_applied_parent_hits",
            "source_action_admission_rejections",
            "source_action_bypasses",
            "source_action_disabled_bypasses",
            "failed_work",
        ):
            self.ledger.bump(self.counter_prefix + metric, 0)
        owner = ledger.register(
            f"mahler-source-action-construction-{len(ledger.inventory())}",
            "arithmetic_workspace",
        )
        self.records: OwnedMemo[
            tuple[int, int],
            tuple[_SupportNode, MahlerSourceBoundSafetyAction, int],
        ] = OwnedMemo(ledger, owner, nodes_per_entry=3)
        self.lease: CacheLease | None = None
        cache = get_process_cache() if shared_cache else None
        if cache is not None and cache.enabled:
            try:
                self.lease = cache.acquire(
                    "mahler-source-bound-action",
                    "integer-root-v2-publisher-qualified",
                    cast(
                        tuple[ImmutableValue, ...],
                        (
                            MACHINE_SHA256,
                            law.descriptor,
                            "centered-parity-strict-margin-positive-infinity",
                        ),
                    ),
                )
            except BlockContextBudgetExceeded:
                self.count("source_action_bypasses")
        else:
            self.count("source_action_disabled_bypasses")

    def __enter__(self) -> Self:
        return self

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> None:
        self.close()

    def count(self, suffix: str, amount: int = 1) -> None:
        self.ledger.bump(self.counter_prefix + suffix, amount)

    def close(self) -> None:
        try:
            self.records.dispose()
        finally:
            if self.lease is not None:
                self.lease.close()

    def _check(self, node: _SupportNode, action: MahlerSourceBoundSafetyAction) -> None:
        """Check consumer consistency, not re-prove the issued source recurrence.

        The transfer, odd count and ledger minimum originate in the admitted
        arithmetic constructor. Correlated changes to all these fields cannot
        be authenticated by their mutual consistency. Their provenance is the
        private producer capability; complete constructor refinement is a
        separate proof obligation, not work replayed on a cache hit.
        """
        action.__post_init__()
        self.count(
            "admission_operand_bits",
            node.transfer.upper.bit_length()
            + abs(node.transfer.offset).bit_length()
            + node.transfer.lower.bit_length()
            + abs(action.offset_hat).bit_length(),
        )
        if action.extent != node.width or action.offset_hat != -12 * (
            node.transfer.upper + node.transfer.offset - node.transfer.lower
        ):
            raise ValueError("Mahler occurrence lost its admitted affine transfer")
        if (
            node.width < 2
            or node.residue & 3
            or action.cap_hat is None
            or action.cap_hat >= 0
            or action.cap_hat != 6 * node.transfer.upper + action.offset_hat
        ):
            raise ValueError("Mahler occurrence lost its centered-11 safety cap")

    def _store(
        self,
        node: _SupportNode,
        action: MahlerSourceBoundSafetyAction,
        publisher: int,
    ) -> None:
        self._check(node, action)
        if type(publisher) is not int or publisher < 0:
            raise ValueError("Mahler occurrence publisher must be a natural integer")
        if publisher & ((1 << node.width) - 1) != node.residue:
            raise ValueError("Mahler occurrence publisher differs from its source germ")
        self.count("publication_operand_bits", publisher.bit_length())
        key = node.width, node.residue
        self.records[key] = node, action, publisher
        # No wide branch word or endpoint is retained in the process cache.
        wire: tuple[ImmutableValue, ...] = (
            node.width,
            node.residue,
            node.transfer.upper,
            node.transfer.offset,
            node.transfer.lower,
            node.odd_steps,
            node.delta,
            node.minimum,
            node.branch_word if node.width <= 8 else None,
            action.offset_hat,
            action.cap_hat,
            publisher,
        )
        if self.lease is not None and not self.lease.put_issued(
            ("gain", node.width), node.transfer.upper, _SOURCE_ACTION_PUBLISHER
        ):
            self.count("source_action_bypasses")
        if self.lease is not None:
            if self.lease.put_issued(key, wire, _SOURCE_ACTION_PUBLISHER):
                self.count("source_action_publications")
            else:
                self.count("source_action_bypasses")

    def lookup(
        self, width: int, residue: int, *, source: int | None = None
    ) -> _SupportNode | None:
        if (
            type(width) is not int
            or width <= 0
            or type(residue) is not int
            or residue < 0
            or residue.bit_length() > width
        ):
            raise ValueError("Mahler lookup requires a complete exact source cylinder")
        if source is None:
            source = residue
        if type(source) is not int or source < 0:
            raise ValueError("Mahler lookup source must be a natural integer")
        if source & ((1 << width) - 1) != residue:
            raise ValueError("Mahler lookup source differs from its exact cylinder")
        self.count("source_action_lookups")
        self.count(
            "key_operand_bits",
            width.bit_length() + residue.bit_length() + source.bit_length(),
        )
        key = width, residue
        local = self.records.get(key)
        if local is not None:
            node, action, publisher = local
            self._check(node, action)
            self._retrieved(source, publisher, "local")
            return node
        found: object = MISSING
        if self.lease is None:
            found = MISSING
        else:
            try:
                found = self.lease.get_issued(key, _SOURCE_ACTION_PUBLISHER)
            except CacheRecordIssuerMismatch:
                self.count("source_action_admission_rejections")
                self.count("failed_work")
                raise
        if found is MISSING:
            self.count("source_action_misses")
            return None
        try:
            if (
                type(found) is not tuple
                or len(found) != 12
                or any(type(part) is not int for part in found[:8])
            ):
                raise TypeError("Mahler occurrence cache contains another record sort")
            (
                w,
                r,
                upper,
                offset,
                lower,
                odd,
                delta,
                minimum,
                word,
                b_hat,
                c_hat,
                publisher,
            ) = found
            if type(publisher) is not int or publisher < 0:
                raise TypeError("Mahler cached publisher must be a natural integer")
            self.count(
                "record_validation_operand_bits",
                abs(upper).bit_length()
                + abs(offset).bit_length()
                + abs(lower).bit_length()
                + publisher.bit_length(),
            )
            try:
                gain = (
                    MISSING
                    if self.lease is None
                    else self.lease.get_issued(
                        ("gain", width), _SOURCE_ACTION_PUBLISHER
                    )
                )
            except CacheRecordIssuerMismatch:
                self.count("source_action_admission_rejections")
                self.count("failed_work")
                raise
            if gain is MISSING:
                gain = 3**width
                self.count("gain_validation_operand_bits", gain.bit_length())
                if self.lease is not None and not self.lease.put_issued(
                    ("gain", width), gain, _SOURCE_ACTION_PUBLISHER
                ):
                    self.count("source_action_bypasses")
            if type(gain) is not int or gain <= 0:
                raise ValueError("Mahler cached level gain has another sort")
            if (
                w != width
                or r != residue
                or upper != gain
                or lower <= 0
                or lower.bit_length() != width + 1
                or lower.bit_count() != 1
                or not 0 <= odd <= width
                or delta != 2 * width - 3 * odd
                or minimum > min(0, delta)
                or (width > 8 and word is not None)
                or (
                    width <= 8 and (type(word) is not int or not 0 <= word < 1 << width)
                )
                or type(b_hat) is not int
                or type(c_hat) is not int
                or publisher & ((1 << width) - 1) != residue
            ):
                raise ValueError(
                    "Mahler cached occurrence has another source/action domain"
                )
            node = _SupportNode(
                width,
                residue,
                SkewTransfer(upper, offset, lower),
                odd,
                delta,
                minimum,
                word,
                None,
                None,
                width > 8,
            )
            action = MahlerSourceBoundSafetyAction(width, b_hat, c_hat)
            self._check(node, action)
        except CacheRecordIssuerMismatch:
            raise
        except (TypeError, ValueError):
            self.count("source_action_admission_rejections")
            self.count("failed_work")
            raise
        try:
            self.records[key] = node, action, publisher
        except BlockContextBudgetExceeded:
            self.count("source_action_admission_rejections")
            self.count("failed_work")
            raise
        self._retrieved(source, publisher, "process")
        return node

    def _retrieved(self, source: int, publisher: int, location: str) -> None:
        self.count(f"source_action_{location}_hits")
        self.count(
            "source_action_exact_hits"
            if source == publisher
            else "source_action_transported_hits"
        )

    def applied(self, *, parent: bool) -> None:
        """Record cache reuse only after its exact candidate was published."""
        self.count("source_action_applied_hits")
        if parent:
            self.count("source_action_applied_parent_hits")

    def publish_root(self, summary: DyadicImageSummary, *, publisher: int) -> None:
        """Derive the pinned centered-11 root predicate from admitted arithmetic."""
        if summary.width < 2 or summary.residue & 3:
            raise ValueError("Mahler root requires its admitted centered 11 prefix")
        transfer = summary.transfer
        offset = -12 * (transfer.upper + transfer.offset - transfer.lower)
        cap = 6 * transfer.upper + offset
        if cap >= 0:
            raise ValueError("Mahler root cap lost its two-bit failure")
        node = _SupportNode(
            summary.width,
            summary.residue,
            transfer,
            summary.odd_steps,
            summary.delta,
            summary.minimum,
            None,
            None,
            None,
            True,
        )
        self._store(
            node,
            MahlerSourceBoundSafetyAction(summary.width, offset, cap),
            publisher,
        )
