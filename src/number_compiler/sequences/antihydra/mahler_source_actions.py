"""Exact occurrence actions consumed during the admitted arithmetic traversal.

Finite deck/safety/harmonic aliases are not keys for these coefficients. A
complete source cylinder and pinned consumer law qualify every reusable node.
Cold discovery belongs to the shared arithmetic walker, not this consumer.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd
from operator import add, lt, mul
from typing import TYPE_CHECKING, Final, Literal, Self, cast

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational,
    SaturatingAffineAction,
    compose_increasing_minplus_values,
)
from number_compiler.arithmetic.fields.homogeneous_growth import HomogeneousGrowthScale
from number_compiler.arithmetic.fields.radial_sturmian import RadialSturmianClock
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.arithmetic.fields.three_power_radix import (
    ThreePowerRadixOrbit,
)
from number_compiler.arithmetic.fields.walsh import walsh64_mod5
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicImageSummary,
    DyadicReturnSupportRecord,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.metric_keys import antihydra as _antihydra_keys
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
    from number_compiler.sequences.antihydra.mahler_joint_future import (
        MahlerJointInteriorWindow,
    )


# Trusted producer-path marker only; domain action admission remains local.
_SOURCE_ACTION_PUBLISHER = object()
MAX_MAHLER_SOURCE_EXTENT: Final[int] = 4096
_INTEGER_ROOT_ACTION_CACHE_VERSION: Final[str] = "integer-root-v2-publisher-qualified"
_CENTERED_PARITY_SAFETY_TAG: Final[str] = (
    "centered-parity-strict-margin-positive-infinity"
)


@dataclass(frozen=True, slots=True)
class MahlerSourceBoundSafetyAction:
    """min(C_hat/2^(R+2), (4*3^R*m+B_hat)/2^(R+2))."""

    extent: int = 0
    offset_hat: int = 0
    cap_hat: int | None = None

    def __post_init__(self) -> None:
        if type(self.extent) is not int or self.extent < 0:
            raise ValueError("Mahler action extent must be a natural integer")
        if self.extent > MAX_MAHLER_SOURCE_EXTENT:
            raise BlockContextBudgetExceeded("Mahler source extent exceeds hard limit")
        if type(self.offset_hat) is not int or (
            self.cap_hat is not None and type(self.cap_hat) is not int
        ):
            raise TypeError("Mahler normal form requires exact integer coefficients")
        if self.extent == 0:
            if self.offset_hat != 0 or self.cap_hat is not None:
                raise ValueError("zero-extent Mahler action must be identity")
        elif self.cap_hat is None:
            raise ValueError("nonempty Mahler source action requires a finite cap")

    @classmethod
    def one_bit(cls, epsilon: int) -> MahlerSourceBoundSafetyAction:
        """Return the exact source-normal-form action for one admitted bit.

        This is the same min-plus action used by the finite Mahler predicate:
        ``3/2 * (margin - epsilon)``, capped at ``9/4`` for zero and ``3/4``
        for one.  Keeping the bit action in the source-bound normal form lets
        consumers compose it with the scheduler's existing coefficient type.
        """
        if type(epsilon) is not int or epsilon not in (0, 1):
            raise ValueError("Mahler epsilon must be zero or one")
        # to_action divides offsets and caps by 2^(extent + 2) = 8 here.
        return cls(1, -12 * epsilon, 18 if epsilon == 0 else 6)

    def then_bit(
        self,
        epsilon: int,
        *,
        ledger: ResourceLedger | None = None,
    ) -> MahlerSourceBoundSafetyAction:
        """Compose one more exact bit through the common min-plus owner."""
        return self.then(self.one_bit(epsilon), ledger=ledger)

    def then(
        self,
        after: MahlerSourceBoundSafetyAction,
        *,
        ledger: ResourceLedger | None = None,
    ) -> MahlerSourceBoundSafetyAction:
        """Chronologically compose complete source-bound Mahler actions."""
        if type(after) is not MahlerSourceBoundSafetyAction:
            raise TypeError("Mahler composition requires another source-bound action")
        after.__post_init__()
        if self.extent + after.extent > MAX_MAHLER_SOURCE_EXTENT:
            raise BlockContextBudgetExceeded(
                "Mahler composition exceeds hard extent limit"
            )
        return self._then_with_authenticated_gain(after, 3**after.extent, ledger=ledger)

    def _then_with_authenticated_gain(
        self,
        after: MahlerSourceBoundSafetyAction,
        after_gain: int,
        *,
        ledger: ResourceLedger | None = None,
    ) -> MahlerSourceBoundSafetyAction:
        """Compose using the exact multiplier already carried by a joint action.

        This private path avoids rebuilding ``3**after.extent`` during source
        action powering.  Its caller is the checked joint-action owner, whose
        ``after_gain`` is validated together with the source cylinder.
        """
        if type(after) is not MahlerSourceBoundSafetyAction:
            raise TypeError("Mahler composition requires another source-bound action")
        if type(after_gain) is not int or after_gain < 1:
            raise ValueError("Mahler composition needs a positive exact multiplier")
        self.__post_init__()
        after.__post_init__()
        if self.extent + after.extent > MAX_MAHLER_SOURCE_EXTENT:
            raise BlockContextBudgetExceeded(
                "Mahler composition exceeds hard extent limit"
            )
        if not self.extent:
            return after
        if not after.extent:
            return self
        offset, cap = compose_increasing_minplus_values(
            self.offset_hat,
            self.cap_hat,
            after_gain,
            after.offset_hat << self.extent,
            None if after.cap_hat is None else after.cap_hat << self.extent,
            multiply=mul,
            add=add,
            less=lt,
        )
        result = MahlerSourceBoundSafetyAction(self.extent + after.extent, offset, cap)
        if ledger is not None:
            if type(ledger) is not ResourceLedger:
                raise TypeError("Mahler composition metrics require a query ledger")
            ledger.bump(_antihydra_keys.MAHLER_SOURCE_BOUND_COMPOSITIONS)
        return result

    def power(
        self,
        repetitions: int,
        *,
        max_coefficient_bits: int = 8192,
        ledger: ResourceLedger | None = None,
    ) -> MahlerSourceBoundSafetyAction:
        """Square a repeated admitted min-plus word within an explicit cap."""
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("Mahler repetitions must be a natural integer")
        if type(max_coefficient_bits) is not int or max_coefficient_bits < 1:
            raise ValueError("Mahler coefficient budget must be positive")
        if self.extent * repetitions > MAX_MAHLER_SOURCE_EXTENT:
            raise BlockContextBudgetExceeded("Mahler power exceeds hard extent limit")
        result = MahlerSourceBoundSafetyAction()
        factor = self
        remaining = repetitions
        while remaining:
            if remaining & 1:
                estimate = (
                    max(
                        result.extent + factor.extent,
                        abs(result.offset_hat).bit_length(),
                        abs(factor.offset_hat).bit_length(),
                        abs(result.cap_hat).bit_length()
                        if result.cap_hat is not None
                        else 0,
                        abs(factor.cap_hat).bit_length()
                        if factor.cap_hat is not None
                        else 0,
                    )
                    * 2
                )
                if estimate > max_coefficient_bits:
                    raise BlockContextBudgetExceeded(
                        "Mahler power exceeds its bit budget"
                    )
                result = result.then(factor, ledger=ledger)
            remaining >>= 1
            if remaining:
                estimate = (
                    max(
                        factor.extent,
                        abs(factor.offset_hat).bit_length(),
                        abs(factor.cap_hat).bit_length()
                        if factor.cap_hat is not None
                        else 0,
                    )
                    * 4
                )
                if estimate > max_coefficient_bits:
                    raise BlockContextBudgetExceeded(
                        "Mahler square exceeds its bit budget"
                    )
                factor = factor.then(factor, ledger=ledger)
        if ledger is not None:
            if type(ledger) is not ResourceLedger:
                raise TypeError("Mahler power metrics require a query ledger")
            ledger.bump(_antihydra_keys.MAHLER_SOURCE_BOUND_POWERS)
        return result

    def demanded_tripling_ports(
        self,
        *,
        base: int,
        places: int,
        walsh: bool = False,
        ledger: ResourceLedger | None = None,
        source: int | None = None,
        endpoint_h: int | None = None,
        binary_places: int = 16,
        decimal_places: int = 4,
        _workspace: object | None = None,
        _workspace_transfer: SkewTransfer[int] | None = None,
        _window_memo: OwnedMemo[tuple[object, ...], MahlerJointInteriorWindow]
        | None = None,
    ) -> dict[str, object]:
        """Demand homogeneous ports and, when supplied, a source-bound future.

        The finite successor selector is derived from the exact original
        source cylinder and its strict fractional guard. It remains an
        observer and does not authorize an Antihydra physical transition.
        """
        self.__post_init__()
        if self.extent < 1:
            raise ValueError("positive Mahler extent required for difference ports")
        if walsh and (base != 64 or places != 64):
            raise ValueError("Walsh64 requires 64 radix-64 positions")
        if _workspace is None:
            if endpoint_h is not None or _workspace_transfer is not None:
                raise ValueError("source endpoint requires a workspace-issued transfer")
        else:
            from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
            from number_compiler.sequences.antihydra.arithmetic_images import (
                AntihydraArithmeticImageWorkspace,
            )

            if (
                source != 7
                or type(endpoint_h) is not int
                or endpoint_h < 1
                or type(_workspace) is not AntihydraArithmeticImageWorkspace
                or type(_workspace_transfer) is not SkewTransfer
                or _workspace.returns != self.extent
            ):
                raise ValueError("root source detail requires its admitted transfer")
            endpoint_limit_bits = (
                max(
                    _workspace_transfer.upper.bit_length() + 4,
                    abs(_workspace_transfer.offset).bit_length(),
                )
                + 1
            )
            if endpoint_h.bit_length() > endpoint_limit_bits:
                raise ValueError("root endpoint exceeds its admitted transfer bound")
        if ledger is not None:
            if type(ledger) is not ResourceLedger:
                raise TypeError("Mahler radix-port metrics require a query ledger")
            ledger.bump(_antihydra_keys.MAHLER_RADIX_PORT_DEMANDS)
        orbit = ThreePowerRadixOrbit("ordinary", self.extent, base)
        ports = orbit.ordinary_ports(places)
        pivot = ports.difference_xor_mask
        # For this fixed two-step gap, 3**(R+2)-3**R is exactly 8*3**R,
        # with v2=3.  Reuse the last source residue already present in the
        # shared radix tape instead of launching a second modular power pass.
        modulus = base**places
        normalized = ports.tape[-1].source_remainder
        raw, valuation = (8 * normalized) % modulus, 3
        joint: dict[str, object] | None = None
        if source is not None:
            from number_compiler.sequences.antihydra.mahler_joint_future import (
                MahlerJointFutureAction,
                MahlerJointInteriorWindow,
            )

            if type(source) is not int or source < 0:
                raise ValueError(
                    "joint Mahler port requires a nonnegative integer source"
                )
            if _workspace is not None:
                assert endpoint_h is not None
                future = MahlerJointFutureAction._from_admitted_root_workspace(
                    _workspace, endpoint_h, self, _workspace_transfer
                )
            else:
                future = MahlerJointFutureAction.from_source_prefix(
                    source, self.extent, max_steps=4096
                )
                if future.safety != self:
                    raise ValueError(
                        "Mahler safety action is not from the source prefix"
                    )
            window_key = (
                future.semantic_id,
                source,
                binary_places,
                decimal_places,
            )
            if _window_memo is not None and _window_memo.ledger is not ledger:
                raise ValueError("Mahler window memo belongs to another ledger")
            cached_window = (
                None if _window_memo is None else _window_memo.get(window_key)
            )
            if cached_window is None:
                window = future.source_window(
                    source, bits=binary_places, decimal_places=decimal_places
                )
                window.verify_issued()
                if _window_memo is not None:
                    # This observer cache is a single-entry exact-demand memo.
                    # It is per source workspace, ledger-owned, and its key
                    # includes the full future action as well as precision.
                    _window_memo.clear()
                    _window_memo[window_key] = window
            else:
                if type(cached_window) is not MahlerJointInteriorWindow:
                    raise ValueError("Mahler observer memo contains another value")
                window = cached_window
                window.verify_issued()
                if (
                    window.source != source
                    or window.bits != binary_places
                    or window.decimal_places != decimal_places
                    or window.source_endpoint != future.endpoint(source)
                ):
                    raise ValueError("Mahler observer memo detached from its source")
            high_fiber = (source - future.residue) >> future.extent
            fiber_residue, fiber_modulus = future.interior_fiber_class(
                high_fiber, bits=binary_places, decimal_places=decimal_places
            )
            a5, b5, mod5 = future.five_adic_affine(decimal_places)
            if (a5 * source + b5) % mod5 != window.source_endpoint % mod5:
                raise ArithmeticError("5-adic temporal action detached from its source")
            joint = {
                "scope": "finite exact source-cylinder observer; no all-time authority",
                "source_residue": future.residue,
                "source_modulus": future.source_modulus,
                "innovation": future.innovation,
                "source_endpoint": window.source_endpoint,
                "interior_fiber_modulus": fiber_modulus,
                "interior_fiber_residue": fiber_residue,
                "interior_fiber_exact": True,
                "guard": (
                    (future.guard.lower.numerator, future.guard.lower.denominator),
                    (future.guard.upper.numerator, future.guard.upper.denominator),
                ),
                "guard_empty": future.guard.empty,
                "future_source_classes": tuple(
                    {
                        "epsilon": branch.epsilon,
                        "high_fiber_parity": branch.high_fiber_parity,
                        "source_residue": branch.action.residue,
                        "source_modulus": branch.action.source_modulus,
                        "guard": (
                            (
                                branch.action.guard.lower.numerator,
                                branch.action.guard.lower.denominator,
                            ),
                            (
                                branch.action.guard.upper.numerator,
                                branch.action.guard.upper.denominator,
                            ),
                        ),
                    }
                    for branch in future.successor_branches()
                ),
                "selected_next_bit": window.epsilon,
                "selected_next_source": window.next_source,
                "binary_next_low": window.next_binary,
                "binary_generate_mask": window.generate_mask,
                "binary_propagate_mask": window.propagate_mask,
                "binary_xor_mask": window.xor_mask,
                "binary_difference_borrows": window.binary_difference_borrows,
                "decimal_next_low": window.next_decimal,
                "decimal_difference_borrows": window.decimal_difference_borrows,
                "five_next_low": window.next_five,
                "five_adic_affine": (a5, b5, mod5),
                "five_primary_multiplier_period": (2 * 5 ** (decimal_places - 1))
                // gcd(2 * 5 ** (decimal_places - 1), future.extent),
                "counter_two_carry_contexts": window.counter.next_carries,
                "counter_walsh_h5": tuple(
                    (harmonic.phi2, harmonic.phi3_a, harmonic.phi3_b)
                    for harmonic in window.counter.harmonics
                ),
                "fraction_safety_claim": "none without a fractional witness",
                "all_time_claim": False,
            }
        elif (
            endpoint_h is not None
            or _workspace is not None
            or _workspace_transfer is not None
            or _window_memo is not None
        ):
            raise ValueError("endpoint/gain requires an authenticated original source")
        return {
            "source_extent": self.extent,
            "radial_scale": (self.extent, self.extent),
            "base": base,
            "places": places,
            "tripling_carries": ports.carry_word,
            "successive_innovation_borrows": ports.forward_borrow_mask,
            "difference_xor_mask": pivot,
            "dyadic_block_difference": (raw, valuation, normalized),
            "walsh64_mod5": walsh64_mod5(pivot) if walsh else None,
            "joint_source_successor": joint,
            "scope": (
                "source-bound finite successor and interior ports when a source is supplied; "
                "homogeneous otherwise"
            ),
        }

    @property
    def radial_sturmian_clock(self) -> RadialSturmianClock:
        """Scale for this admitted Mahler source action, without its offset."""
        self.__post_init__()
        return RadialSturmianClock(HomogeneousGrowthScale(self.extent, self.extent))

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
            tuple[DyadicReturnSupportRecord, MahlerSourceBoundSafetyAction, int],
        ] = OwnedMemo(ledger, owner, nodes_per_entry=3)
        self.lease: CacheLease | None = None
        cache = get_process_cache() if shared_cache else None
        if cache is not None and cache.enabled:
            try:
                self.lease = cache.acquire(
                    "mahler-source-bound-action",
                    _INTEGER_ROOT_ACTION_CACHE_VERSION,
                    cast(
                        tuple[ImmutableValue, ...],
                        (
                            MACHINE_SHA256,
                            law.descriptor,
                            _CENTERED_PARITY_SAFETY_TAG,
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
        cleanup_all(
            (self.records.dispose,)
            if self.lease is None
            else (self.records.dispose, self.lease.close)
        )

    def _check(
        self, node: DyadicReturnSupportRecord, action: MahlerSourceBoundSafetyAction
    ) -> None:
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

    def _checked_local_record(
        self,
        width: int,
        residue: int,
        record: object,
    ) -> tuple[DyadicReturnSupportRecord, MahlerSourceBoundSafetyAction, int]:
        """Validate the local memo key as well as its internally consistent payload."""
        if (
            type(record) is not tuple
            or len(record) != 3
            or type(record[0]) is not DyadicReturnSupportRecord
            or type(record[1]) is not MahlerSourceBoundSafetyAction
            or type(record[2]) is not int
            or record[2] < 0
        ):
            raise ValueError("local Mahler source action has another record sort")
        node, action, publisher = record
        self.count(
            "record_validation_operand_bits",
            width + residue.bit_length() + publisher.bit_length(),
        )
        if (
            node.width != width
            or node.residue != residue
            or publisher & ((1 << width) - 1) != residue
        ):
            raise ValueError("local Mahler source action belongs to another cylinder")
        self._check(node, action)
        return node, action, publisher

    def _store(
        self,
        node: DyadicReturnSupportRecord,
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
    ) -> DyadicReturnSupportRecord | None:
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
            try:
                node, _action, publisher = self._checked_local_record(
                    width, residue, local
                )
            except (TypeError, ValueError):
                self.count("source_action_admission_rejections")
                self.count("failed_work")
                raise
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
                or found[8] is not None
                and type(found[8]) is not int
                or any(type(part) is not int for part in found[9:])
            ):
                raise TypeError("Mahler occurrence cache contains another record sort")
            record_payload = cast(
                tuple[
                    int, int, int, int, int, int, int, int, int | None, int, int, int
                ],
                found,
            )
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
            ) = record_payload
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
            node = DyadicReturnSupportRecord(
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

    def normal_action(self, width: int, residue: int) -> MahlerSourceBoundSafetyAction:
        """Return the exact action from a successful lookup, without replay."""
        if (
            type(width) is not int
            or width <= 0
            or type(residue) is not int
            or residue < 0
            or residue.bit_length() > width
        ):
            raise ValueError("Mahler action lookup requires an exact source cylinder")
        record = self.records.get((width, residue))
        if record is None:
            raise KeyError("Mahler action was not admitted in this occurrence")
        _node, action, _publisher = self._checked_local_record(width, residue, record)
        return action

    def publish_action(
        self,
        summary: DyadicImageSummary,
        action: MahlerSourceBoundSafetyAction,
        *,
        publisher: int,
    ) -> None:
        """Publish a scheduler-composed normal form under its exact image."""
        if type(summary) is not DyadicImageSummary:
            raise TypeError("Mahler action publication needs its exact image summary")
        if type(action) is not MahlerSourceBoundSafetyAction:
            raise TypeError("Mahler action publication has another normal form")
        node = DyadicReturnSupportRecord(
            summary.width,
            summary.residue,
            summary.transfer,
            summary.odd_steps,
            summary.delta,
            summary.minimum,
            None,
            None,
            summary.cycle,
            True,
        )
        self._store(node, action, publisher)

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
        node = DyadicReturnSupportRecord(
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
