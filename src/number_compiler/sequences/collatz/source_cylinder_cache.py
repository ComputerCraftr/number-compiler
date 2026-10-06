"""Bounded, source-qualified normalized Collatz dyadic cylinder macros.

A width-w occurrence owns its complete low-w source germ. Its affine action
is target_origin + 3**odd_symbols * high_fiber. The live run producer supplies
proved cylinder coefficients; cache lookup admits the complete source germ.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Self

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.process_cache import (
    MISSING,
    CacheRecordIssuerMismatch,
    get_process_cache,
)
from number_compiler.sequences.collatz.tape_width import (
    CollatzTapeWidthSummary,
    compose_width_ledger,
)

# Trusted producer-path marker only; CacheLease does not prove Collatz semantics.
_OCCURRENCE_PUBLISHER = object()
_GAIN_PUBLISHER = object()
_WIDTH_SPINE_PUBLISHER = object()


def _canonical_gain(odd_symbols: int) -> int:
    """Return a trusted exact gain; callers charge each construction."""
    if type(odd_symbols) is not int or odd_symbols < 0:
        raise ValueError("Collatz odd-symbol count must be a natural integer")
    return int(3**odd_symbols)


def _low_residue(value: int, width: int) -> int:
    """Return low-width bits without allocating a mask wider than the value."""
    if width >= value.bit_length():
        return value
    return value & ((1 << width) - 1)


def _admit_source_key(source: int, width: int) -> tuple[int, int]:
    """Validate one source germ and return its residue and actual key size."""
    if type(source) is not int or source <= 0:
        raise ValueError("Collatz macro source must be positive")
    if type(width) is not int or width < 8 or width & (width - 1):
        raise ValueError("Collatz macro width must be dyadic and at least eight")
    return _low_residue(source, width), source.bit_length() + width.bit_length()


@dataclass(frozen=True, slots=True, init=False)
class _CanonicalGain:
    """An exact Collatz gain tied to the exponent that produced it.

    Normal construction computes the power. Cache rehydration is private and
    follows exact issuer, payload-shape, and exponent checks.
    """

    odd_symbols: int
    multiplier: int

    def __init__(self, odd_symbols: int) -> None:
        if type(odd_symbols) is not int or odd_symbols < 0:
            raise ValueError("Collatz gain exponent must be natural")
        object.__setattr__(self, "odd_symbols", odd_symbols)
        object.__setattr__(self, "multiplier", _canonical_gain(odd_symbols))

    @classmethod
    def _from_issued_payload(cls, odd_symbols: int, multiplier: int) -> _CanonicalGain:
        if (
            type(odd_symbols) is not int
            or odd_symbols < 0
            or type(multiplier) is not int
            or multiplier <= 0
        ):
            raise ValueError("Collatz canonical gain cache is malformed")
        gain = object.__new__(cls)
        object.__setattr__(gain, "odd_symbols", odd_symbols)
        object.__setattr__(gain, "multiplier", multiplier)
        return gain


@dataclass(frozen=True, slots=True)
class CollatzDyadicOccurrence:
    width: int
    residue: int
    odd_symbols: int
    target_origin: int
    multiplier: int

    def __post_init__(self) -> None:
        self._validate(None)
        self._validate(_canonical_gain(self.odd_symbols))

    def _validate(self, canonical_gain: int | None) -> None:
        if any(
            type(value) is not int
            for value in (
                self.width,
                self.residue,
                self.odd_symbols,
                self.target_origin,
                self.multiplier,
            )
        ):
            raise TypeError("Collatz occurrence coordinates require exact integers")
        if self.width < 8 or self.width & (self.width - 1):
            raise ValueError("Collatz occurrence width must be dyadic")
        if (
            self.residue < 0
            or self.residue.bit_length() > self.width
            or not 0 <= self.odd_symbols <= self.width
        ):
            raise ValueError("Collatz occurrence germ or odd count is invalid")
        if self.multiplier <= 0 or not 0 <= self.target_origin < self.multiplier:
            raise ValueError("Collatz occurrence centered coefficients are invalid")
        if canonical_gain is not None and self.multiplier != canonical_gain:
            raise ValueError("Collatz occurrence centered coefficients are invalid")

    @classmethod
    def _from_gain(
        cls,
        width: int,
        residue: int,
        odd_symbols: int,
        target_origin: int,
        gain: _CanonicalGain,
    ) -> CollatzDyadicOccurrence:
        if (
            type(gain) is not _CanonicalGain
            or type(odd_symbols) is not int
            or gain.odd_symbols != odd_symbols
            or type(gain.multiplier) is not int
            or gain.multiplier <= 0
        ):
            raise ValueError("Collatz occurrence has invalid canonical gain")
        occurrence = object.__new__(cls)
        object.__setattr__(occurrence, "width", width)
        object.__setattr__(occurrence, "residue", residue)
        object.__setattr__(occurrence, "odd_symbols", odd_symbols)
        object.__setattr__(occurrence, "target_origin", target_origin)
        object.__setattr__(occurrence, "multiplier", gain.multiplier)
        occurrence._validate(gain.multiplier)
        return occurrence

    def apply(self, source: int) -> int:
        if type(source) is not int or source < 0:
            raise ValueError("Collatz cylinder needs a nonnegative exact source")
        if _low_residue(source, self.width) != self.residue:
            raise ValueError("Collatz cylinder source germ differs")
        return self.target_origin + self.multiplier * (source >> self.width)


class CollatzDyadicMacros:
    """Ledger-owned bounded local records with optional bounded cross-query reuse."""

    LIMIT = 4096
    MAX_INTERIOR_RECORDS = 64
    VERSION = "collatz-normalized-cylinder-v3-fiber-gain"
    GAIN_VERSION = "exact-v2-exponent-payload"
    GAIN_LIMIT = 4096
    WIDTH_SPINE_LIMIT = 4096
    WIDTH_SPINE_VERSION = "collatz-exact-source-width-spine-v1"

    def __init__(self, ledger: ResourceLedger, *, shared_cache: bool = False) -> None:
        if type(ledger) is not ResourceLedger or type(shared_cache) is not bool:
            raise TypeError("Collatz macros require a ledger and Boolean cache flag")
        self.ledger = ledger
        self._closed = False
        self._bump("primitive_steps", 0)
        for metric in (
            "occurrence_lookups",
            "occurrence_exact_hits",
            "occurrence_transported_hits",
            "occurrence_local_hits",
            "occurrence_process_hits",
            "occurrence_misses",
            "occurrence_publications",
            "occurrence_bypasses",
            "occurrence_disabled_bypasses",
            "occurrence_evictions",
            "occurrence_applied_hits",
            "occurrence_applied_parent_hits",
            "occurrence_rejected_fit",
            "occurrence_admission_rejections",
            "failed_work",
            "gain_operand_bits",
            "gain_local_hits",
            "gain_process_hits",
            "gain_key_operand_bits",
            "gain_construction_operand_bits",
            "gain_validation_operand_bits",
            "gain_bypasses",
            "gain_evictions",
            "width_spine_lookups",
            "width_spine_local_hits",
            "width_spine_process_hits",
            "width_spine_misses",
            "width_spine_publications",
            "width_spine_bypasses",
            "width_spine_evictions",
            "width_spine_admission_rejections",
            "width_spine_key_operand_bits",
            "width_spine_payload_operand_bits",
        ):
            self._bump(metric, 0)
        self.shared_cache = shared_cache
        self._interior_records = 0
        prefix = f"collatz-dyadic-{ledger.owner_count}"
        self.occurrences: OwnedMemo[
            tuple[int, int], tuple[CollatzDyadicOccurrence, int]
        ] = OwnedMemo(
            ledger,
            ledger.register(prefix + "-occurrences", "query_memo"),
            evictable=True,
            nodes_per_entry=2,
        )
        self.width_spines: OwnedMemo[tuple[int, int, int], CollatzTapeWidthSummary] = (
            OwnedMemo(
                ledger,
                ledger.register(prefix + "-exact-width-spines", "query_memo"),
                evictable=True,
                nodes_per_entry=10,
            )
        )
        self.gains: OwnedMemo[int, _CanonicalGain] = OwnedMemo(
            ledger,
            ledger.register(prefix + "-gains", "query_memo"),
            evictable=True,
        )
        # A binary frontier of already executed, adjacent source occurrences.
        # Endpoints are transient construction data, never shared-cache identity.
        self.frontier: OwnedMemo[
            int, tuple[int, int, CollatzTapeWidthSummary | None]
        ] = OwnedMemo(
            ledger,
            ledger.register(prefix + "-frontier", "execution_stack"),
            nodes_per_entry=10,
        )
        ledger.register_execution_root(self)

    def __enter__(self) -> Self:
        self._check_open()
        return self

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> None:
        if self._closed:
            return
        self._closed = True
        self.occurrences.dispose()
        self.width_spines.dispose()
        self.gains.dispose()
        self.frontier.dispose()

    def _check_open(self) -> None:
        if self._closed:
            raise RuntimeError("Collatz dyadic macros are closed")

    def _bump(self, suffix: str, amount: int = 1) -> None:
        self._check_open()
        self.ledger.bump("collatz_hashlife_" + suffix, amount)

    def _retain_gain(self, gain: _CanonicalGain) -> None:
        if gain.odd_symbols not in self.gains and len(self.gains) >= self.GAIN_LIMIT:
            del self.gains[next(iter(self.gains))]
            self._bump("gain_evictions")
        try:
            self.gains[gain.odd_symbols] = gain
        except BlockContextBudgetExceeded:
            # The gain is still available as a temporary certified value for
            # this occurrence; retaining it is an optional query-memo benefit.
            self._bump("gain_bypasses")

    def _gain(self, odd_symbols: int) -> _CanonicalGain:
        self._check_open()
        if type(odd_symbols) is not int or odd_symbols < 0:
            raise ValueError("Collatz gain exponent must be natural")
        self._bump("gain_key_operand_bits", odd_symbols.bit_length())
        found = self.gains.get(odd_symbols)
        if found is not None:
            if (
                type(found) is not _CanonicalGain
                or found.odd_symbols != odd_symbols
                or type(found.multiplier) is not int
                or found.multiplier <= 0
            ):
                raise ValueError("Collatz local canonical gain is malformed")
            self._bump("gain_local_hits")
            return found
        cache = get_process_cache()
        if self.shared_cache and not cache.enabled:
            self._bump("gain_bypasses")
        if self.shared_cache and cache.enabled:
            try:
                lease = cache.acquire(
                    "collatz-power-of-three", self.GAIN_VERSION, (odd_symbols,)
                )
            except BlockContextBudgetExceeded:
                self._bump("gain_bypasses")
            else:
                with lease:
                    value = lease.get_issued(("gain",), _GAIN_PUBLISHER)
                    if value is not MISSING:
                        if (
                            type(value) is not tuple
                            or len(value) != 2
                            or type(value[0]) is not int
                            or value[0] != odd_symbols
                            or type(value[1]) is not int
                            or value[1] <= 0
                        ):
                            raise ValueError(
                                "Collatz canonical gain cache is malformed"
                            )
                        gain = _CanonicalGain._from_issued_payload(*value)
                        self._retain_gain(gain)
                        self._bump("gain_process_hits")
                        return gain
                    gain = self._construct_gain(odd_symbols)
                    if not lease.put_issued(
                        ("gain",),
                        (odd_symbols, gain.multiplier),
                        _GAIN_PUBLISHER,
                    ):
                        self._bump("gain_bypasses")
                    return gain
        return self._construct_gain(odd_symbols)

    def _construct_gain(self, odd_symbols: int) -> _CanonicalGain:
        gain = _CanonicalGain(odd_symbols)
        self._bump("gain_operand_bits", gain.multiplier.bit_length())
        self._bump("gain_construction_operand_bits", gain.multiplier.bit_length())
        self._retain_gain(gain)
        return gain

    def _publish(
        self, occurrence: CollatzDyadicOccurrence, publisher_fiber: int
    ) -> CollatzDyadicOccurrence:
        self._check_open()
        if type(publisher_fiber) is not int or publisher_fiber < 0:
            raise ValueError("Collatz occurrence publisher fiber must be natural")
        self._bump(
            "operand_bits",
            occurrence.residue.bit_length()
            + occurrence.target_origin.bit_length()
            + occurrence.multiplier.bit_length()
            + publisher_fiber.bit_length(),
        )
        if (occurrence.width, occurrence.residue) not in self.occurrences and len(
            self.occurrences
        ) >= self.LIMIT:
            del self.occurrences[next(iter(self.occurrences))]
            self._bump("occurrence_evictions")
        self.occurrences[occurrence.width, occurrence.residue] = (
            occurrence,
            publisher_fiber,
        )
        self._bump("occurrence_publications")
        level = occurrence.width.bit_length() - 1
        previous = self.ledger.counters.get("collatz_hashlife_max_level", 0)
        self._bump("max_level", max(0, level - previous))
        return occurrence

    def lookup(self, source: int, width: int) -> CollatzDyadicOccurrence | None:
        self._check_open()
        residue, key_bits = _admit_source_key(source, width)
        # The low-width slice forms the lookup key; the full source also
        # classifies an exact publisher match versus a transported fiber.
        self._bump("key_operand_bits", key_bits)
        self._bump("occurrence_lookups")
        local = self.occurrences.get((width, residue))
        if local is not None:
            try:
                if not (
                    type(local) is tuple
                    and len(local) == 2
                    and type(local[0]) is CollatzDyadicOccurrence
                    and type(local[1]) is int
                    and local[1] >= 0
                    and local[0].width == width
                    and local[0].residue == residue
                ):
                    raise ValueError("Collatz local occurrence record is malformed")
                found, publisher_fiber = local
            except (TypeError, ValueError):
                self._bump("occurrence_admission_rejections")
                self._bump("failed_work")
                raise
            self._retrieved(source, width, publisher_fiber, "local")
            return found
        if self.shared_cache:
            cache = get_process_cache()
            if not cache.enabled:
                self._bump("occurrence_disabled_bypasses")
                self._bump("occurrence_misses")
                return None
            try:
                lease = cache.acquire(
                    "collatz-dyadic-occurrence", self.VERSION, (width, residue)
                )
            except BlockContextBudgetExceeded:
                self._bump("occurrence_bypasses")
                self._bump("occurrence_misses")
                return None
            with lease:
                try:
                    payload = lease.get_issued(("effect",), _OCCURRENCE_PUBLISHER)
                except CacheRecordIssuerMismatch:
                    self._bump("occurrence_admission_rejections")
                    self._bump("failed_work")
                    raise
                if payload is not MISSING:
                    try:
                        if not (
                            type(payload) is tuple
                            and len(payload) == 4
                            and all(type(item) is int for item in payload)
                        ):
                            raise ValueError(
                                "Collatz shared occurrence payload is invalid"
                            )
                        ones, origin, gain, publisher_fiber = payload
                        if not 0 <= ones <= width or publisher_fiber < 0:
                            raise ValueError(
                                "Collatz shared occurrence has an invalid gain key"
                            )
                        canonical_gain = self._gain(ones)
                        self._bump(
                            "gain_validation_operand_bits",
                            canonical_gain.multiplier.bit_length() + gain.bit_length(),
                        )
                        if gain != canonical_gain.multiplier:
                            raise ValueError("Collatz shared occurrence gain differs")
                        self._bump(
                            "gain_validation_operand_bits",
                            ones.bit_length() + canonical_gain.multiplier.bit_length(),
                        )
                        found = CollatzDyadicOccurrence._from_gain(
                            width,
                            residue,
                            ones,
                            origin,
                            canonical_gain,
                        )
                        self._bump(
                            "operand_bits",
                            gain.bit_length()
                            + origin.bit_length()
                            + width
                            + publisher_fiber.bit_length(),
                        )
                    except (TypeError, ValueError, BlockContextBudgetExceeded):
                        self._bump("occurrence_admission_rejections")
                        self._bump("failed_work")
                        raise
                    try:
                        result = self._publish(found, publisher_fiber)
                    except BlockContextBudgetExceeded:
                        self._bump("occurrence_admission_rejections")
                        self._bump("failed_work")
                        raise
                    self._retrieved(source, width, publisher_fiber, "process")
                    return result
        else:
            self._bump("occurrence_disabled_bypasses")
        self._bump("occurrence_misses")
        return None

    def _retrieved(
        self, source: int, width: int, publisher_fiber: int, location: str
    ) -> None:
        self._check_open()
        self._bump(f"occurrence_{location}_hits")
        self._bump(
            "occurrence_exact_hits"
            if source >> width == publisher_fiber
            else "occurrence_transported_hits"
        )

    def applied(self) -> None:
        """Called only after the admitted cached block advances the caller."""
        self._check_open()
        self._bump("occurrence_applied_hits")
        self._bump("occurrence_applied_parent_hits")

    def rejected_fit(self) -> None:
        self._check_open()
        self._bump("occurrence_rejected_fit")

    def _share(self, source: int, found: CollatzDyadicOccurrence) -> None:
        self._check_open()
        if self.shared_cache:
            cache = get_process_cache()
            if not cache.enabled:
                self._bump("occurrence_disabled_bypasses")
                return
            try:
                lease = cache.acquire(
                    "collatz-dyadic-occurrence",
                    self.VERSION,
                    (found.width, found.residue),
                )
            except BlockContextBudgetExceeded:
                self._bump("occurrence_bypasses")
                return
            with lease:
                if not lease.put_issued(
                    ("effect",),
                    (
                        found.odd_symbols,
                        found.target_origin,
                        found.multiplier,
                        source >> found.width,
                    ),
                    _OCCURRENCE_PUBLISHER,
                ):
                    self._bump("occurrence_bypasses")

    def remember(
        self,
        source: int,
        width: int,
        ones: int,
        endpoint: int,
        *,
        tape_width_summary: CollatzTapeWidthSummary | None = None,
    ) -> bool:
        self._check_open()
        residue, key_bits = _admit_source_key(source, width)
        if type(ones) is not int or not 0 <= ones <= width:
            raise ValueError("Collatz macro odd count is invalid")
        if tape_width_summary is not None:
            self._validate_width_summary(tape_width_summary, source, width)
            if (
                tape_width_summary.odd_steps != ones
                or tape_width_summary.target_width != endpoint.bit_length()
            ):
                raise ValueError("Collatz width spine differs from occurrence action")
        self._bump("key_operand_bits", key_bits)
        if (width, residue) in self.occurrences:
            if tape_width_summary is not None:
                self._remember_exact_width(source, width, tape_width_summary)
            return False
        try:
            gain = self._gain(ones)
        except (CacheRecordIssuerMismatch, ValueError):
            self._bump("occurrence_admission_rejections")
            self._bump("failed_work")
            raise
        # The private factory accepts only a typed gain from the canonical
        # producer or an exactly issued process-cache record.
        self._bump(
            "gain_validation_operand_bits",
            ones.bit_length() + gain.multiplier.bit_length(),
        )
        cell = CollatzDyadicOccurrence._from_gain(
            width,
            residue,
            ones,
            endpoint - gain.multiplier * (source >> width),
            gain,
        )
        try:
            self._publish(cell, source >> width)
        except BlockContextBudgetExceeded:
            self._bump("occurrence_admission_rejections")
            self._bump("failed_work")
            raise
        self._share(source, cell)
        if tape_width_summary is not None:
            self._remember_exact_width(source, width, tape_width_summary)
        return True

    def _remember_exact_width(
        self,
        source: int,
        width: int,
        summary: CollatzTapeWidthSummary,
    ) -> None:
        residue, _ = _admit_source_key(source, width)
        fiber = source >> width
        key = (width, residue, fiber)
        self._validate_width_summary(summary, source, width)
        if key in self.width_spines:
            existing = self.width_spines[key]
            self._validate_width_summary(existing, source, width)
            if existing != summary:
                raise ValueError(
                    "conflicting Collatz width spines for one exact source"
                )
            return
        retained = self._retain_width_summary(key, summary)
        shared = self._share_width_summary(key, summary)
        if retained or shared:
            self._bump("width_spine_publications")

    def _compose_width_summaries(
        self,
        before: CollatzTapeWidthSummary | None,
        after: CollatzTapeWidthSummary | None,
    ) -> CollatzTapeWidthSummary | None:
        if before is None or after is None:
            return None
        if before.target_width != after.source_width:
            raise ValueError("adjacent Collatz width summaries do not meet")
        blank = compose_width_ledger(self.ledger, before.blank, after.blank)
        return CollatzTapeWidthSummary(
            before.source_width,
            after.target_width,
            before.physical_ticks + after.physical_ticks,
            before.normalized_symbols + after.normalized_symbols,
            before.odd_steps + after.odd_steps,
            blank,
        )

    def observe(
        self,
        source: int,
        width: int,
        ones: int,
        endpoint: int,
        *,
        anchor: int,
        tape_width_summary: CollatzTapeWidthSummary | None = None,
    ) -> None:
        """Retain useful dyadic submacros from the existing producer, once.

        No branch is evaluated here. Adjacent equal-sized intervals coalesce
        using their measured odd count and endpoint. Root-prefix intervals are
        retained directly; interior intervals are retained only after an
        existing join supplies their exact source, action, and endpoint.
        Irregular run boundaries end the frontier rather than trigger splitting
        or source rediscovery.
        """
        self._check_open()
        if width < 8 or width & (width - 1) or endpoint <= 2:
            self.frontier.clear()
            return
        if tape_width_summary is not None:
            self._validate_width_summary(tape_width_summary, source, width)
            if (
                tape_width_summary.normalized_symbols != width
                or tape_width_summary.odd_steps != ones
                or tape_width_summary.physical_ticks != width + ones
                or tape_width_summary.target_width != endpoint.bit_length()
            ):
                raise ValueError("Collatz observed width spine differs from segment")
        if any(smaller < width for smaller in self.frontier):
            # A shorter unmatched suffix separates this block from any earlier
            # block of the same width. They must never be composed as adjacent.
            self.frontier.clear()
        joined = False
        while True:
            root_prefix = source == anchor
            useful_join = (
                joined
                and not root_prefix
                and self._interior_records < self.MAX_INTERIOR_RECORDS
            )
            if (
                (root_prefix or useful_join)
                and 16 <= width <= source.bit_length()
                and self.remember(
                    source,
                    width,
                    ones,
                    endpoint,
                    tape_width_summary=tape_width_summary,
                )
                and useful_join
            ):
                self._interior_records += 1
            left = self.frontier.pop(width, None)
            if left is None:
                self.frontier[width] = (source, ones, tape_width_summary)
                break
            source, left_ones, left_summary = left
            ones += left_ones
            width *= 2
            tape_width_summary = self._compose_width_summaries(
                left_summary, tape_width_summary
            )
            joined = True
            self._bump("occurrence_frontier_joins")

    def lookup_largest(
        self, source: int, width: int, physical_ticks: int
    ) -> CollatzDyadicOccurrence | None:
        """Try the admitted parent before smaller cached cylinders."""
        self._check_open()
        while width >= 16:
            found = self.lookup(source, width)
            if found is not None:
                if width + found.odd_symbols <= physical_ticks:
                    return found
                self.rejected_fit()
            width //= 2
        return None

    def lookup_largest_with_width(
        self, source: int, width: int, physical_ticks: int
    ) -> tuple[CollatzDyadicOccurrence, CollatzTapeWidthSummary | None] | None:
        """Select the largest endpoint macro and its exact-source width spine.

        The endpoint macro may transport to any high fiber with the same low
        residue. Its width spine is fetched from a separate exact-fiber key and
        is therefore absent for a transported source unless that exact source
        was itself admitted during an earlier construction.
        """
        found = self.lookup_largest(source, width, physical_ticks)
        if found is None:
            return None
        return found, self.lookup_width_summary(source, found.width)

    def lookup_width_summary(
        self, source: int, width: int
    ) -> CollatzTapeWidthSummary | None:
        """Look up a completed width spine only for its exact source fiber."""
        self._check_open()
        residue, _ = _admit_source_key(source, width)
        fiber = source >> width
        key = (width, residue, fiber)
        self._bump("width_spine_lookups")
        self._bump(
            "width_spine_key_operand_bits",
            width.bit_length() + residue.bit_length() + fiber.bit_length(),
        )
        if key in self.width_spines:
            local = self.width_spines[key]
            try:
                if type(local) is not CollatzTapeWidthSummary:
                    raise ValueError("local Collatz width spine has another sort")
                self._validate_width_summary(local, source, width)
            except (TypeError, ValueError):
                self._bump("width_spine_admission_rejections")
                self._bump("failed_work")
                raise
            self._bump("width_spine_local_hits")
            return local
        if not self.shared_cache:
            self._bump("width_spine_misses")
            return None
        cache = get_process_cache()
        if not cache.enabled:
            self._bump("width_spine_bypasses")
            self._bump("width_spine_misses")
            return None
        try:
            lease = cache.acquire(
                "collatz-dyadic-width-spine", self.WIDTH_SPINE_VERSION, key
            )
        except BlockContextBudgetExceeded:
            self._bump("width_spine_bypasses")
            self._bump("width_spine_misses")
            return None
        with lease:
            try:
                payload = lease.get_issued(("summary",), _WIDTH_SPINE_PUBLISHER)
            except CacheRecordIssuerMismatch:
                self._bump("width_spine_admission_rejections")
                self._bump("failed_work")
                raise
            if payload is MISSING:
                self._bump("width_spine_misses")
                return None
            try:
                summary = self._decode_width_summary(payload, source, width)
                self._retain_width_summary(key, summary)
            except (TypeError, ValueError, BlockContextBudgetExceeded):
                self._bump("width_spine_admission_rejections")
                self._bump("failed_work")
                raise
            self._bump("width_spine_process_hits")
            return summary

    def _validate_width_summary(
        self, summary: CollatzTapeWidthSummary, source: int, width: int
    ) -> None:
        if type(summary) is not CollatzTapeWidthSummary:
            raise ValueError("Collatz exact width spine is malformed or detached")
        if type(summary.blank) is not BlankLedger:
            raise ValueError("Collatz exact width spine has a foreign blank ledger")
        # Frozen dataclasses can still be tampered with through object.__setattr__.
        # Re-run canonical validation before trusting any cached field.
        summary.blank.__post_init__()
        summary.__post_init__()
        if (
            summary.source_width != source.bit_length()
            or summary.normalized_symbols != width
            or summary.physical_ticks != width + summary.odd_steps
            or summary.odd_steps > width
            or summary.target_width <= 0
            or summary.blank.delta != summary.target_width - summary.source_width
        ):
            raise ValueError("Collatz exact width spine is malformed or detached")

    def _decode_width_summary(
        self, payload: object, source: int, width: int
    ) -> CollatzTapeWidthSummary:
        if (
            type(payload) is not tuple
            or len(payload) != 8
            or any(type(value) is not int for value in payload)
        ):
            raise ValueError("Collatz shared width spine payload is invalid")
        (
            source_width,
            target_width,
            physical,
            normalized,
            odd,
            delta,
            minimum,
            maximum,
        ) = payload
        summary = CollatzTapeWidthSummary(
            source_width,
            target_width,
            physical,
            normalized,
            odd,
            BlankLedger(delta, minimum, maximum),
        )
        self._validate_width_summary(summary, source, width)
        self._bump(
            "width_spine_payload_operand_bits", sum(v.bit_length() for v in payload)
        )
        return summary

    def _retain_width_summary(
        self,
        key: tuple[int, int, int],
        summary: CollatzTapeWidthSummary,
    ) -> bool:
        if key in self.width_spines:
            return False
        if len(self.width_spines) >= self.WIDTH_SPINE_LIMIT:
            del self.width_spines[next(iter(self.width_spines))]
            self._bump("width_spine_evictions")
        try:
            self.width_spines[key] = summary
        except BlockContextBudgetExceeded:
            self._bump("width_spine_bypasses")
            return False
        return True

    def _share_width_summary(
        self,
        key: tuple[int, int, int],
        summary: CollatzTapeWidthSummary,
    ) -> bool:
        if not self.shared_cache:
            return False
        cache = get_process_cache()
        if not cache.enabled:
            self._bump("width_spine_bypasses")
            return False
        try:
            lease = cache.acquire(
                "collatz-dyadic-width-spine", self.WIDTH_SPINE_VERSION, key
            )
        except BlockContextBudgetExceeded:
            self._bump("width_spine_bypasses")
            return False
        with lease:
            published = lease.put_issued(
                ("summary",),
                (
                    summary.source_width,
                    summary.target_width,
                    summary.physical_ticks,
                    summary.normalized_symbols,
                    summary.odd_steps,
                    *summary.blank.as_tuple(),
                ),
                _WIDTH_SPINE_PUBLISHER,
            )
            if not published:
                self._bump("width_spine_bypasses")
            return published
