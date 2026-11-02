"""One iterative Legendre action DAG, shared by wheel and prime selection.

The descriptor is an append-only factor word. Completed prefix states survive
rank queries and extensions; traversal frames are local and released on return.
Primality of the descriptor is the caller's obligation. The source constructor
in ``select`` discharges it by selecting the least remaining positive survivor.
"""

from __future__ import annotations

from bisect import bisect_right
from collections.abc import Generator, MutableMapping
from contextlib import ExitStack, contextmanager
from dataclasses import dataclass
from itertools import islice
from math import gcd

from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import prime as _prime_keys
from number_compiler.resources.process_cache import MISSING, CacheLease
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.prime.ordered_rank import (
    ORDERED_BOUNDARY_NODE_COST,
    ORDERED_WHEEL_210_TERMS,
    OrderedRankBoundary2310,
    OrderedRankBoundaryStore,
    ordered_cyclotomic_suffix_rank,
)

MAX_SHARED_FACTOR_STAGES = 4096

_ORDERED_WHEEL_2310_LENGTH = 2310
_ORDERED_SUFFIX_PACKET_NODES = 64
_ORDERED_WHEEL_2310_BUILD_WORK = 4 * 210 + 11 * 48 + 37


@dataclass(frozen=True, slots=True)
class PrimeFactorSourceIdentity:
    """Read-only identity for one append-only prime-factor source."""

    _owner_token: object
    mutation_stamp: tuple[object, int]
    factor_count: int

    def belongs_to(self, owner_token: object) -> bool:
        """Check the opaque issuer identity without exposing it to callers."""
        return self._owner_token is owner_token


@dataclass(frozen=True, slots=True)
class CachedPrimePrefixCapability:
    """Owner-bound permission to import the next factor of one issued prefix."""

    _owner_token: object
    _issuer: object
    _factors: tuple[object, ...]

    def next_factor(
        self,
        *,
        owner_token: object,
        issuer: object,
        prefix: tuple[int, ...],
    ) -> int:
        """Return exactly the next item after validating the issued prefix."""
        if (
            self._owner_token is not owner_token
            or self._issuer is not issuer
            or type(prefix) is not tuple
            or len(prefix) >= len(self._factors)
            or self._factors[: len(prefix)] != prefix
        ):
            raise ValueError("cached prime prefix is not bound to this source")
        value = self._factors[len(prefix)]
        if type(value) is not int:
            raise ValueError("cached prime prefix contains a noninteger factor")
        return value


class CoprimeRankDAG:
    """Query-owned recurrence storage with bounded, charged evaluation."""

    def __init__(
        self,
        primes: tuple[int, ...] = (),
        *,
        max_states: int | None = None,
        max_work: int | None = None,
        retain_queries: bool = True,
        shared_lease: CacheLease | None = None,
        cache_import_issuer: object | None = None,
    ) -> None:
        if any(
            v is not None and (type(v) is not int or v < 1)
            for v in (max_states, max_work)
        ):
            raise ValueError("prime states and work budgets must be positive integers")
        if cache_import_issuer is not None and type(cache_import_issuer) is not object:
            raise TypeError("prime cache importer requires an exact object capability")
        self.max_states = max_states
        self.max_work = max_work
        self.ledger = ResourceLedger()
        owner = self.ledger.register("prime.rank.states", "Legendre recurrence states")
        self.memo: OwnedMemo[tuple[int, int], int] = OwnedMemo(self.ledger, owner)
        progression_owner = self.ledger.register(
            "prime.rank.progressions", "congruence-restricted Legendre states"
        )
        self.progression_memo: OwnedMemo[tuple[int, int, int, int], int] = OwnedMemo(
            self.ledger, progression_owner
        )
        inverse_owner = self.ledger.register(
            "prime.rank.inverse_workspace", "query-local progression inverses"
        )
        self._progression_inverses: OwnedMemo[int, int] = OwnedMemo(
            self.ledger, inverse_owner
        )
        self.retain_queries = retain_queries
        self.shared_lease = shared_lease
        self.shared_publication_enabled = True
        self._closed = False
        self._factor_owner = self.ledger.register(
            "prime.rank.factors", "factor descriptor"
        )
        self._ordered_boundary_owner = self.ledger.register(
            "prime.rank.ordered_boundary", "fixed 2310-period rank boundary"
        )
        self._ordered_boundary_store = OrderedRankBoundaryStore()
        self.ledger.register_container(
            self._ordered_boundary_owner,
            self._ordered_boundary_store,
            node_count=self._ordered_boundary_store.node_count,
            payloads=self._ordered_boundary_store.payloads,
        )
        self._primes: LedgerList[int] = self.ledger.make_list(
            self._factor_owner, append_only=True
        )
        self._issued_factor_store = self._primes
        self._issued_factor_stamp = self._primes.mutation_stamp
        self._factor_source_token = object()
        self._cache_import_issuer = cache_import_issuer
        self.work = self.cache_hits = self.arithmetic_bit_work = 0
        self.shared_hits = self.shared_misses = self.shared_puts = 0
        self.peak_pending_frames = self.pending_frames = 0
        self._consecutive_depth = 0
        try:
            for prime in primes:
                self.append_factor(prime)
            if self._primes and self._primes[0] == 2:
                self._consecutive_depth = 1
        except BaseException:
            self.close()
            raise

    @property
    def primes(self) -> tuple[int, ...]:
        """Immutable descriptor; cache keys remain bound to their original prefix."""
        self._validate_factor_source()
        return self._primes.snapshot()

    @property
    def factor_count(self) -> int:
        return len(self._primes)

    def factor_source_identity(self) -> PrimeFactorSourceIdentity:
        """Return a read-only source identity without exposing its mutable store."""
        self._validate_factor_source()
        return PrimeFactorSourceIdentity(
            self._factor_source_token,
            self._issued_factor_stamp,
            len(self._primes),
        )

    def validates_factor_source(self, identity: PrimeFactorSourceIdentity) -> bool:
        """Check that an identity belongs to this intact append-only source."""
        if type(identity) is not PrimeFactorSourceIdentity:
            return False
        try:
            self._validate_factor_source()
        except RuntimeError:
            return False
        return (
            identity.belongs_to(self._factor_source_token)
            and type(identity.mutation_stamp) is tuple
            and len(identity.mutation_stamp) == 2
            and identity.mutation_stamp[0] is self._issued_factor_stamp[0]
            and type(identity.mutation_stamp[1]) is int
            and 0 <= identity.mutation_stamp[1] <= self._issued_factor_stamp[1]
            and type(identity.factor_count) is int
            and 0 <= identity.factor_count <= len(self._primes)
        )

    def is_current_factor_source(self, identity: PrimeFactorSourceIdentity) -> bool:
        """Check both source ownership and the exact current prefix snapshot."""
        return self.validates_factor_source(identity) and identity == (
            self.factor_source_identity()
        )

    def factor_source_mutation_stamp(
        self, identity: PrimeFactorSourceIdentity
    ) -> tuple[object, int]:
        """Read mutation state for a bound source so its prefix can be rechecked.

        This deliberately observes an unissued mutation of the original store:
        its caller must compare the returned stamp and revalidate the bound
        prefix before reusing any cached action. It does not certify the changed
        store as a valid factor source.
        """
        if type(identity) is not PrimeFactorSourceIdentity:
            raise ValueError("prime factor source identity is stale or foreign")
        stamp = self._primes.mutation_stamp
        if (
            not identity.belongs_to(self._factor_source_token)
            or self._primes is not self._issued_factor_store
            or not self._primes.append_only
            or type(identity.mutation_stamp) is not tuple
            or len(identity.mutation_stamp) != 2
            or identity.mutation_stamp[0] is not stamp[0]
            or type(identity.mutation_stamp[1]) is not int
            or not 0 <= identity.mutation_stamp[1] <= self._issued_factor_stamp[1]
            or type(identity.factor_count) is not int
            or (
                not self._closed and not 0 <= identity.factor_count <= len(self._primes)
            )
        ):
            raise ValueError("prime factor source identity is stale or foreign")
        return stamp

    def factor_at(self, index: int, identity: PrimeFactorSourceIdentity) -> int:
        """Read one factor through an authenticated source identity."""
        if not self.validates_factor_source(identity):
            raise ValueError("prime factor source identity is stale or foreign")
        if type(index) is not int or not 0 <= index < identity.factor_count:
            raise IndexError("prime factor index is outside the admitted source")
        return self._primes[index]

    def issue_cached_prefix_capability(
        self, factors: tuple[object, ...], issuer: object
    ) -> CachedPrimePrefixCapability:
        """Bind a cache-issued immutable prefix to this exact rank owner."""
        self._validate_factor_source()
        if (
            self._cache_import_issuer is None
            or type(issuer) is not object
            or issuer is not self._cache_import_issuer
            or type(factors) is not tuple
            or not factors
            or len(factors) > MAX_SHARED_FACTOR_STAGES
            or len(factors) < len(self._primes)
            or factors[: len(self._primes)] != self._primes.snapshot()
        ):
            raise ValueError("cached prime prefix lacks this owner's issuer")
        return CachedPrimePrefixCapability(self._factor_source_token, issuer, factors)

    @property
    def last_factor(self) -> int:
        self._validate_factor_source()
        return self._primes[-1]

    def factor_rank(self, limit: int) -> int:
        self._validate_factor_source()
        return bisect_right(self._primes, limit)

    def _validate_factor_source(self) -> None:
        """Only this owner's appends may advance numerical memo authority."""
        if (
            self._primes is not self._issued_factor_store
            or self._primes.mutation_stamp != self._issued_factor_stamp
        ):
            raise RuntimeError(
                "prime factor source changed: prime successor action lost its parent source binding"
            )

    def charge(self, bit_work: int = 0) -> None:
        """One admission/evaluation step; operand bits are reported separately."""
        self.charge_many(1, bit_work)

    def charge_many(self, amount: int, bit_work: int = 0) -> None:
        """Charge a known batch before doing cache-admission validation."""
        if self._closed:
            raise RuntimeError("prime rank workspace is closed")
        self._validate_factor_source()
        if type(amount) is not int or amount < 0:
            raise ValueError("prime work charge must be a nonnegative integer")
        if self.max_work is not None and self.work + amount > self.max_work:
            raise ValueError("prime work budget exceeded (--max-prime-work)")
        self.work += amount
        self.arithmetic_bit_work += bit_work

    def append_factor(self, prime: int) -> None:
        self._validate_factor_source()
        if (
            type(prime) is not int
            or prime < 2
            or (self._primes and prime <= self._primes[-1])
        ):
            raise ValueError("wheel factors must be increasing integers >= 2")
        self.charge(prime.bit_length())
        self.ledger.reserve(self._factor_owner, entries=1, nodes=1)
        try:
            self._primes.append(prime)
            self._issued_factor_stamp = self._primes.mutation_stamp
        except BaseException:
            self.ledger.release(self._factor_owner, entries=1, nodes=1)
            raise

    def append_consecutive_factor(self, prime: int) -> None:
        """Admit the next factor by the exact least-survivor construction."""
        self.validate_fresh_successor(prime)
        self.append_factor(prime)
        self._consecutive_depth = len(self._primes)

    def advance_verified_phase_lane(
        self, root: int, *, max_stages: int
    ) -> tuple[int | None, int, bool]:
        """Find the next prefix prime by scanning its exact odd divisor lanes.

        For candidates at most the square of the last admitted prime, every
        composite has a divisor in this authenticated consecutive prefix.
        The scan is ordered, so its first survivor is the exact next prime.
        If the requested endpoint exceeds that square and no survivor was
        found, the caller must use the ordinary exact rank recurrence.

        The return values are the appended factor (if any), odd candidates
        examined, and whether the requested interval is fully covered.
        """
        self._validate_factor_source()
        if self._closed:
            raise RuntimeError("prime rank workspace is closed")
        if (
            type(root) is not int
            or root < 2
            or type(max_stages) is not int
            or max_stages < 1
        ):
            raise ValueError("invalid prime phase-lane horizon or stage budget")
        if (
            not self._primes
            or self._consecutive_depth != len(self._primes)
            or self._primes[0] != 2
        ):
            raise RuntimeError(
                "phase-lane discovery needs a certified consecutive prefix"
            )
        previous = self._primes[-1]
        if previous >= root:
            return None, 0, True
        square_bound = previous * previous
        end = min(root, square_bound)
        start = 3 if previous == 2 else previous + 2
        if start > end:
            return None, 0, root <= square_bound
        tested = 0
        factor_count = len(self._primes)
        for candidate in range(start, end + 1, 2):
            tested += 1
            self.charge(candidate.bit_length())
            removed = False
            for index in range(1, factor_count):
                factor = self._primes[index]
                if factor * factor > candidate:
                    break
                self.charge(candidate.bit_length() + factor.bit_length())
                if candidate % factor == 0:
                    removed = True
                    break
            if removed:
                continue
            if factor_count >= max_stages:
                raise ValueError("prime stage budget exceeded (--max-prime-stages)")
            self.append_factor(candidate)
            self._consecutive_depth = len(self._primes)
            return candidate, tested, False
        return None, tested, root <= square_bound

    def _build_ordered_boundary_2310(
        self,
    ) -> OrderedRankBoundary2310 | None:
        """Build the one fixed 210-to-2310 boundary under ledger ownership."""
        existing = self._ordered_boundary_store.boundary
        if existing is not None:
            return existing
        if (
            self._consecutive_depth < 5
            or len(self._primes) < 5
            or tuple(self._primes[index] for index in range(5)) != (2, 3, 5, 7, 11)
        ):
            return None
        if (
            self.max_work is not None
            and self.work + _ORDERED_WHEEL_2310_BUILD_WORK > self.max_work
        ):
            return None
        self.ledger.reserve(
            self._ordered_boundary_owner,
            nodes=ORDERED_BOUNDARY_NODE_COST,
        )
        try:
            self.charge_many(
                _ORDERED_WHEEL_2310_BUILD_WORK,
                _ORDERED_WHEEL_2310_BUILD_WORK * 12,
            )
            boundary = OrderedRankBoundary2310.build()
            self._ordered_boundary_store.publish(boundary)
            self.ledger.note_store_mutation()
        except BaseException:
            if self._ordered_boundary_store.clear():
                self.ledger.note_store_mutation()
            self.ledger.release(
                self._ordered_boundary_owner,
                nodes=ORDERED_BOUNDARY_NODE_COST,
            )
            raise
        return boundary

    def _ordered_cyclotomic_carry_rank(self, limit: int, depth: int) -> int | None:
        """Evaluate a bounded exact suffix over the fixed 2310 boundary.

        The source must own a consecutive prime prefix. The inclusion-exclusion
        packet is bounded to sixteen ordered divisor pullbacks; greater depth
        uses the existing memoized recurrence rather than extending a wheel.
        """
        suffix_length = depth - 5
        if depth < 5 or depth > self._consecutive_depth or suffix_length > 4:
            return None
        if self._ordered_boundary_store.boundary is None and (
            depth < 8 or limit < _ORDERED_WHEEL_2310_LENGTH * 32
        ):
            return None
        estimated_terms = 1 << suffix_length
        build_work = (
            0
            if self._ordered_boundary_store.boundary is not None
            else _ORDERED_WHEEL_2310_BUILD_WORK
        )
        packet_work = suffix_length + 7 * estimated_terms
        estimated_work = build_work + packet_work
        if self.max_work is not None and self.work + estimated_work > self.max_work:
            return None
        boundary = self._build_ordered_boundary_2310()
        if boundary is None:
            return None
        bit_work = packet_work * (limit.bit_length() + 12)
        self.ledger.reserve(
            self._ordered_boundary_owner,
            nodes=_ORDERED_SUFFIX_PACKET_NODES,
        )
        try:
            self.charge_many(packet_work, bit_work)
            return ordered_cyclotomic_suffix_rank(
                limit,
                boundary,
                (self._primes[index] for index in range(5, depth)),
            )
        finally:
            self.ledger.release(
                self._ordered_boundary_owner,
                nodes=_ORDERED_SUFFIX_PACKET_NODES,
            )

    def append_next_cached_prefix_factor(
        self, capability: CachedPrimePrefixCapability
    ) -> int:
        """Import only the next factor from an authenticated cached prefix.

        The capability binds the complete immutable manifest, cache issuer and
        this exact source owner. Callers cannot supply an arbitrary factor.
        """
        self._validate_factor_source()
        if (
            type(capability) is not CachedPrimePrefixCapability
            or self._cache_import_issuer is None
            or self._consecutive_depth != len(self._primes)
        ):
            raise RuntimeError("cached prime prefix is not bound to this source")
        try:
            prime = capability.next_factor(
                owner_token=self._factor_source_token,
                issuer=self._cache_import_issuer,
                prefix=self._primes.snapshot(),
            )
        except ValueError as error:
            raise RuntimeError(
                "cached prime prefix is not bound to this source"
            ) from error
        self.append_factor(prime)
        self._consecutive_depth = len(self._primes)
        return prime

    def validate_consecutive_prefix(self, depth: int | None = None) -> None:
        """Authenticate factors as the initial consecutive prime prefix.

        Every successor after 2 must be the least positive parent-wheel
        survivor above 1.  The check uses this same exact rank owner and caches
        only the greatest validated depth; it does not call a primality oracle.
        """
        if self._closed:
            raise RuntimeError("prime rank workspace is closed")
        self._validate_factor_source()
        if depth is None:
            depth = len(self._primes)
        if type(depth) is not int or not 1 <= depth <= len(self._primes):
            raise ValueError("consecutive prefix depth must be admitted and nonempty")
        if self._primes[0] != 2:
            raise ValueError("consecutive prime prefix must start at 2")
        start = max(1, self._consecutive_depth)
        for index in range(start, depth):
            factor = self._primes[index]
            if self.count(factor - 1, index) != 1 or self.count(factor, index) != 2:
                raise ValueError("wheel descriptor is not a consecutive prime prefix")
            self._consecutive_depth = index + 1
        self._consecutive_depth = max(self._consecutive_depth, min(depth, 1))

    def validate_fresh_successor(self, fresh_prime: int) -> None:
        """Prove ``fresh_prime`` is the next survivor of this exact prefix."""
        self._validate_factor_source()
        if (
            type(fresh_prime) is not int
            or not self._primes
            or fresh_prime <= self._primes[-1]
        ):
            raise ValueError("fresh successor must follow a nonempty prefix")
        self.validate_consecutive_prefix()
        depth = len(self._primes)
        if (
            self.count(fresh_prime - 1, depth) != 1
            or self.count(fresh_prime, depth) != 2
        ):
            raise ValueError("fresh prime is not the least parent-wheel survivor")

    def validate_bound_factor_prefix(
        self, parent: tuple[int, ...], successor: int | None = None
    ) -> None:
        """Recheck a previously admitted prefix after its store changes.

        This validates source contents, not primality discovery. The caller
        owns the immutable expected prefix and its mutation-stamp admission.
        Charge before scanning and retain no detached factor copy.
        """
        depth = len(parent)
        required = depth + int(successor is not None)
        self.charge_many(required)
        self.ledger.bump(
            _prime_keys.PRIME_SUCCESSOR_PREFIX_VALIDATION_FACTORS, required
        )
        bit_work = 0
        try:
            if len(self._primes) < required:
                raise RuntimeError(
                    "prime successor action lost its parent source binding"
                )
            for index in range(required):
                expected = parent[index] if index < depth else successor
                actual = self._primes[index]
                if type(actual) is not int or type(expected) is not int:
                    raise RuntimeError(
                        "prime successor action lost its parent source binding"
                    )
                bit_work += actual.bit_length() + expected.bit_length()
                if actual != expected:
                    raise RuntimeError(
                        "prime successor action lost its parent source binding"
                    )
        finally:
            self.charge_many(0, bit_work)

    def count_via_fresh_successor(self, limit: int, depth: int | None = None) -> int:
        """Apply the final admitted prime as an exact partial successor action.

        For the fresh final factor ``q``, multiplication by ``q`` bijects the
        deleted parent survivors up to ``limit`` with parent survivors up to
        ``floor(limit/q)``.  This is the zero-phase, single-forbidden-residue
        specialization of the successor action and never evaluates its full
        parent period.
        """
        if self._closed:
            raise RuntimeError("prime rank workspace is closed")
        if depth is None:
            depth = len(self._primes)
        if (
            type(limit) is not int
            or type(depth) is not int
            or not 1 <= depth <= len(self._primes)
        ):
            raise ValueError("invalid fresh-prime partial rank request")
        self.validate_consecutive_prefix(depth)
        q = self._primes[depth - 1]
        parent_depth = depth - 1
        self.ledger.bump(_prime_keys.PRIME_FRESH_SUCCESSOR_PARTIAL_QUERIES)
        return self.count(limit, parent_depth) - self.count(limit // q, parent_depth)

    def count(self, limit: int, depth: int | None = None) -> int:
        """Count positive survivors <= limit without materializing a gap cycle."""
        if self._closed:
            raise RuntimeError("prime rank workspace is closed")
        self._validate_factor_source()
        if depth is None:
            depth = len(self._primes)
        if (
            type(limit) is not int
            or type(depth) is not int
            or not 0 <= depth <= len(self._primes)
        ):
            raise ValueError("invalid wheel count request")
        root = (depth, limit)
        # A compatibility call owns this local map only for this evaluation.
        # It is never published on the execution owner or retained by a closure.
        memo: MutableMapping[tuple[int, int], int] = (
            self.memo if self.retain_queries else {}
        )
        stack = [(depth, limit, False)]

        def local_value(key: tuple[int, int]) -> int | None:
            try:
                value = memo[key]
            except KeyError:
                return None
            self.cache_hits += 1
            return value

        def shared_key(key: tuple[int, int]) -> tuple[str, tuple[int, ...], int]:
            # Exact prefix keys require a traversal, unlike a sampled digest.
            # Admit that work before allocating the tuple. Operand bits use a
            # conservative bound from the largest factor in the sorted prefix.
            bits = key[0] * self._primes[key[0] - 1].bit_length()
            self.charge_many(key[0], bits + abs(key[1]).bit_length())
            return "phi", tuple(islice(self._primes, key[0])), key[1]

        def shared_value(key: tuple[int, int]) -> int | None:
            if self.shared_lease is None or not 0 < key[0] <= MAX_SHARED_FACTOR_STAGES:
                return None
            found = self.shared_lease.get(shared_key(key), MISSING)
            if found is MISSING:
                self.shared_misses += 1
                return None
            if type(found) is not int or not 0 <= found <= max(0, key[1]):
                raise RuntimeError("invalid shared prime rank state")
            self.shared_hits += 1
            return found

        def publish(key: tuple[int, int], value: int) -> None:
            if (
                self.shared_lease is not None
                and self.shared_publication_enabled
                and 0 < key[0] <= MAX_SHARED_FACTOR_STAGES
            ):
                self.shared_puts += int(self.shared_lease.put(shared_key(key), value))

        try:
            local_root = local_value(root)
            if local_root is not None:
                self.charge()
                return local_root
            shared_root = shared_value(root)
            if shared_root is not None:
                self.charge()
                return shared_root
            while stack:
                self.pending_frames = len(stack)
                self.peak_pending_frames = max(self.peak_pending_frames, len(stack))
                d, x, ready = stack.pop()
                self.charge()
                key = (d, x)
                if local_value(key) is not None:
                    continue
                if x <= 1 or d == 0:
                    result = max(0, x)
                elif d <= self._consecutive_depth and x <= self._primes[d - 1]:
                    # The source owns every prime through p_d. Thus 1 is the
                    # sole positive survivor at or below that endpoint.
                    result = 1
                elif d == 4 and self._consecutive_depth >= 4:
                    # Exact ordered Phi_210 prefix action. A phase histogram
                    # would lose endpoint ownership; the signed floor sum
                    # retains it directly.
                    self.charge_many(16, 16 * x.bit_length())
                    result = sum(
                        sign * (x // divisor)
                        for divisor, sign in ORDERED_WHEEL_210_TERMS
                    )
                elif (
                    d >= 5
                    and (ordered_result := self._ordered_cyclotomic_carry_rank(x, d))
                    is not None
                ):
                    result = ordered_result
                elif d == 1:
                    # Exact base recurrence: Phi(x,1)=x-floor(x/p1).
                    p = self._primes[0]
                    self.arithmetic_bit_work += 2 * x.bit_length() + p.bit_length()
                    result = x - x // p
                else:
                    p = self._primes[d - 1]
                    self.arithmetic_bit_work += abs(x).bit_length() + p.bit_length()
                    left, right = (d - 1, x), (d - 1, x // p)
                    if not ready:
                        stack.append((d, x, True))
                        if local_value(right) is None:
                            stack.append((*right, False))
                        if local_value(left) is None:
                            stack.append((*left, False))
                        continue
                    left_value, right_value = local_value(left), local_value(right)
                    if left_value is None or right_value is None:
                        raise RuntimeError("prime rank traversal lost a dependency")
                    result = left_value - right_value
                    self.arithmetic_bit_work += (
                        left_value.bit_length() + right_value.bit_length()
                    )
                if (
                    self.max_states is not None
                    and self.ledger.entries - self.factor_count >= self.max_states
                ):
                    raise ValueError("prime state budget exceeded (--max-prime-states)")
                memo[key] = result
            if root not in memo:
                raise RuntimeError("prime rank traversal did not produce its root")
            result = memo[root]
            publish(root, result)
            return result
        finally:
            stack.clear()
            self.pending_frames = 0
            if not self.retain_queries:
                memo.clear()

    @staticmethod
    def _base_progression_count(limit: int, modulus: int, residue: int) -> int:
        """Positive integers ``<= limit`` in one canonical residue class."""
        if limit < 1:
            return 0
        first = modulus if residue == 0 else residue
        if first > limit:
            return 0
        return 1 + (limit - first) // modulus

    def count_progression(
        self,
        limit: int,
        modulus: int,
        residue: int,
        depth: int | None = None,
    ) -> int:
        """Count prefix survivors in one congruence class without scanning.

        The result is the number of positive ``n <= limit`` that are coprime
        to the first ``depth`` descriptor factors and satisfy
        ``n == residue (mod modulus)``.  The progression modulus must be
        coprime to the admitted factor prefix.  ``modulus == 1`` is exactly
        the canonical :meth:`count` owner, so ordinary prime selection keeps
        the established Phi implementation and cache behavior.
        """
        if self._closed:
            raise RuntimeError("prime rank workspace is closed")
        self._validate_factor_source()
        if depth is None:
            depth = len(self._primes)
        if (
            type(limit) is not int
            or type(modulus) is not int
            or type(residue) is not int
            or type(depth) is not int
            or modulus < 1
            or not 0 <= depth <= len(self._primes)
        ):
            raise ValueError("invalid prime progression count request")
        residue %= modulus
        if modulus == 1:
            return self.count(limit, depth)
        if any(gcd(modulus, p) != 1 for p in islice(self._primes, depth)):
            raise ValueError("progression modulus must be coprime to wheel factors")
        if limit < 1:
            self.charge()
            return 0

        root = (depth, limit, modulus, residue)
        memo = self.progression_memo
        # A returning frame retains the already computed right-child residue.
        # Zero is a valid residue; None alone denotes an unopened node.
        stack: list[tuple[int, int, int, int | None]] = [(depth, limit, residue, None)]
        try:
            while stack:
                self.pending_frames = len(stack)
                self.peak_pending_frames = max(self.peak_pending_frames, len(stack))
                d, x, r, child_residue = stack.pop()
                self.charge()
                key = (d, x, modulus, r)
                if key in memo:
                    self.cache_hits += 1
                    continue
                if x < 1:
                    result = 0
                elif d == 0:
                    result = self._base_progression_count(x, modulus, r)
                    self.arithmetic_bit_work += (
                        x.bit_length() + modulus.bit_length() + r.bit_length()
                    )
                else:
                    if child_residue is None:
                        p = self._primes[d - 1]
                        child_residue = 0
                        if r:
                            inverse = self._progression_inverses.get(d)
                            if inverse is None:
                                if (
                                    self.max_states is not None
                                    and self.ledger.entries - self.factor_count
                                    >= self.max_states
                                ):
                                    raise ValueError(
                                        "prime state budget exceeded (--max-prime-states)"
                                    )
                                self.charge(p.bit_length() + modulus.bit_length())
                                inverse = pow(p, -1, modulus)
                                self._progression_inverses[d] = inverse
                                self.ledger.bump(
                                    _prime_keys.PRIME_PROGRESSION_INVERSE_EVALUATIONS
                                )
                            child_residue = r * inverse % modulus
                        self.arithmetic_bit_work += (
                            x.bit_length() + p.bit_length() + modulus.bit_length()
                        )
                        stack.append((d, x, r, child_residue))
                        right = (d - 1, x // p, modulus, child_residue)
                        left = (d - 1, x, modulus, r)
                        if right not in memo:
                            stack.append((d - 1, x // p, child_residue, None))
                        else:
                            self.cache_hits += 1
                        if left not in memo:
                            stack.append((d - 1, x, r, None))
                        else:
                            self.cache_hits += 1
                        continue
                    p = self._primes[d - 1]
                    left = (d - 1, x, modulus, r)
                    right = (d - 1, x // p, modulus, child_residue)
                    self.arithmetic_bit_work += x.bit_length() + p.bit_length()
                    try:
                        left_value, right_value = memo[left], memo[right]
                    except KeyError as error:
                        raise RuntimeError(
                            "prime progression traversal lost a dependency"
                        ) from error
                    result = left_value - right_value
                    self.arithmetic_bit_work += (
                        left_value.bit_length() + right_value.bit_length()
                    )
                if (
                    self.max_states is not None
                    and self.ledger.entries - self.factor_count >= self.max_states
                ):
                    raise ValueError("prime state budget exceeded (--max-prime-states)")
                memo[key] = result
            try:
                return memo[root]
            except KeyError as error:
                raise RuntimeError(
                    "prime progression traversal did not produce its root"
                ) from error
        finally:
            stack.clear()
            self.pending_frames = 0
            self._progression_inverses.clear()
            if not self.retain_queries:
                memo.clear()

    def count_progression_interval(
        self,
        lower: int,
        upper: int,
        modulus: int,
        residue: int,
        depth: int | None = None,
    ) -> int:
        """Count admitted values in the half-open interval ``[lower, upper)``."""
        if type(lower) is not int or type(upper) is not int or lower > upper:
            raise ValueError("invalid prime progression interval")
        return self.count_progression(
            upper - 1, modulus, residue, depth
        ) - self.count_progression(lower - 1, modulus, residue, depth)

    @contextmanager
    def suspend_shared_publication(self) -> Generator[None, None, None]:
        """Keep temporary discovery ranks local, preserving the caller's mode."""
        previous = self.shared_publication_enabled
        self.shared_publication_enabled = False
        try:
            yield
        finally:
            self.shared_publication_enabled = previous

    def close(self) -> None:
        """Release query retention, including on budget refusal."""
        if self._closed:
            return
        with ExitStack() as cleanup:
            cleanup.callback(self._close_factors)
            cleanup.callback(self._close_ordered_boundary)
            cleanup.callback(self.memo.dispose)
            cleanup.callback(self._progression_inverses.dispose)
            self.progression_memo.dispose()
        self._closed = True

    def _close_ordered_boundary(self) -> None:
        if self._ordered_boundary_store.clear():
            self.ledger.note_store_mutation()
            self.ledger.release(
                self._ordered_boundary_owner,
                nodes=ORDERED_BOUNDARY_NODE_COST,
            )
        self.ledger.mark_disposed(self._ordered_boundary_owner)

    def _close_factors(self) -> None:
        size = len(self._primes)
        if size:
            # Factor positions are source authorities while the query is live,
            # so the public store is append-only.  Disposal may discard its
            # unpublished backing suffix only after all consumers have closed.
            self._primes.rollback_unpublished(0)
            self.ledger.release(self._factor_owner, entries=size, nodes=size)
        self._issued_factor_stamp = self._primes.mutation_stamp
        self.ledger.mark_disposed(self._factor_owner)


__all__ = ["CoprimeRankDAG"]
