"""Bounded modular signs for a supplied common-growth coefficient bound.

This research helper evaluates ``sum c_s * choose(row, k-s)`` modulo small
primes with Lucas' theorem and reconstructs it with the repository's coprime
CRT helper.  If the caller supplies the true hypothesis ``abs(value) <= B``, a
modulus greater than ``2*B`` determines the integer and therefore its sign.

The hypothesis is not authenticated here.  Congruences can reject some false
bounds, but they cannot prove that an accepted bound belongs to a source or is
true.  This object is not a future-coefficient callback or temporal admission.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.carry.carry_itinerary import crt_coprime

_FIXED_PRIMES = (
    2,
    3,
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
    83,
    89,
    97,
    101,
    103,
    107,
    109,
    113,
    127,
    131,
)


@dataclass(frozen=True, slots=True)
class ModularSignLimits:
    max_terms: int = 128
    max_primes: int = 32
    max_table_entries: int = 10_000
    max_lucas_digits: int = 100_000
    max_integer_bits: int = 65_536
    max_integer_work_bits: int = 16_000_000
    max_retained_items: int = 12_000

    def __post_init__(self) -> None:
        for value in (
            self.max_terms,
            self.max_primes,
            self.max_table_entries,
            self.max_lucas_digits,
            self.max_integer_bits,
            self.max_integer_work_bits,
            self.max_retained_items,
        ):
            if type(value) is not int or value <= 0:
                raise ValueError("modular sign limits must be positive exact integers")
        if self.max_primes > len(_FIXED_PRIMES):
            raise ValueError("modular sign prime limit exceeds the verified prime list")


@dataclass(slots=True)
class ModularSignWork:
    queries: int = 0
    primes_constructed: int = 0
    factorial_entries: int = 0
    lucas_digits: int = 0
    modular_products: int = 0
    crt_merges: int = 0
    integer_work_bits: int = 0
    peak_integer_bits: int = 0
    retained_items: int = 0
    peak_retained_items: int = 0


@dataclass(frozen=True, slots=True)
class _PrimeTable:
    prime: int
    factorial: tuple[int, ...]
    inverse_factorial: tuple[int, ...]


class ModularSignOracle:
    """Reusable Lucas tables and CRT state for bounded sign queries.

    ``sign(..., bound=B)`` is sound only under the caller-supplied mathematical
    hypothesis that the absolute integer coefficient is at most ``B``.
    """

    def __init__(
        self,
        *,
        limits: ModularSignLimits | None = None,
        work: ModularSignWork | None = None,
    ) -> None:
        self.limits = limits or ModularSignLimits()
        self.work = work or ModularSignWork()
        self._tables: dict[int, _PrimeTable] = {}

    def clear(self) -> None:
        """Release this oracle's retained tables while preserving work totals."""
        released = sum(2 * table.prime + 1 for table in self._tables.values())
        self._tables.clear()
        self.work.retained_items -= released
        if self.work.retained_items < 0:
            raise RuntimeError("modular sign retention accounting underflow")

    def close(self) -> None:
        """Release this oracle's retained tables; repeated calls are harmless."""
        self.clear()

    def _charge_bits(self, bits: int, *, repetitions: int = 1) -> None:
        bits = max(1, bits)
        repetitions = max(1, repetitions)
        if bits > self.limits.max_integer_bits:
            raise ValueError("modular sign integer size budget exhausted")
        charge = bits * repetitions
        if self.work.integer_work_bits + charge > self.limits.max_integer_work_bits:
            raise ValueError("modular sign integer work budget exhausted")
        self.work.integer_work_bits += charge
        self.work.peak_integer_bits = max(self.work.peak_integer_bits, bits)

    def _reserve_table(self, prime: int) -> None:
        entries = 2 * prime
        # Construction temporarily holds both mutable lists and both immutable
        # tuples.  Check that four arrays fit before allocating even the first.
        transient_items = 4 * prime + 1
        if self.work.primes_constructed >= self.limits.max_primes:
            raise ValueError("modular sign prime budget exhausted")
        if self.work.factorial_entries + entries > self.limits.max_table_entries:
            raise ValueError("modular sign factorial-table budget exhausted")
        if self.work.retained_items + transient_items > self.limits.max_retained_items:
            raise ValueError("modular sign retention budget exhausted")
        prime_bits = prime.bit_length()
        self._charge_bits(2 * prime_bits + 1, repetitions=4 * prime)
        self.work.primes_constructed += 1
        self.work.factorial_entries += entries
        self.work.retained_items += entries + 1
        self.work.peak_retained_items = max(
            self.work.peak_retained_items,
            self.work.retained_items - entries - 1 + transient_items,
        )

    def _build_table(self, prime: int) -> _PrimeTable:
        if prime not in _FIXED_PRIMES[: self.limits.max_primes]:
            raise ValueError("prime is outside the verified modular sign list")
        existing = self._tables.get(prime)
        if existing is not None:
            return existing
        self._reserve_table(prime)
        factorial = [1] * prime
        for value in range(1, prime):
            self.work.modular_products += 1
            factorial[value] = factorial[value - 1] * value % prime
        inverse_factorial = [1] * prime
        inverse_factorial[-1] = pow(factorial[-1], prime - 2, prime)
        for value in range(prime - 1, 0, -1):
            self.work.modular_products += 1
            inverse_factorial[value - 1] = inverse_factorial[value] * value % prime
        table = _PrimeTable(prime, tuple(factorial), tuple(inverse_factorial))
        self._tables[prime] = table
        return table

    def _small_binomial(self, table: _PrimeTable, n: int, k: int) -> int:
        if not 0 <= k <= n < table.prime:
            return 0
        self.work.modular_products += 2
        first = table.factorial[n] * table.inverse_factorial[k] % table.prime
        return first * table.inverse_factorial[n - k] % table.prime

    def binomial_mod(self, n: int, k: int, prime: int) -> int:
        """Return ``choose(n,k) mod prime`` by Lucas digits, without a row walk."""
        if any(type(value) is not int for value in (n, k, prime)):
            raise TypeError("Lucas binomial inputs must be exact integers")
        if n < 0:
            raise ValueError("Lucas binomial row must be nonnegative")
        if k < 0 or k > n:
            return 0
        table = self._build_table(prime)
        result = 1
        while n or k:
            if self.work.lucas_digits >= self.limits.max_lucas_digits:
                raise ValueError("modular sign Lucas-digit budget exhausted")
            bits = max(1, n.bit_length(), k.bit_length(), prime.bit_length())
            self._charge_bits(bits + prime.bit_length() + 1)
            self.work.lucas_digits += 1
            n, low_n = divmod(n, prime)
            k, low_k = divmod(k, prime)
            if low_k > low_n:
                return 0
            # Precharge the two table products and the result product before
            # Python constructs any of their integer intermediates.
            self._charge_bits(2 * prime.bit_length() + 1, repetitions=3)
            self.work.modular_products += 1
            result = result * self._small_binomial(table, low_n, low_k) % prime
        return result

    def _residue(
        self, row: int, terms: tuple[tuple[int, int], ...], k: int, prime: int
    ) -> int:
        residue = 0
        prime_bits = prime.bit_length()
        for shift, coefficient in terms:
            self._charge_bits(
                max(
                    1,
                    row.bit_length(),
                    k.bit_length(),
                    shift.bit_length(),
                    coefficient.bit_length(),
                )
                + prime_bits
                + 1
            )
            value = self.binomial_mod(row, k - shift, prime)
            self.work.modular_products += 1
            residue = (residue + (coefficient % prime) * value) % prime
        return residue

    def sign(
        self,
        row: int,
        terms: tuple[tuple[int, int], ...],
        k: int,
        *,
        bound: int,
    ) -> int:
        """Return the exact sign under the supplied hypothesis ``abs(value)<=B``.

        Terms are ``(shift, coefficient)`` pairs in one common binomial row.
        A congruence consistent with ``bound`` does not authenticate that bound.
        """
        if any(type(value) is not int for value in (row, k, bound)):
            raise TypeError("modular sign coordinates must be exact integers")
        if row < 0 or bound < 0:
            raise ValueError("modular sign row and bound must be nonnegative")
        if type(terms) is not tuple or len(terms) > self.limits.max_terms:
            raise ValueError("modular sign term budget exhausted")
        for term in terms:
            if (
                type(term) is not tuple
                or len(term) != 2
                or type(term[0]) is not int
                or type(term[1]) is not int
            ):
                raise TypeError("modular sign terms require exact integer pairs")
        self._charge_bits(
            max(
                1,
                row.bit_length(),
                k.bit_length(),
                bound.bit_length(),
                *(max(abs(s).bit_length(), abs(c).bit_length()) for s, c in terms),
            )
            + 1
        )
        self.work.queries += 1
        if bound == 0:
            return 0
        threshold = bound << 1
        modulus = 1
        residue = 0
        for prime in _FIXED_PRIMES[: self.limits.max_primes]:
            value = self._residue(row, terms, k, prime)
            merge_bits = modulus.bit_length() + prime.bit_length() + 2
            self._charge_bits(merge_bits, repetitions=4)
            residue = crt_coprime(residue, modulus, value, prime)
            modulus *= prime
            self.work.crt_merges += 1
            if modulus > threshold:
                lifted = residue if 2 * residue <= modulus else residue - modulus
                if abs(lifted) > bound:
                    raise ValueError(
                        "modular residues are inconsistent with the supplied bound"
                    )
                return (lifted > 0) - (lifted < 0)
        raise ValueError("modular sign modulus budget is insufficient for bound")


__all__ = ["ModularSignLimits", "ModularSignOracle", "ModularSignWork"]
