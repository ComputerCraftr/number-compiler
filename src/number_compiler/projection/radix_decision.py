"""Small reduced ordered radix decision DAG experiments.

These helpers are intentionally post-projection canonicalizers.  They answer
whether an already exact finite bitmap/map contains radix decision redundancy;
they do not hide the cost of constructing that bitmap/map.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence


@dataclass(frozen=True, slots=True)
class RadixDecisionMetrics:
    input_bits: int
    output_bits: int
    nonterminal_nodes: int
    distinct_roots: int
    order: str


@dataclass(frozen=True, slots=True)
class CollatzInverseDecisionMetrics:
    """Truth-table-free LSB decision DAG metrics for ``Q_k^-1``.

    ``symbolic_states`` counts exact residual states visited while constructing
    all output-bit roots. ``residual_state_upper_bound`` is the closed finite
    bound obtained from the prefix-popcount/truncated-affine factorization.
    """

    width: int
    nonterminal_nodes: int
    distinct_roots: int
    symbolic_states: int
    residual_state_upper_bound: int


def collatz_inverse_residual_state_upper_bound(width: int) -> int:
    """Exact finite upper bound for the symbolic LSB ``Q_k^-1`` construction.

    For output bit ``t``, after assigning ``l`` low parity bits, the residual
    function is determined by prefix popcount ``s`` and one quotient residue
    modulo ``2**(t+1-l)``.  Hence the frontier is bounded by

        min(2**l, (l+1)*2**(t+1-l)).

    Splitting this sum near ``l=(t+log2(t))/2`` yields
    ``O(sqrt(t)*2**(t/2))`` states for one high output bit and therefore
    ``O(sqrt(k)*2**(k/2))`` over all output bits up to width ``k``.
    """
    k = int(width)
    if k < 0:
        raise ValueError(k)
    total = 0
    for t in range(k):
        for left_index in range(t + 1):
            total += min(1 << left_index, (left_index + 1) << (t + 1 - left_index))
    return total


def collatz_inverse_symbolic_decision_metrics(
    width: int,
) -> CollatzInverseDecisionMetrics:
    """Build the shared ``Q_k^-1`` ROBDD without enumerating its ``2**k`` table.

    Let ``A`` be the already-fixed prefix contribution to

        Q_k^-1(q) = -sum_j q_j 2**j 3**(-s_(j+1)).

    At input level ``l`` and for output bit ``t``, all lower ``l`` bits of
    ``A`` are irrelevant to the remaining decision.  The exact residual state
    is therefore only ``(s, a)`` with

        a = floor(A/2**l) mod 2**(t+1-l).

    Choosing the next parity bit updates ``a`` by either right-shifting it or
    subtracting ``3**(-(s+1))`` and right-shifting.  This is the executable
    meet-in-the-middle construction behind the earlier empirical
    ``k*2**(k/2)`` observation.
    """
    k = int(width)
    if k < 0:
        raise ValueError(k)
    unique: dict[tuple[int, int, int], int] = {}
    roots: list[int] = []
    symbolic_states = 0

    for t in range(k):
        seen: set[tuple[int, int, int]] = set()

        root = (0, 0, 0)
        memo: dict[tuple[int, int, int], int] = {}
        stack: list[tuple[int, int, int, bool]] = [(0, 0, 0, False)]
        while stack:
            level, ones, quotient, expanded = stack.pop()
            state = (level, ones, quotient)
            if state in memo:
                continue
            if state not in seen:
                seen.add(state)
                symbolic_states += 1
            modulus = 1 << (t + 1 - level)
            if not 0 <= quotient < modulus:
                raise AssertionError((t, state, modulus))
            inverse = pow(3, -(ones + 1), modulus)
            low_q = quotient
            high_q = (quotient - inverse) % modulus
            if level == t:
                low_id = low_q & 1
                high_id = high_q & 1
            else:
                low_state = (level + 1, ones, low_q >> 1)
                high_state = (level + 1, ones + 1, high_q >> 1)
                if not expanded:
                    stack.append((level, ones, quotient, True))
                    stack.append((*high_state, False))
                    stack.append((*low_state, False))
                    continue
                low_id = memo[low_state]
                high_id = memo[high_state]
            if low_id == high_id:
                memo[state] = low_id
                continue
            key = (level, low_id, high_id)
            old = unique.get(key)
            if old is None:
                old = len(unique) + 2
                unique[key] = old
            memo[state] = old

        roots.append(memo[root])

    return CollatzInverseDecisionMetrics(
        width=k,
        nonterminal_nodes=len(unique),
        distinct_roots=len(set(roots)),
        symbolic_states=symbolic_states,
        residual_state_upper_bound=collatz_inverse_residual_state_upper_bound(k),
    )


def _validate_order(order: str) -> str:
    if order not in ("lsb", "msb"):
        raise ValueError(order)
    return order


def shared_radix_decision_metrics(
    outputs: Sequence[int],
    input_bits: int,
    output_bits: int,
    *,
    order: str = "lsb",
) -> RadixDecisionMetrics:
    """Reduce every output bit into one shared ROBDD-style DAG."""
    input_bits, output_bits = int(input_bits), int(output_bits)
    order = _validate_order(order)
    if input_bits < 0 or output_bits < 0 or len(outputs) != (1 << input_bits):
        raise ValueError((len(outputs), input_bits, output_bits))
    vals = tuple(map(int, outputs))
    if any(v < 0 or (output_bits and v >= (1 << output_bits)) for v in vals):
        raise ValueError("output outside declared width")

    variables = (
        tuple(range(input_bits))
        if order == "lsb"
        else tuple(range(input_bits - 1, -1, -1))
    )
    unique: dict[tuple[int, int, int], int] = {}

    def reduce_vector(vector: tuple[int, ...], level: int) -> int:
        root = (vector, level)
        memo: dict[tuple[tuple[int, ...], int], int] = {}
        stack: list[tuple[tuple[int, ...], int, bool]] = [(vector, level, False)]
        while stack:
            current, current_level, expanded = stack.pop()
            state = (current, current_level)
            if state in memo:
                continue
            first = current[0]
            if all(x == first for x in current):
                memo[state] = first
                continue
            if current_level >= input_bits:
                raise AssertionError("nonconstant vector after all variables")
            var = variables[current_level]
            if order == "lsb":
                lo = current[0::2]
                hi = current[1::2]
            else:
                half = len(current) // 2
                lo = current[:half]
                hi = current[half:]
            low_state, high_state = (lo, current_level + 1), (hi, current_level + 1)
            if not expanded:
                stack.append((current, current_level, True))
                stack.append((hi, current_level + 1, False))
                stack.append((lo, current_level + 1, False))
                continue
            low_id, high_id = memo[low_state], memo[high_state]
            if low_id == high_id:
                memo[state] = low_id
                continue
            key = (var, low_id, high_id)
            old = unique.get(key)
            if old is None:
                old = len(unique) + 2
                unique[key] = old
            memo[state] = old
        return memo[root]

    roots = []
    for bit in range(output_bits):
        vector = tuple((value >> bit) & 1 for value in vals)
        roots.append(reduce_vector(vector, 0))
    return RadixDecisionMetrics(
        input_bits=input_bits,
        output_bits=output_bits,
        nonterminal_nodes=len(unique),
        distinct_roots=len(set(roots)),
        order=order,
    )


def bitmap_radix_decision_metrics(
    mask: int, input_bits: int, *, order: str = "lsb"
) -> RadixDecisionMetrics:
    input_bits = int(input_bits)
    if input_bits < 0 or mask < 0 or mask >= (1 << (1 << input_bits)):
        raise ValueError((mask, input_bits))
    outputs = tuple((mask >> i) & 1 for i in range(1 << input_bits))
    return shared_radix_decision_metrics(outputs, input_bits, 1, order=order)


__all__ = [
    "RadixDecisionMetrics",
    "CollatzInverseDecisionMetrics",
    "shared_radix_decision_metrics",
    "bitmap_radix_decision_metrics",
    "collatz_inverse_residual_state_upper_bound",
    "collatz_inverse_symbolic_decision_metrics",
]
