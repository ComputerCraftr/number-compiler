"""Exact projection-observer / Myhill--Nerode experiments across sequence families.

The full digit state may be much larger than the information required by a
particular projection.  This module minimizes deterministic *projection
processes*: two states merge only when their present observation agrees and
successors remain equivalent.  No sampled fingerprint authorizes an exact
merge.

The finite experiments are deliberately analysis-only.  Production keeps only
quotients with direct algebraic proofs (carry reset, Collatz sentinel, factored
prime congruence, etc.).
"""

from __future__ import annotations

from collections.abc import Callable, Hashable, Iterable, Mapping, Sequence
from dataclasses import dataclass
from math import gcd, prod
from typing import TypeVar

from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.arithmetic.polynomials.digit_convolution import (
    binary_square_sign_representative,
)
from number_compiler.sequences.collatz.parity import collatz_parity_word

S = TypeVar("S", bound=Hashable)
ObservationT = TypeVar("ObservationT", bound=Hashable)


@dataclass(frozen=True, slots=True)
class MooreObserverProfile:
    name: str
    source_states: int
    observer_classes: int
    source_bits: int
    observer_bits: int
    refinement_rounds: int
    initial_class: int | None = None

    @property
    def state_ratio(self) -> float:
        return self.observer_classes / self.source_states if self.source_states else 1.0


@dataclass(frozen=True, slots=True)
class InformationObserverProfile:
    name: str
    horizon: int
    exact_projection_words: int
    required_bits: int
    note: str


@dataclass(frozen=True, slots=True)
class ReverseAddGrowthObserverProfile:
    scan_states: int = 2
    block_transformations: int = 3
    transformation_bits: int = 2


@dataclass(frozen=True, slots=True)
class SpecialObserverTheory:
    family: str
    parameter: int
    modulus: int
    source_states: int
    expected_classes_if_prime: int
    expected_observer_bits_if_prime: int
    generic_projection_steps: int


@dataclass(frozen=True, slots=True)
class SignQuotientObserverProfile:
    family: str
    parameter: int
    source_states: int
    quotient_classes: int
    target_separating: bool
    next_closed: bool


def minimize_unary_moore(
    states: Iterable[S],
    transition: Callable[[S], S],
    observation: Callable[[S], ObservationT],
    *,
    name: str = "observer",
    initial_state: S | None = None,
) -> tuple[MooreObserverProfile, Mapping[S, int]]:
    """Exact Moore minimization for one deterministic temporal transition."""
    ordered = tuple(states)
    if not ordered:
        raise ValueError("nonempty state space required")

    def assign(keys: Sequence[Hashable]) -> dict[S, int]:
        ids: dict[Hashable, int] = {}
        out: dict[S, int] = {}
        for state, key in zip(ordered, keys, strict=True):
            out[state] = ids.setdefault(key, len(ids))
        return out

    cls = assign(tuple(observation(s) for s in ordered))
    rounds = 0
    while True:
        rounds += 1
        nxt = assign(tuple((observation(s), cls[transition(s)]) for s in ordered))
        if tuple(nxt[s] for s in ordered) == tuple(cls[s] for s in ordered):
            cls = nxt
            break
        cls = nxt
    source_bits = bit_width(len(ordered) - 1)
    classes = len(set(cls.values()))
    profile = MooreObserverProfile(
        name,
        len(ordered),
        classes,
        source_bits,
        bit_width(classes - 1),
        rounds,
        None if initial_state is None else cls[initial_state],
    )
    return profile, cls


def bounded_future_trace_classes(
    states: Iterable[S],
    transition: Callable[[S], S],
    observation: Callable[[S], ObservationT],
    horizon: int,
) -> int:
    """Count exact length-h future observation words (diagnostic, not a merge proof)."""
    horizon = int(horizon)
    if horizon < 0:
        raise ValueError(horizon)
    words: set[tuple[ObservationT, ...]] = set()
    for source in states:
        state = source
        word: list[ObservationT] = []
        for _ in range(horizon):
            word.append(observation(state))
            state = transition(state)
        words.add(tuple(word))
    return len(words)


def reverse_add_growth_observer_profile() -> ReverseAddGrowthObserverProfile:
    """The carry-growth digit observer is exactly {CONST0, ID, CONST1}."""
    return ReverseAddGrowthObserverProfile()


def reverse_add_admissible_growth_words(horizon: int) -> InformationObserverProfile:
    """Universal growth-language upper bound from the proved no-1111 theorem."""
    h = int(horizon)
    if h < 0:
        raise ValueError(h)
    # Number of binary words of length h avoiding four consecutive growths.
    dp = [1, 0, 0, 0]  # suffix run length 0..3, initially empty
    for _ in range(h):
        ndp = [sum(dp), dp[0], dp[1], dp[2]]
        dp = ndp
    count = sum(dp)
    return InformationObserverProfile(
        "reverse-add-growth-language",
        h,
        count,
        bit_width(count - 1),
        "universal no-four-consecutive-growth language; still exponential in horizon",
    )


def collatz_parity_observer_profile(
    width: int, *, verify: bool = True
) -> InformationObserverProfile:
    """Exact information lower bound from the finite parity-coordinate bijection."""
    width = int(width)
    if width < 0:
        raise ValueError(width)
    count = 1 << width
    if verify and width <= 16:
        actual = {collatz_parity_word(n, width) for n in range(1 << width)}
        if len(actual) != count:
            raise AssertionError((width, len(actual), count))
    return InformationObserverProfile(
        "collatz-parity",
        width,
        count,
        width,
        "Q_k is bijective modulo 2^k, so k future parity bits require k bits universally",
    )


def prime_lane_observer_profile(period: int) -> MooreObserverProfile:
    """Minimal observer for one divisor lane under candidate translation by +2."""
    q = int(period)
    if q < 3 or not (q & 1):
        raise ValueError(q)
    profile, _ = minimize_unary_moore(
        range(q),
        lambda r: (r + 2) % q,
        lambda r: r == 0,
        name=f"prime-lane-{q}",
    )
    if profile.observer_classes != q:
        raise AssertionError((q, profile))
    return profile


def prime_wheel_observer_profile(factors: Sequence[int]) -> MooreObserverProfile:
    """Exact raw-wheel Moore quotient; CRT factorization is needed to store it compactly."""
    fs = tuple(map(int, factors))
    if not fs or any(q < 3 or not (q & 1) for q in fs):
        raise ValueError(fs)
    modulus = prod(fs)
    profile, _ = minimize_unary_moore(
        range(modulus),
        lambda r: (r + 2) % modulus,
        lambda r: gcd(r, modulus) > 1,
        name="prime-wheel-" + "x".join(map(str, fs)),
    )
    if profile.observer_classes != modulus:
        raise AssertionError((fs, profile))
    return profile


def fermat_squaring_observer_profile(index: int) -> MooreObserverProfile:
    """Exact target observer x->x^2 mod F_n for bounded materialized Fermat terms."""
    n = int(index)
    if not 0 <= n <= 4:
        raise ValueError("bounded exact minimization supports F_0..F_4")
    modulus = (1 << (1 << n)) + 1
    profile, _ = minimize_unary_moore(
        range(modulus),
        lambda x: (x * x) % modulus,
        lambda x: x == modulus - 1,
        name=f"fermat-square-F{n}",
        initial_state=3 % modulus,
    )
    expected = (1 << n) + 1
    if profile.observer_classes != expected:
        raise AssertionError((n, profile, expected))
    return profile


def fermat_observer_theory(index: int) -> SpecialObserverTheory:
    n = int(index)
    if n < 0:
        raise ValueError(n)
    bit_length = (1 << n) + 1
    modulus = (1 << (1 << n)) + 1 if n <= 4 else 0
    classes = (1 << n) + 1
    return SpecialObserverTheory(
        "fermat",
        n,
        modulus,
        0 if not modulus else modulus,
        classes,
        bit_width(classes - 1),
        bit_length - 2,
    )


def mersenne_lucas_observer_profile(exponent: int) -> MooreObserverProfile:
    """Exact Moore observer for Lucas--Lehmer's x->x^2-2 recurrence."""
    p = int(exponent)
    if not 2 <= p <= 13:
        raise ValueError("bounded exact minimization supports p<=13")
    modulus = (1 << p) - 1
    profile, _ = minimize_unary_moore(
        range(modulus),
        lambda x: (x * x - 2) % modulus,
        lambda x: x == 0,
        name=f"lucas-lehmer-M{p}",
        initial_state=4 % modulus,
    )
    return profile


def mersenne_observer_theory(exponent: int) -> SpecialObserverTheory:
    p = int(exponent)
    if p < 2:
        raise ValueError(p)
    modulus = (1 << p) - 1 if p <= 13 else 0
    return SpecialObserverTheory(
        "mersenne",
        p,
        modulus,
        0 if not modulus else modulus,
        p,
        bit_width(p - 1),
        max(0, p - 2),
    )


def special_square_sign_quotient_profile(
    family: str,
    parameter: int,
) -> SignQuotientObserverProfile:
    """Exact ``x ~ -x`` quotient of the special-number squaring recurrences.

    Lucas--Lehmer's target ``0`` is fixed by sign, so the representative alone
    is target-safe.  Pepin observes ``-1`` while ``+1`` shares its square, so
    the current target bit is retained alongside the sign representative.
    """
    family = str(family)
    parameter = int(parameter)
    if family == "mersenne":
        width = parameter
        modulus = (1 << width) - 1

        def transition(x: int) -> int:
            return (x * x - 2) % modulus

        def target(x: int) -> bool:
            return x == 0

        def key(x: int) -> int | tuple[bool, int]:
            return binary_square_sign_representative(x, width, 1)
    elif family == "fermat":
        width = 1 << parameter
        modulus = (1 << width) + 1

        def transition(x: int) -> int:
            return (x * x) % modulus

        def target(x: int) -> bool:
            return x == modulus - 1

        def key(x: int) -> int | tuple[bool, int]:
            return (bool(target(x)), binary_square_sign_representative(x, width, -1))
    else:
        raise ValueError(family)

    outputs: dict[Hashable, bool] = {}
    successors: dict[Hashable, Hashable] = {}
    target_ok = next_ok = True
    keys: list[Hashable] = []
    for state in range(modulus):
        current = key(state)
        keys.append(current)
        out = bool(target(state))
        nxt = key(transition(state))
        if current in outputs:
            target_ok &= outputs[current] == out
            next_ok &= successors[current] == nxt
        else:
            outputs[current] = out
            successors[current] = nxt
    return SignQuotientObserverProfile(
        family, parameter, modulus, len(set(keys)), bool(target_ok), bool(next_ok)
    )


def special_prime_assumption_summary() -> tuple[SpecialObserverTheory, ...]:
    return tuple(fermat_observer_theory(n) for n in range(5)) + tuple(
        mersenne_observer_theory(p) for p in (3, 5, 7, 13)
    )


__all__ = [
    "InformationObserverProfile",
    "MooreObserverProfile",
    "ReverseAddGrowthObserverProfile",
    "SignQuotientObserverProfile",
    "SpecialObserverTheory",
    "bounded_future_trace_classes",
    "collatz_parity_observer_profile",
    "fermat_observer_theory",
    "fermat_squaring_observer_profile",
    "mersenne_lucas_observer_profile",
    "mersenne_observer_theory",
    "minimize_unary_moore",
    "prime_lane_observer_profile",
    "prime_wheel_observer_profile",
    "reverse_add_admissible_growth_words",
    "reverse_add_growth_observer_profile",
    "special_prime_assumption_summary",
    "special_square_sign_quotient_profile",
]
