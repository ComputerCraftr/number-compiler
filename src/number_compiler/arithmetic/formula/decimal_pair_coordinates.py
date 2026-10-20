"""Exact local decimal pair coordinates used by the primitive tile kernel.

The coordinate change is bijective on pair symbols ``0..18``. It factors the
normalizer and digit-pair adder into one ``F5`` coordinate and two Boolean
coordinates; it is not an equivalence between different exact outputs.
"""

from __future__ import annotations

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple


def _pair_symbol(value: object) -> int:
    if type(value) is not int:
        raise TypeError("decimal pair symbols require exact integers")
    if not 0 <= value <= 18:
        raise ValueError("decimal pair symbol lies outside 0..18")
    return value


def _carry_bit(value: object) -> int:
    if type(value) is not int:
        raise TypeError("decimal pair carries require exact integers")
    if value not in (0, 1):
        raise ValueError("decimal pair carry must be zero or one")
    return value


def _normalized_coordinate(value: object) -> tuple[int, int]:
    if not is_exact_object_tuple(value) or len(value) != 2:
        raise TypeError("normalized decimal coordinates require an immutable pair")
    alpha, beta = value
    if (
        type(alpha) is not int
        or not 0 <= alpha < 5
        or type(beta) is not int
        or beta not in (0, 1)
    ):
        raise ValueError("normalized decimal coordinate lies outside F5 x F2")
    return alpha, beta


def _carry_domain(value: object) -> CarryFn:
    if type(value) is not CarryFn:
        raise TypeError("decimal carry domains require a CarryFn")
    return value


def decimal_pair_coordinates(symbol: int) -> tuple[int, int, int]:
    """Return the exact ``F5 x F2 x F2`` coordinates of one pair symbol."""
    value = _pair_symbol(symbol)
    return value % 5, value % 10 // 5, value // 10


def decimal_factored_coordinates(symbol: int) -> tuple[CarryFn, int, int]:
    """Return the exact ``(domain, F5, F2)`` carrier of one pair symbol.

    ``CarryFn.CONST0``, ``CarryFn.ID``, and ``CarryFn.CONST1`` are respectively
    the canonical LT, EQ, and GT domains.  The high decimal coordinate is
    therefore derived rather than retained.
    """
    value = _pair_symbol(symbol)
    return decimal_kernel_carry_action(value), value % 5, value % 10 // 5


def decimal_cocycle_coordinates(symbol: int) -> tuple[CarryFn, int, int]:
    """Return ``(domain, alpha, epsilon)`` with the low-digit parity cocycle."""
    value = _pair_symbol(symbol)
    digit = value % 10
    return decimal_kernel_carry_action(value), digit % 5, digit % 2


def decimal_crt_digit(alpha: int, epsilon: int) -> int:
    """Recover the unique decimal digit with given F5 residue and parity."""
    phase, parity = _normalized_coordinate((alpha, epsilon))
    return phase if phase % 2 == parity else phase + 5


def decimal_cocycle_domain(alpha: int, epsilon: int, kappa: int) -> CarryFn:
    """Classify an output from its CRT digit and isolated decimal carry."""
    digit = decimal_crt_digit(alpha, epsilon)
    high = _carry_bit(kappa)
    value = digit + 10 * high
    if value > 18:
        raise ValueError("cocycle coordinates lie outside the decimal pair image")
    return decimal_kernel_carry_action(value)


def decimal_cocycle_value(domain: CarryFn, alpha: int, epsilon: int) -> int:
    """Decode one admissible ``(domain, F5, parity)`` pair carrier."""
    function = _carry_domain(domain)
    digit = decimal_crt_digit(alpha, epsilon)
    is_eq_value = digit == 9
    if function is CarryFn.ID:
        if not is_eq_value:
            raise ValueError("EQ requires the exact decimal pair value 9")
        return 9
    if is_eq_value:
        raise ValueError("the exact decimal pair value 9 requires EQ")
    return digit + 10 * int(function is CarryFn.CONST1)


def decimal_factored_value(domain: CarryFn, alpha: int, beta: int) -> int:
    """Decode one admissible factored carrier without a 19-symbol lookup."""
    function = _carry_domain(domain)
    phase, half = _normalized_coordinate((alpha, beta))
    is_eq_value = phase == 4 and half == 1
    if function is CarryFn.ID:
        if not is_eq_value:
            raise ValueError("EQ requires the exact decimal pair value 9")
        return 9
    if is_eq_value:
        raise ValueError("the exact decimal pair value 9 requires EQ")
    high = int(function is CarryFn.CONST1)
    return phase + 5 * half + 10 * high


def decimal_pair_value(coordinates: tuple[int, int, int]) -> int:
    """Invert :func:`decimal_pair_coordinates` on its 19-element image."""
    if type(coordinates) is not tuple or len(coordinates) != 3:
        raise TypeError("decimal pair coordinates require an immutable triple")
    alpha, beta, nu = coordinates
    if (
        type(alpha) is not int
        or not 0 <= alpha < 5
        or type(beta) is not int
        or beta not in (0, 1)
        or type(nu) is not int
        or nu not in (0, 1)
        or coordinates == (4, 1, 1)
    ):
        raise ValueError("coordinates lie outside the decimal pair image")
    return alpha + 5 * beta + 10 * nu


def decimal_pair_carry_action(symbol: int) -> CarryFn:
    """Project one exact pair symbol onto its three-element carry action."""
    return decimal_kernel_carry_action(_pair_symbol(symbol))


def decimal_q95(symbol: int, forcing: int) -> int:
    """Exact output carrier plus F5 forcing, with no incoming-carry coordinate.

    Forgetting homogeneous F2 forcing requires separate source admission;
    encoding this local alphabet alone does not establish that admission.
    """
    value = _pair_symbol(symbol)
    if type(forcing) is not int or not 0 <= forcing < 5:
        raise ValueError("Q95 forcing must be an exact F5 integer")
    return 5 * value + forcing


def decimal_q95_coordinates(value: int) -> tuple[int, int]:
    """Decode the fixed Q95 alphabet; spatial carry is derived from its output."""
    if type(value) is not int or not 0 <= value < 95:
        raise ValueError("Q95 requires an exact integer in 0..94")
    return divmod(value, 5)


def decimal_kernel_carry_action(symbol: int) -> CarryFn:
    """Carry projection after the primitive kernel has admitted ``symbol``."""
    if symbol == 9:
        return CarryFn.ID
    return CarryFn.CONST1 if symbol > 9 else CarryFn.CONST0


def decimal_normalized_coordinates(symbol: int, carry: int) -> tuple[int, int]:
    """Normalize a pair coefficient to one exact decimal digit in ``F5 x F2``."""
    alpha, beta, _nu = decimal_pair_coordinates(symbol)
    return decimal_normalize_factored(alpha, beta, carry)


def decimal_normalize_factored(alpha: int, beta: int, carry: int) -> tuple[int, int]:
    """Normalize native ``F5 x F2`` channels with one incoming carry bit."""
    phase, half = _normalized_coordinate((alpha, beta))
    incoming = _carry_bit(carry)
    wrap = int(phase == 4 and incoming == 1)
    return (phase + incoming) % 5, half ^ wrap


def decimal_normalize_cocycle(alpha: int, epsilon: int, carry: int) -> tuple[int, int]:
    """Normalize the F5/parity channels; decimal wrap needs no extra gate."""
    phase, parity = _normalized_coordinate((alpha, epsilon))
    incoming = _carry_bit(carry)
    return (phase + incoming) % 5, parity ^ incoming


def decimal_cocycle_kappa(left: tuple[int, int], right: tuple[int, int]) -> int:
    """Return the isolated high decimal carry of two normalized CRT digits."""
    left_alpha, left_parity = _normalized_coordinate(left)
    right_alpha, right_parity = _normalized_coordinate(right)
    left_digit = decimal_crt_digit(left_alpha, left_parity)
    right_digit = decimal_crt_digit(right_alpha, right_parity)
    return int(left_digit + right_digit >= 10)


def decimal_add_cocycle(
    left: tuple[int, int], right: tuple[int, int]
) -> tuple[CarryFn, int, int, int]:
    """Add normalized F5/parity channels and expose the decimal carry cocycle."""
    left_alpha, left_parity = _normalized_coordinate(left)
    right_alpha, right_parity = _normalized_coordinate(right)
    alpha = (left_alpha + right_alpha) % 5
    epsilon = left_parity ^ right_parity
    kappa = decimal_cocycle_kappa(left, right)
    return decimal_cocycle_domain(alpha, epsilon, kappa), alpha, epsilon, kappa


def decimal_add_normalized(
    left: tuple[int, int], right: tuple[int, int]
) -> tuple[int, int, int]:
    """Add two normalized digits through ``F5`` addition and one full adder."""
    domain, alpha, beta = decimal_add_factored(left, right)
    return alpha, beta, int(domain is CarryFn.CONST1)


def decimal_add_factored(
    left: tuple[int, int], right: tuple[int, int]
) -> tuple[CarryFn, int, int]:
    """Combine two normalized channels into an exact factored pair carrier."""
    left_alpha, left_beta = _normalized_coordinate(left)
    right_alpha, right_beta = _normalized_coordinate(right)
    phase_sum = left_alpha + right_alpha
    threshold = int(phase_sum >= 5)
    alpha = phase_sum % 5
    beta = left_beta ^ right_beta ^ threshold
    high = int(left_beta + right_beta + threshold >= 2)
    domain = (
        CarryFn.CONST1
        if high
        else CarryFn.ID
        if alpha == 4 and beta == 1
        else CarryFn.CONST0
    )
    return domain, alpha, beta


def decimal_normalized_pair_sum(
    left_symbol: int,
    left_carry: int,
    right_symbol: int,
    right_carry: int,
) -> int:
    """Return the exact pair sum of two normalized pair coefficients."""
    return decimal_kernel_pair_sum(
        _pair_symbol(left_symbol),
        _carry_bit(left_carry),
        _pair_symbol(right_symbol),
        _carry_bit(right_carry),
    )


def decimal_kernel_pair_sum(
    left_symbol: int,
    left_carry: int,
    right_symbol: int,
    right_carry: int,
) -> int:
    """Allocation-free factored sum after primitive input admission."""
    left_alpha = left_symbol % 5
    right_alpha = right_symbol % 5
    left_phase = (left_alpha + left_carry) % 5
    right_phase = (right_alpha + right_carry) % 5
    left_binary = left_symbol % 10 // 5 ^ int(left_alpha == 4 and left_carry == 1)
    right_binary = right_symbol % 10 // 5 ^ int(right_alpha == 4 and right_carry == 1)
    phase_sum = left_phase + right_phase
    binary_sum = left_binary + right_binary + int(phase_sum >= 5)
    return phase_sum % 5 + 5 * (binary_sum % 2) + 10 * int(binary_sum >= 2)


__all__ = [
    "decimal_add_cocycle",
    "decimal_add_factored",
    "decimal_add_normalized",
    "decimal_cocycle_coordinates",
    "decimal_cocycle_domain",
    "decimal_cocycle_kappa",
    "decimal_cocycle_value",
    "decimal_crt_digit",
    "decimal_factored_coordinates",
    "decimal_factored_value",
    "decimal_normalize_cocycle",
    "decimal_normalize_factored",
    "decimal_normalized_coordinates",
    "decimal_normalized_pair_sum",
    "decimal_pair_carry_action",
    "decimal_pair_coordinates",
    "decimal_pair_value",
    "decimal_q95",
    "decimal_q95_coordinates",
]
