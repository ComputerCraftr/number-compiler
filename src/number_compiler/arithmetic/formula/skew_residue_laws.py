"""Exact decimal skew coordinates; derived views are never carrier identity.

The 19 reachable (domain, mod9) pairs encode 0..18 exactly. This is not a
nine-state temporal quotient. The normalization law is total on the 27 input
pairs, with nonzero EQ residues excluded by the action admission predicate.
"""

from number_compiler.arithmetic.carry.carry_monoid import CarryFn, apply_carry_fn


def skew_pair_value(domain: int, residue: int) -> int:
    """Decode only at an explicitly requested observation boundary."""
    if type(domain) is not int or domain not in (0, 1, 2):
        raise ValueError("invalid skew domain")
    if type(residue) is not int or not 0 <= residue < 9:
        raise ValueError("invalid mod9 residue")
    if domain == 1:
        if residue:
            raise ValueError("EQ requires zero mod9 residue")
        return 9
    return residue if domain == 0 else (residue + 9 if residue else 18)


def skew_normalized_digit(domain: int, residue: int, incoming: int) -> int:
    """Local consumer law D=u+9z-rho, with no retained q/reset coordinate."""
    outgoing = apply_carry_fn(tuple(CarryFn)[domain], incoming)
    zero_lift = int(residue == 0 and (domain == 2 or domain == 1 and incoming == 0))
    return residue + 9 * zero_lift - outgoing + incoming
