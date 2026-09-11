"""Explicit slow/reference special-number oracles.

Nothing under this namespace is imported by the production sequence compiler or
by the package root.  These APIs exist only for differential tests, research,
and release audits.  Importing this namespace is an explicit opt-in to bounded
carrier enumeration or recurrence-equivalent reference arithmetic.
"""

from devtools.proofs.oracles.bounded_filtration import (
    bounded_candidate_image_filtration,
)
from devtools.proofs.oracles.special_binary_jump import (
    SpecialBinaryJumpApplication,
    SpecialBinaryJumpProgram,
    build_fermat_binary_jump,
    build_mersenne_binary_jump,
    fermat_radix_orbit_representative,
    mersenne_sign_representative,
)
from devtools.proofs.oracles.special_power_reference import (
    SpecialPowerApplication,
    apply_special_power_reference,
    bounded_binary_target_jump,
)
from devtools.proofs.oracles.special_primality import (
    LucasLehmerResult,
    PepinResult,
    lucas_lehmer_test,
    pepin_test,
)
from number_compiler.sequences.power_numbers.digit_power import (
    DigitPowerProjectionResult,
    lucas_lehmer_digit_field,
    pepin_digit_field,
)

__all__ = [
    "PepinResult",
    "pepin_test",
    "LucasLehmerResult",
    "lucas_lehmer_test",
    "DigitPowerProjectionResult",
    "lucas_lehmer_digit_field",
    "pepin_digit_field",
    "SpecialBinaryJumpApplication",
    "SpecialBinaryJumpProgram",
    "mersenne_sign_representative",
    "build_mersenne_binary_jump",
    "fermat_radix_orbit_representative",
    "build_fermat_binary_jump",
    "bounded_candidate_image_filtration",
    "SpecialPowerApplication",
    "apply_special_power_reference",
    "bounded_binary_target_jump",
]
