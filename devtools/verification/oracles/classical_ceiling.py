"""Compatibility import for the bounded special-form recurrence oracle."""

from devtools.verification.oracles.special_classical_ceiling import (
    SpecialClassicalCeilingResult,
    fermat_classical_ceiling,
    mersenne_classical_ceiling,
    special_classical_ceiling,
)

__all__ = [
    "SpecialClassicalCeilingResult",
    "fermat_classical_ceiling",
    "mersenne_classical_ceiling",
    "special_classical_ceiling",
]
