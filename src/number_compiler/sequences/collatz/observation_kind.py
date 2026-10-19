"""Typed identities for Collatz event-prefix observations."""

from __future__ import annotations

from enum import Enum


class CollatzObservationKind(Enum):
    """Family-owned observer operations; values are stable packet spellings."""

    CLOCK = "clock"
    MODULAR = "modular"
    TWISTED = "twisted"
    HASSE = "hasse"
    HENSEL = "hensel"
    TROPICAL = "tropical"
    FACTOR = "factor"
    SAFETY = "safety"
