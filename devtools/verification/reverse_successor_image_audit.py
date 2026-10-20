"""Bounded audit of source-free reverse/add successor image identity.

This is a finite research oracle, not a temporal action implementation.  A
source occurrence retains its carry-domain geometry long enough to execute one
successor.  The resulting image ID owns only the canonical exact output word.
It therefore measures occurrence-image aliases without asserting that two
unbound actions are extensionally equal on every future input.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass
from itertools import product

from number_compiler.arithmetic.automata import program_word as words
from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_pair_carry_action,
)


@dataclass(frozen=True, slots=True)
class ReverseSuccessorImageID:
    """Canonical exact output word, with no source geometry in its identity."""

    output: words.CanonicalWord

    def __post_init__(self) -> None:
        if type(self.output) is not words.CanonicalWord or self.output.length < 1:
            raise ValueError("successor images require one nonempty canonical word")


@dataclass(frozen=True, slots=True)
class SourceOccurrenceImageKey:
    """Negative-control key that deliberately retains consumed provenance."""

    source_domains: tuple[CarryFn, ...]
    image: ReverseSuccessorImageID


@dataclass(frozen=True, slots=True)
class BranchImageAudit:
    sources: int
    images: int
    provenance_images: int


@dataclass(frozen=True, slots=True)
class SuccessorImageAudit:
    width: int
    no_growth: BranchImageAudit
    growth: BranchImageAudit
    images: int


def _validate_source(source: tuple[int, ...]) -> None:
    if (
        type(source) is not tuple
        or not source
        or source != source[::-1]
        or any(type(value) is not int or not 0 <= value < 19 for value in source)
        or len(source) % 2
        and source[len(source) // 2] % 2
    ):
        raise ValueError("expected an admissible symmetric decimal pair field")


def source_domain_provenance(source: tuple[int, ...]) -> tuple[CarryFn, ...]:
    """Return source Gamma for the negative control, never for image identity."""
    _validate_source(source)
    return tuple(decimal_pair_carry_action(value) for value in source)


def canonical_successor_image(
    source: tuple[int, ...],
) -> tuple[ReverseSuccessorImageID, int]:
    """Execute the exact finite oracle and intern only its canonical output."""
    _validate_source(source)
    output, growth = pair_step(source, 10)
    return ReverseSuccessorImageID(words.from_values(output)), growth


def occurrence_image_key(source: tuple[int, ...]) -> SourceOccurrenceImageKey:
    image, _growth = canonical_successor_image(source)
    return SourceOccurrenceImageKey(source_domain_provenance(source), image)


def symmetric_sources(
    width: int, *, leading_nonzero: bool = False
) -> Iterator[tuple[int, ...]]:
    if type(width) is not int or not 1 <= width <= 8:
        raise ValueError("bounded successor-image audit supports widths 1..8")
    alphabets = [range(19)] * (width // 2)
    if width % 2:
        alphabets.append(range(0, 19, 2))
    if leading_nonzero:
        alphabets[0] = range(2, 19, 2) if width == 1 else range(1, 19)
    for half in product(*alphabets):
        reflected = half[:-1] if width % 2 else half
        yield half + reflected[::-1]


def audit_width(width: int) -> SuccessorImageAudit:
    """Count exact image keys and the intentionally sourceful control keys.

    The immutable output tuple is the extensional key of the canonical word.
    Keeping tens of thousands of global weak-word roots alive merely to count
    those keys would turn this finite validation into a memory benchmark.  The
    point regressions separately exercise the actual ``CanonicalWord`` owner.
    """
    sources = [0, 0]
    images: tuple[set[tuple[int, ...]], set[tuple[int, ...]]] = (set(), set())
    provenance: tuple[
        set[tuple[tuple[CarryFn, ...], tuple[int, ...]]],
        set[tuple[tuple[CarryFn, ...], tuple[int, ...]]],
    ] = (set(), set())
    all_images: set[tuple[int, ...]] = set()
    for source in symmetric_sources(width):
        output, growth = pair_step(source, 10)
        sources[growth] += 1
        images[growth].add(output)
        provenance[growth].add((source_domain_provenance(source), output))
        all_images.add(output)
    return SuccessorImageAudit(
        width,
        BranchImageAudit(sources[0], len(images[0]), len(provenance[0])),
        BranchImageAudit(sources[1], len(images[1]), len(provenance[1])),
        len(all_images),
    )


__all__ = [
    "BranchImageAudit",
    "ReverseSuccessorImageID",
    "SourceOccurrenceImageKey",
    "SuccessorImageAudit",
    "audit_width",
    "canonical_successor_image",
    "occurrence_image_key",
    "source_domain_provenance",
]
