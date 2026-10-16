"""Bounded image identity stays separate from free temporal action identity."""

from dataclasses import fields

from devtools.verification.reverse_successor_image_audit import (
    ReverseSuccessorImageID,
    canonical_successor_image,
    occurrence_image_key,
    source_domain_provenance,
)
from number_compiler.arithmetic.automata import program_word as words


def test_growth_collision_consumes_source_gamma_before_image_identity() -> None:
    first = (10, 0, 0, 10)
    second = (10, 9, 9, 10)
    first_image, first_growth = canonical_successor_image(first)
    second_image, second_growth = canonical_successor_image(second)

    assert first_growth == second_growth == 1
    assert source_domain_provenance(first) != source_domain_provenance(second)
    assert first_image == second_image
    assert first_image.output == words.from_values((1, 1, 0, 1, 1))
    assert occurrence_image_key(first) != occurrence_image_key(second)
    assert tuple(field.name for field in fields(ReverseSuccessorImageID)) == ("output",)


def test_image_identity_is_not_a_free_function_action_claim() -> None:
    first = (10, 0, 0, 10)
    second = (10, 9, 9, 10)
    image, _growth = canonical_successor_image(first)

    # The exact bounded images alias, while their source occurrences remain
    # distinguishable.  No unbound action or future-class ID is constructed.
    assert canonical_successor_image(second)[0] == image
    assert occurrence_image_key(first).source_domains != (
        occurrence_image_key(second).source_domains
    )
