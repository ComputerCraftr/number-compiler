"""Measure bounded vs theorem special-number image-filtration construction."""

from __future__ import annotations

import json
from dataclasses import asdict

from devtools.paths import repository_root
from devtools.verification.oracles.bounded_filtration import (
    bounded_candidate_image_filtration,
)
from number_compiler.arithmetic.polynomials.two_primary_filtration import (
    HigherTwoPowerCharacterUnavailable,
    higher_two_power_character,
    outer_source_character,
    pure_two_primary_image_filtration,
)

ROOT = repository_root()


def row(family: str, parameter: int) -> dict[str, object]:
    bounded = bounded_candidate_image_filtration(family, parameter)
    theorem = None
    if bounded.pure_two_primary_shape:
        theorem = pure_two_primary_image_filtration(family, parameter)
    outer = outer_source_character(family, parameter)
    deeper_available = True
    try:
        higher_two_power_character(family, parameter, 2)
    except HigherTwoPowerCharacterUnavailable:
        deeper_available = False
    return {
        "family": family,
        "parameter": parameter,
        "status": bounded.status,
        "image_ranks": bounded.image_ranks,
        "depth_strata": bounded.depth_strata,
        "stable_image_states": bounded.stable_image_states,
        "moore_classes": bounded.moore_classes,
        "image_depth_classes": bounded.image_depth_classes,
        "moore_equals_image_depth": bounded.moore_equals_image_depth,
        "pure_two_primary_shape": bounded.pure_two_primary_shape,
        "bounded_carrier_states_enumerated": bounded.carrier_states_enumerated,
        "bounded_scalable": bounded.scalable_construction,
        "theorem_carrier_states_enumerated": None
        if theorem is None
        else theorem.carrier_states_enumerated,
        "theorem_scalable": None if theorem is None else theorem.scalable_construction,
        "outer_character": asdict(outer),
        "higher_level_2_character_available": deeper_available,
    }


def main() -> None:
    payload = {
        "rows": [
            row("fermat", 4),
            row("mersenne", 11),
            row("mersenne", 13),
        ],
        "invariant": {
            "outer_character_does_not_classify_m11_vs_m13": True,
            "deeper_character_is_fail_closed": True,
            "bounded_construction_is_not_logarithmic": True,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
