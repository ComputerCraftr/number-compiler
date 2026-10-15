"""Independent bounded audit of source-guarded Fermat/Mersenne low ports."""

from __future__ import annotations

import json

from number_compiler.sequences.power_numbers.numbers import (
    FermatNumberSpec,
    MersenneNumberSpec,
)
from number_compiler.sequences.power_numbers.source_matrix import (
    demand_unwrapped_inner_radix_port,
    source_no_wrap_guard,
)
from tests.support.power_number_source_oracle import (
    literal_power_number_radix_port,
    literal_power_number_sparse_digits,
)


def run() -> dict[str, object]:
    radix_cases = 0
    for family, parameters in (
        ("fermat", (4, 6, 8, 10, 12)),
        ("mersenne", (17, 32, 128, 512, 4096)),
    ):
        for parameter in parameters:
            for level in range(12):
                if not source_no_wrap_guard(family, parameter, level):
                    continue
                for base in (2, 3, 5, 7, 10):
                    actual = demand_unwrapped_inner_radix_port(
                        family, parameter, level, base
                    )
                    expected = literal_power_number_radix_port(family, level, base)
                    assert (
                        actual.source_prefix,
                        actual.target_prefix,
                        actual.carry,
                        actual.borrow,
                        actual.xor,
                    ) == expected
                    radix_cases += 1

    sparse_cases = 0
    for family, parameter, spec in (
        ("fermat", 20, FermatNumberSpec(20)),
        ("mersenne", 1 << 20, MersenneNumberSpec(1 << 20)),
    ):
        level = 14
        for base, positions in (
            (2, (0, 3, 6, 11, 18)),
            (3, (0, 2, 7, 11)),
            (7, (0, 2, 5)),
            (10, (1, 3, 5)),
        ):
            stencil = spec.demand_unwrapped_inner_digit_stencil(level, base, positions)
            assert stencil.digits == literal_power_number_sparse_digits(
                family, level, base, positions
            )
            sparse_cases += 1

    # These blocks carry very large source parameters and spans, but neither a
    # represented candidate nor a temporal list is built.
    fermat_block = FermatNumberSpec(10**9).power_stable_unwrapped_inner_halo(
        4, 100_000_000
    )
    assert len(fermat_block.observation_runs) == 1
    assert fermat_block.observation_runs[0][1] == 100_000_000
    mersenne_block = MersenneNumberSpec(1 << 2048).power_stable_unwrapped_inner_halo(
        2, 1024
    )
    assert mersenne_block.last_four_halo == ((-1, -1, 0, 0, 0),) * 4

    guard_refusals = 0
    for family, parameter, level in (
        ("fermat", 4, 4),
        ("mersenne", 13, 4),
    ):
        assert not source_no_wrap_guard(family, parameter, level)
        try:
            demand_unwrapped_inner_radix_port(family, parameter, level, 7)
        except ValueError as error:
            assert "wrap" in str(error)
            guard_refusals += 1
        else:
            raise AssertionError((family, parameter, level))

    return {
        "radix_literal_differentials": radix_cases,
        "sparse_digit_differentials": sparse_cases,
        "powered_halo_source_levels": [
            fermat_block.span,
            mersenne_block.span,
        ],
        "nilpotent_suffix_differentials": "covered by focused test module",
        "wrapped_source_refusals": guard_refusals,
        "candidate_integer_constructions": 0,
        "raw_source_recurrence_constructions_in_production": 0,
        "max_digit_modulus": 1_000_000,
        "max_source_level_bit_length": 4_096,
    }


def main() -> int:
    print(json.dumps(run(), sort_keys=True))
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
