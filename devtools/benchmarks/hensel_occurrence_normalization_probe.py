"""Actual interner reuse across equivalent bounded affine suffix requests."""

from __future__ import annotations

import json

from devtools.verification import exact_oracle
from number_compiler.arithmetic.automata.program_word import from_values
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.sequences.collatz.hensel_occurrence import (
    CollatzHenselAction,
    CollatzHenselOccurrenceCarrier,
)


def report() -> dict[str, int | bool]:
    carrier = CollatzHenselOccurrenceCarrier()
    raw = set()
    values = set()
    for h in range(4):
        coefficient = 2 * 3**h
        for b in range(1, coefficient, 2):
            for m in range(32):
                representations = [(1, b, m)]
                if m % 2 == 0:
                    representations.append((2, b, m // 2))
                if m:
                    representations.append((1, b + coefficient, m - 1))
                expected = coefficient * m + b
                occurrences = []
                for a, offset, suffix in representations:
                    raw.add((a, h, offset, suffix))
                    occurrence = carrier.reimage(
                        CollatzHenselAction(a, h, offset),
                        from_values(digits_lsd(suffix, 4)),
                    )
                    assert occurrence.value == expected
                    assert occurrence.a == 1
                    occurrences.append(occurrence)
                    values.add(expected)
                assert all(row is occurrences[0] for row in occurrences)
    return {
        "raw_representations": len(raw),
        "canonical_occurrences": len(carrier._occurrences),
        "distinct_values": len(values),
        "carrier_hits": carrier.hits,
        "requests": carrier.requests,
        "physical_scheduler_integration": False,
    }


def _command() -> None:
    with exact_oracle():
        print(json.dumps(report(), indent=2))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(_command))
