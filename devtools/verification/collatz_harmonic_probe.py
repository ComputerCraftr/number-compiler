"""Exact Collatz harmonic controls; reported projections are not temporal IDs."""

from __future__ import annotations

import argparse
import json
from itertools import product

from devtools.verification import exact_oracle
from devtools.verification.collatz_harmonic_ports import (
    ZERO,
    Radix64OutputHarmonicAction,
    WireResponse,
    binary_carry_birth,
    binary_jet,
)
from devtools.verification.collatz_harmonic_ports import (
    Radix64WireHarmonicAction as Action,
)
from number_compiler.arithmetic.carry.collatz_carry_wires import CollatzCarryWires
from number_compiler.arithmetic.carry.collatz_output_quotient import DOMAIN_ACTIONS
from number_compiler.arithmetic.fields.radix import digits_lsd, value_from_lsd_digits
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.arithmetic.polynomials.primary_jet import (
    PrimaryJetAffineMorphism,
    primary_jet_from_digits,
)
from number_compiler.sequences.collatz.raw_field import (
    summarize_collatz_sentinel_boundaries,
)


def spatial() -> dict[str, object]:
    leaves = tuple(Action.digit(d) for d in (0, 21, 22, 42, 43))
    current = {Action.identity().response_key: Action.identity()}
    counts = []
    transitions = 0
    witnesses: dict[tuple[WireResponse, WireResponse], tuple[int, ...]] = {
        Action.identity().response_key: ()
    }
    for width in range(1, 9):
        following = {}
        next_words = {}
        for key, before in current.items():
            for digit, leaf in zip((0, 21, 22, 42, 43), leaves, strict=True):
                after = before.then(leaf)
                assert after.domain == leaf.domain.after(before.domain)
                following[after.response_key] = after
                next_words[after.response_key] = witnesses[key] + (digit,)
                transitions += 1
        current, witnesses = following, next_words
        assert {a.domain.outputs for a in current.values()} == set(DOMAIN_ACTIONS)
        counts.append(len(current))
        # Every retained response has an exact digit-word witness. Check all
        # three staircase ports using raw arithmetic, not response composition.
        for key, action in current.items():
            for incoming in range(3):
                carry = incoming
                lower, upper = [], []
                for digit in witnesses[key]:
                    lower.append(int(carry >= 1))
                    upper.append(int(carry == 2))
                    carry = (3 * digit + carry) // 64
                assert action.domain.apply(incoming) == carry
                assert (
                    action.lower.emit(int(incoming >= 1))
                    == primary_jet_from_digits(lower, degree=5, modulus=2).jet
                )
                assert (
                    action.upper.emit(int(incoming == 2))
                    == primary_jet_from_digits(upper, degree=5, modulus=2).jet
                )
    return {
        "length_counts": counts,
        "generator_transitions": transitions,
        "nonempty_domain_actions": list(DOMAIN_ACTIONS),
        "identity": CollatzCarryWires.identity().outputs,
    }


def temporal(chunk: int) -> dict[str, object]:
    if not 0 <= chunk < 16:
        raise ValueError("sixteen-bit sweep uses sixteen fixed chunks")
    checked = empty = even_tails = 0
    phases = set()
    for n in range(4096 * chunk + 1, 4096 * (chunk + 1), 2):
        digits = digits_lsd(n, 64)
        boundary = summarize_collatz_sentinel_boundaries(digits, base=64)
        q = boundary.length if boundary.all_sentinel else boundary.low_first_mismatch
        assert q is not None
        normalized = digits[q:]
        if not normalized:
            empty += 1
            continue
        m = value_from_lsd_digits(normalized, 64)
        valuation = v2_positive(3 * m + 1)
        assert valuation < 6
        action = PrimaryJetAffineMorphism.binary_event(valuation, binary_carry_birth(m))
        target = (3 * m + 1) >> valuation
        assert action.apply(binary_jet(m)) == binary_jet(target)
        assert v2_positive(3 * n + 1) == 6 * q + valuation
        phases.add(valuation)
        even_tails += int(m % 2 == 0)
        checked += 1
    return {
        "chunk": chunk,
        "sources": 2048,
        "nonempty_tails": checked,
        "empty_tails": empty,
        "even_normalized_tails": even_tails,
        "phases": sorted(phases),
    }


def death() -> dict[str, object]:
    actions = tuple(PrimaryJetAffineMorphism.binary_event(e, ZERO) for e in range(6))
    count = 0
    for phases in product(range(6), repeat=5):
        combined = PrimaryJetAffineMorphism.identity(5, 32)
        for e in phases:
            combined = combined.then(actions[e])
        assert combined.kernel == ZERO
        count += 1
    return {
        "phase_sequences": count,
        "linear_source_death": True,
        "nonlinear_closure_inferred": False,
    }


def phase_normalization() -> dict[str, int]:
    """Count canonical zero-run actions after removing exact extent."""
    lengths = range(1, 33)
    wire = {Action.from_digits((0,) * length) for length in lengths}
    output = {
        Radix64OutputHarmonicAction.from_digits((0,) * length) for length in lengths
    }
    return {
        "occurrence_extents": 32,
        "wire_action_ids": len(wire),
        "output_action_ids": len(output),
        "wire_potential_reuses": 32 - len(wire),
        "output_potential_reuses": 32 - len(output),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "mode", choices=("spatial", "temporal", "death", "phase-normalization")
    )
    parser.add_argument("--chunk", type=int, default=0)
    args = parser.parse_args()
    with exact_oracle():
        result = (
            temporal(args.chunk)
            if args.mode == "temporal"
            else spatial()
            if args.mode == "spatial"
            else death()
            if args.mode == "death"
            else phase_normalization()
        )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
