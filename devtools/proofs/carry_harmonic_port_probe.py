"""Reproducible finite/spatial/trajectory controls; no production admission."""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from itertools import product

from devtools.proofs import exact_oracle
from devtools.proofs.carry_harmonic_ports import (
    CarryHarmonicPortAction as Action,
    PortRows,
    compose_rows,
    harmonic_sum,
    prefix_harmonics,
)
from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    scan_carry_automaton,
    value_carry_fn,
)
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.fields.radix import reverse_pair_sums

DOMAINS = tuple(CarryFn)
SYMBOLS = (0, 9, 10)
LEAVES = tuple(Action.leaf(domain) for domain in DOMAINS)


def direct_rows(word: tuple[int, ...], *, border: bool = False) -> PortRows:
    """Independent existing carry-scan owner, observed only in the proof oracle."""
    rows = []
    for incoming in (0, 1):
        carry = scan_carry_automaton(word, incoming=incoming).boundaries
        values = (
            tuple(b - a for a, b in zip(carry, carry[1:])) if border else carry[:-1]
        )
        rows.append((carry[-1], *harmonic_sum(values)))
    return rows[0], rows[1]


def finite() -> dict[str, object]:
    reached = {Action.empty().rows}
    period_start: set[PortRows] | None = None
    rows = []
    for width in range(1, 31):
        reached = {
            compose_rows(left, leaf.rows, (width - 1) % 2)
            for left in reached
            for leaf in LEAVES
        }
        border = {Action(width, row).border_rows() for row in reached}
        codes = {Action(width, row).length_indexed_code() for row in reached}
        assert len(codes) == len(reached)
        if width == 18:
            period_start = reached
        if width == 28:
            # Same exact set and same spatial phase imply all subsequent
            # layers repeat after ten, by deterministic generator expansion.
            assert reached == period_start
        rows.append({"width": width, "occupancy": len(reached), "border": len(border)})
    initial = (0, Action.empty().rows)
    seen = {initial}
    pending = [initial]
    for parity, state in pending:
        for leaf in LEAVES:
            target = (1 - parity, compose_rows(state, leaf.rows, parity))
            if target not in seen:
                seen.add(target)
                pending.append(target)
    return {
        "fixed_length_counts": rows,
        "phase_typed_states": len(seen),
        "untyped_emission_rows": len({state for _, state in seen}),
        "all_eq_emissions": len({prefix_harmonics(n) for n in range(10)}),
        "generator_transitions_checked": 3 * len(seen),
        "reachable_layer_period": 10,
        "periodicity_start": 18,
    }


def spatial() -> dict[str, object]:
    comparisons = 0
    for width in range(1, 9):
        for indices in product(range(3), repeat=width):
            word = tuple(SYMBOLS[i] for i in indices)
            full = direct_rows(word)
            borders = direct_rows(word, border=True)
            prefixes = [Action.empty()]
            suffixes = [Action.empty()]
            for i in indices:
                prefixes.append(prefixes[-1].then(LEAVES[i]))
            for i in reversed(indices):
                suffixes.append(LEAVES[i].then(suffixes[-1]))
            for split in range(width + 1):
                left, right = prefixes[split], suffixes[width - split]
                assert left.then(right).rows == full
                assert (
                    compose_rows(left.border_rows(), right.border_rows(), split % 2)
                    == borders
                )
                comparisons += 2
    assert comparisons == 167304
    return {"composition_comparisons": comparisons, "mismatches": 0}


def parameterization() -> dict[str, object]:
    words = 0
    border_forward: dict[tuple[int, ...], PortRows] = {}
    border_backward: dict[PortRows, tuple[int, ...]] = {}
    for width in range(1, 11):
        forward: dict[tuple[int, ...], PortRows] = {}
        backward: dict[PortRows, tuple[int, ...]] = {}
        for indices in product(range(3), repeat=width):
            action = Action.from_domains(DOMAINS[i] for i in indices)
            code = action.length_indexed_code()
            decisive = next((i for i, d in enumerate(indices) if d != 1), None)
            assert code == (
                (0,)
                if decisive is None
                else (1, action.rows[0][0], (decisive + 1) % 10, *action.rows[0][1:])
            )
            assert forward.setdefault(code, action.rows) == action.rows
            assert backward.setdefault(action.rows, code) == code
            flux = action.border_rows()
            border_code: tuple[int, ...]
            if decisive is None:
                border_code = (0,)
                assert flux == ((0, 0, 0), (1, 0, 0))
            else:
                outgoing, f0, f1 = flux[0]
                border_code = (1, outgoing, decisive % 2, f0)
                w0, w1 = (2, 3) if decisive % 2 else (1, 1)
                assert f1 == (2 * f0 - outgoing) % 5
                assert flux[1] == (outgoing, (f0 - w0) % 5, (f1 - w1) % 5)
            assert border_forward.setdefault(border_code, flux) == flux
            assert border_backward.setdefault(flux, border_code) == border_code
            words += 1
    assert words == 88572
    assert len(border_forward) == len(border_backward) == 21
    return {"words": words, "length_indexed_bijection": True, "border_codes": 21}


def trajectory() -> dict[str, object]:
    lengths = (8, 16, 32, 64, 128)
    words: dict[int, set[tuple[CarryFn, ...]]] = {n: set() for n in lengths}
    occupancy: dict[int, set[PortRows]] = {n: set() for n in lengths}
    border: dict[int, set[PortRows]] = {n: set() for n in lengths}
    successors: dict[tuple[int, PortRows], set[tuple[int, PortRows]]] = defaultdict(set)
    source = reverse_pair_sums(196, 10)
    previous: tuple[int, PortRows] | None = None
    for _ in range(1025):
        domains = tuple(value_carry_fn(v, 10) for v in source)
        whole = Action.from_domains(domains)
        current = len(source) % 2, whole.rows
        if previous is not None:
            successors[previous].add(current)
        # Sample the 1,024 successor states S1..S1024; S0 has no full size-8 block.
        if _ > 0:
            for width in lengths:
                for start in range(0, len(domains) - width + 1, width):
                    word = domains[start : start + width]
                    words[width].add(word)
                    block = Action.from_domains(word)
                    occupancy[width].add(block.rows)
                    border[width].add(block.border_rows())
        previous = current
        if _ < 1024:
            source = pair_step(source, 10)[0]
    return {
        "oracle_successors": 1024,
        "aligned_block_state_range": [1, 1024],
        "whole_transition_source_range": [0, 1023],
        "whole_source_keys": len(successors),
        "conflicted_keys": sum(len(targets) > 1 for targets in successors.values()),
        "aligned_blocks": [
            {
                "width": n,
                "domain_words": len(words[n]),
                "occupancy": len(occupancy[n]),
                "border": len(border[n]),
            }
            for n in lengths
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "mode", choices=("finite", "spatial", "parameterization", "trajectory")
    )
    args = parser.parse_args()
    with exact_oracle():
        result = {
            "finite": finite,
            "spatial": spatial,
            "parameterization": parameterization,
            "trajectory": trajectory,
        }[args.mode]()
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
