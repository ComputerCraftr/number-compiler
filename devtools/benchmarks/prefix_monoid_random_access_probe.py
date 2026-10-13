"""Deterministic v0.53.8 spatial-prefix / slab-removal probe."""

from __future__ import annotations

import json

from devtools.experiments.reverse_add.domain import ReverseAddSpatialIndex
from devtools.paths import report_directory, repository_root
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.query_types import ReverseAddTermQuery
from number_compiler.arithmetic.formula.types import RadixSpec
from number_compiler.hashlife.execution.evaluator import materialize_values
from number_compiler.sequences.collatz.parity import (
    CollatzParityCursor,
    collatz_parity_prefix_index,
    collatz_parity_word,
)
from number_compiler.sequences.reverse_add.digits import reverse_add_orbit_formulas

ROOT = repository_root()


def reverse_add_metrics() -> dict[str, object]:
    arena, digit_roots, pair_roots = reverse_add_orbit_formulas(196, 18, base=10)
    rows = []
    for step in (0, 5, 10, 17):
        index = ReverseAddSpatialIndex.build(arena, pair_roots[step], RadixSpec(10))
        target_digits = materialize_values(digit_roots[step + 1])
        projected = tuple(index.next_digit_at(i) for i in range(len(target_digits)))
        assert projected == target_digits
        rows.append(
            {
                "step": step,
                "source_width": index.source_width,
                "target_width": index.target_width,
                "prefix_stages": index.prefix_stages,
                "exact_domain_alphabet": 19,
                "carry_row_materialized": False,
            }
        )

    compiler = NumberCompiler()
    digit = compiler.project_digit(ReverseAddTermQuery(5, seed=196), 4)
    assert digit == 5  # 52514, LSD-first coordinate 4
    return {
        "controls": rows,
        "random_digit": {"index": 5, "position": 4, "digit": digit},
    }


def collatz_metrics() -> dict[str, object]:
    # Use an explicit parity coordinate large enough to expose the old repeated
    # prefix-scan behavior, while keeping this probe deterministic and cheap.
    seed = 27
    width = 4096
    word = collatz_parity_word(seed, width)
    index = collatz_parity_prefix_index(word, width)
    cursor = CollatzParityCursor(word, width)

    def legacy_repeated_prefix_bits(ticks: int) -> int:
        # Reference the pre-v0.53.8 binary search, which recomputed a bit_count
        # over each increasingly large integer prefix.  This is evidence only;
        # the live query path never calls it.
        lo, hi, scanned = 0, width, 0
        while lo < hi:
            mid = (lo + hi + 1) // 2
            scanned += mid
            duration = mid + (word & ((1 << mid) - 1)).bit_count()
            if duration <= ticks:
                lo = mid
            else:
                hi = mid - 1
        return scanned

    rows = []
    from number_compiler.sequences.collatz.parity import advance_collatz_parity

    for ticks in (1, 257, 2048, 4096):
        result = advance_collatz_parity(cursor, ticks)
        rows.append(
            {
                "physical_steps": ticks,
                "consumed_symbols": result.consumed_symbols,
                "summary_queries": result.rank_queries,
                "leaf_bits_examined": result.rank_bits_scanned,
                "legacy_repeated_prefix_bits_reference": legacy_repeated_prefix_bits(
                    ticks
                ),
            }
        )
        assert result.rank_bits_scanned <= 64

    return {
        "explicit_width": width,
        "block_bits": index.block_bits,
        "block_count": index.block_count,
        "index_build_input_blocks": index.block_count,
        "queries": rows,
        "max_leaf_bits_examined": max(r["leaf_bits_examined"] for r in rows),
    }


def structure_metrics() -> dict[str, object]:
    src = ROOT / "src" / "number_compiler"
    removed = [
        "carry_slab_power.py",
        "carry_slab_behavioral.py",
        "carry_slab_jump.py",
        "carry_boundary_power.py",
    ]
    legacy_kinds = (
        "CARRY_SCAN",
        "PREFIX_XOR",
        "SLAB_PAIR_CORE",
        "SLAB_PAIR_BIT",
        "ACTIVE_NEXT",
        "CARRY_EVENT",
        "INTERVAL_TRANSPORT",
        "MODSUM",
    )
    formula_text = "\n".join(
        (src / name).read_text()
        for name in (
            "arithmetic/formula/construction.py",
            "arithmetic/formula/evaluation.py",
            "hashlife/execution/evaluator.py",
            "arithmetic/functions/boolean_residual.py",
        )
    )
    return {
        "removed_slab_modules": {name: not (src / name).exists() for name in removed},
        "legacy_formula_kinds_remaining": [
            kind for kind in legacy_kinds if kind in formula_text
        ],
        "shared_prefix_owner": "src/number_compiler/arithmetic/carry/prefix_monoid.py",
        "reverse_spatial_owner": "devtools/experiments/reverse_add/domain.py",
    }


def main() -> None:
    payload = {
        "release": "v0.53.8",
        "reverse_add": reverse_add_metrics(),
        "collatz": collatz_metrics(),
        "structure": structure_metrics(),
    }
    out = (
        report_directory("devtools.benchmarks.prefix_monoid_random_access_probe")
        / "prefix_monoid_random_access_metrics.json"
    )
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
