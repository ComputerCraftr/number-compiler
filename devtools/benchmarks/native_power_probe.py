"""Probe the root-level native T^2 construction against successor replay.

This intentionally measures the formula construction that now exists.  It does
*not* report a native bimachine state count: lowering the fully substituted T^2
formula relation into a quotient-during-construction bimachine is the next
separate experiment.
"""

from __future__ import annotations

from devtools.verification.oracles.sequence_arithmetic import (
    reference_successor as reference_successor,
)
import json
import random
import time
from typing import NotRequired, TypedDict

from devtools.benchmarks.probe_support import symmetric_word
from devtools.experiments.reverse_add.native_power import (
    native_four_step,
    native_two_step,
)
from devtools.paths import report_output, repository_root
from number_compiler.arithmetic.formula.derived import successor
from number_compiler.arithmetic.formula.formula import (
    FormulaArena,
    formula_metrics,
    root_from_values,
)
from number_compiler.arithmetic.formula.types import RadixSpec
from number_compiler.hashlife.execution.evaluator import materialize_values

HERE = repository_root()


class ConstructionMetrics(TypedDict):
    values: list[int]
    formula: dict[str, int]
    arena_nodes_added: int
    metadata_entries_added: int
    derived_cache_entries: int
    closed_bits_total: int
    closed_bits_before: NotRequired[int]


def construction_metrics(native: bool) -> ConstructionMetrics:
    spec = RadixSpec(10)
    arena = FormulaArena()
    source = root_from_values((7, 18, 7), arena, spec)
    before_meta = len(arena._metadata)
    before_nodes = arena.unique_nodes
    before_closed = arena.cached_closed_bits
    if native:
        out = native_two_step(arena, source, spec)
    else:
        out = successor(arena, successor(arena, source, spec), spec)
    return {
        "values": list(materialize_values(out)),
        "formula": formula_metrics(out),
        "arena_nodes_added": arena.unique_nodes - before_nodes,
        "metadata_entries_added": len(arena._metadata) - before_meta,
        "derived_cache_entries": len(arena._derived),
        "closed_bits_total": arena.cached_closed_bits,
        "closed_bits_before": before_closed,
    }


def four_step_construction_metrics(native: bool) -> ConstructionMetrics:
    spec = RadixSpec(10)
    arena = FormulaArena()
    source = root_from_values((7, 18, 7), arena, spec)
    before_meta = len(arena._metadata)
    before_nodes = arena.unique_nodes
    if native:
        out = native_four_step(arena, source, spec)
    else:
        out = native_two_step(arena, native_two_step(arena, source, spec), spec)
    return {
        "values": list(materialize_values(out)),
        "formula": formula_metrics(out),
        "arena_nodes_added": arena.unique_nodes - before_nodes,
        "metadata_entries_added": len(arena._metadata) - before_meta,
        "derived_cache_entries": len(arena._derived),
        "closed_bits_total": arena.cached_closed_bits,
    }


def main() -> None:
    rng = random.Random(0x1962002)
    randomized = 0
    for base in range(2, 18):
        spec = RadixSpec(base)
        for _ in range(25):
            values = symmetric_word(rng, base, rng.randint(1, 20))
            expected = reference_successor(reference_successor(values, base), base)
            arena = FormulaArena()
            source = root_from_values(values, arena, spec)
            actual = materialize_values(native_two_step(arena, source, spec))
            assert actual == expected
            randomized += 1

    spec = RadixSpec(10)
    arena = FormulaArena()
    root = root_from_values((7, 18, 7), arena, spec)
    values = (7, 18, 7)
    t0 = time.perf_counter()
    for _ in range(100):
        root = native_two_step(arena, root, spec)
        values = reference_successor(reference_successor(values, 10), 10)
    seconds = time.perf_counter() - t0
    assert materialize_values(root) == values

    previous = json.loads(
        (
            HERE
            / "results"
            / "historical-root-checkpoints"
            / "early_canonical_metrics.json"
        ).read_text()
    )["t2"]
    native_two = construction_metrics(True)
    reference_two = construction_metrics(False)
    native_four = four_step_construction_metrics(True)
    reference_four = four_step_construction_metrics(False)
    data = {
        "native_contract": {
            "calls_successor": False,
            "intermediate_formula_root": False,
            "intermediate_value_sets": False,
            "tau_or_k_cached_as_semantic_objects": False,
            "final_pair_root_cached_by_canonical_source": True,
        },
        "seed_196_two_step": {
            "native": native_two,
            "composed_successor_reference": reference_two,
        },
        "randomized_exact_cases": randomized,
        "native_t2_repeated": {
            "applications": 100,
            "ordinary_steps": 200,
            "seconds": seconds,
            "final_width": root.width,
            "arena_nodes": arena.unique_nodes,
            "final_formula": formula_metrics(root),
        },
        "seed_196_four_step": {
            "native": native_four,
            "t2_squared_formula_reference": reference_four,
        },
        "existing_composed_bimachine_t2": {
            "left": previous["left"],
            "right": previous["right"],
            "primitive_left_states": previous["primitive_left_states"],
            "primitive_right_states": previous["primitive_right_states"],
        },
        "native_bimachine_lowering": None,
        "next_experiment": (
            "lower fully substituted native T2 and native T4 formulas directly into canonical "
            "residual predicates and compare their machines with composed T2 and T2-o-T2"
        ),
    }
    (HERE / "results" / "native_power_metrics.json").write_text(
        json.dumps(data, indent=2) + "\n"
    )

    n = native_two
    c = reference_two
    (
        report_output(
            "devtools.benchmarks.native_power_probe", "NATIVE_POWER_RESULTS.md"
        )
    ).write_text(f"""# Native temporal formula power results

The canonical tree now has a genuinely root-native two-step primitive.  It builds

```text
S -> L/R -> tau(S,L,R) -> K(tau) -> S^(2)(S,L,R,K)
```

inside one hash-consed formula construction.  `tau` is an internal tuple of `Expr` planes:
it is never a `FormulaRoot`, never registered with `BlockSummary`, never assigned first-step
value sets, and never passed through `successor()`.

## Exactness

- randomized arbitrary-radix cases: **{randomized}** exact T² comparisons, bases 2..17;
- repeated seed-196 run: **100 native T² applications = 200 ordinary steps**, exact final
  pair field, width {root.width};
- full pytest regression suite separately covers the substituted second reset sets, native exact
  two-step digit projector, final `X_v -> Z_w` set map, and direct native T⁴.

## Construction footprint on the seed-196 source pair `(7,18,7)`

| metric | native T² | `successor(successor(S))` reference |
|---|---:|---:|
| final reachable formula nodes | {n["formula"]["nodes"]} | {c["formula"]["nodes"]} |
| final formula depth | {n["formula"]["depth"]} | {c["formula"]["depth"]} |
| arena nodes added | {n["arena_nodes_added"]} | {c["arena_nodes_added"]} |
| metadata entries added | {n["metadata_entries_added"]} | {c["metadata_entries_added"]} |
| derived-cache entries | {n["derived_cache_entries"]} | {c["derived_cache_entries"]} |
| closed bits evaluated | {n["closed_bits_total"]} | {c["closed_bits_total"]} |

The final reachable DAG is deliberately the same canonical algebra: native T² changes the
**construction boundary**, not the extensional recurrence.  Its immediate win is that the
first successor is not a semantic/compiler state and its summary/carry cache identity never
exists.

## Native T⁴ formula experiment

Native T⁴ is also built directly from four carry/branch equation layers.  It does **not** call
`native_two_step()` and retains no S² intermediate root.  On the same seed-196 source:

| metric | native T⁴ | native `T²(T²(S))` reference |
|---|---:|---:|
| final reachable formula nodes | {native_four["formula"]["nodes"]} | {reference_four["formula"]["nodes"]} |
| final formula depth | {native_four["formula"]["depth"]} | {reference_four["formula"]["depth"]} |
| arena nodes added | {native_four["arena_nodes_added"]} | {reference_four["arena_nodes_added"]} |
| metadata entries added | {native_four["metadata_entries_added"]} | {reference_four["metadata_entries_added"]} |
| closed bits evaluated | {native_four["closed_bits_total"]} | {reference_four["closed_bits_total"]} |

Again, the final canonical formula DAG is expected to match because both denote the same fully
substituted equations.  The distinction is that native T⁴ never assigns semantic identity to
the two-step midpoint.

## What this does *not* claim yet

The existing powered bimachine T² remains the older composed construction at
**{previous["left"]} left / {previous["right"]} right states**.  This patch does not pretend
those numbers are native-T² state counts.  The next research step is to lower the fully
substituted native T² predicates directly into the canonical residual compiler so quotienting
happens while source predicates are constructed.  Only then is a native-machine state-count
comparison meaningful.  The direct native T⁴ formula now exists, so that lowering can compare
it against the existing composed `T² o T²` machine construction without conflating the two.
""")


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
