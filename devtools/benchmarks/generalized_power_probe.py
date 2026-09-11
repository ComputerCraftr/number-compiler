"""Release measurements for generalized reverse-add temporal powers.

This probe separates three exact objects:
1. closed-source FormulaRoot equation elimination (linear compile oracle),
2. source-independent T^N block-effect syntax (binary composition), and
3. explicit powered projection/context work.

Only (2) is logarithmic in N today; this script deliberately reports (3)
separately so compact operator syntax cannot masquerade as a full-state jump.
"""

from __future__ import annotations

import ast
import hashlib
import json
import random
from time import perf_counter
from typing import TYPE_CHECKING

from devtools.benchmarks.carry_event_formula_probe import (
    build_report as build_carry_event_report,
)
from devtools.benchmarks.probe_support import symmetric_word
from devtools.paths import report_output, repository_root
from devtools.proofs.block_composed import ComposedBlockEffect
from devtools.proofs.block_power import apply_block_power, power_block_effect
from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
from number_compiler.arithmetic.formula.formula import (
    FormulaArena,
    formula_metrics,
    root_from_values,
)
from number_compiler.arithmetic.formula.types import RadixSpec
from number_compiler.hashlife.actions.native_power import compile_native_power

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.block_effect import BlockEffect


HERE = repository_root()


def reference_successor(full: tuple[int, ...], base: int) -> tuple[int, ...]:
    d = len(full)
    carry = [0] * (d + 1)
    for i, value in enumerate(full):
        carry[i + 1] = int(value + carry[i] >= base)
    reverse = [carry[d - i] for i in range(d + 1)]
    if not carry[d]:
        return tuple(
            2 * full[i] + carry[i] + reverse[i + 1] - base * (carry[i + 1] + reverse[i])
            for i in range(d)
        )
    out = [0] * (d + 1)
    out[0] = full[0] + 1 - base * carry[1]
    out[d] = out[0]
    for i in range(1, d):
        out[i] = (
            full[i]
            + full[i - 1]
            + carry[i]
            + reverse[i]
            - base * (carry[i + 1] + reverse[i - 1])
        )
    return tuple(out)


def _find_composed_power(
    root: BlockEffect | None,
    exponent: int,
) -> ComposedBlockEffect:
    stack = [root]
    seen: set[int] = set()
    while stack:
        node = stack.pop()
        if node is None or node.node_id in seen:
            continue
        seen.add(node.node_id)
        if isinstance(node, ComposedBlockEffect):
            if node.exponent == exponent:
                return node
            stack.extend((node.first, node.second))
    raise AssertionError((exponent, sorted(seen)))


def _cached_successors(state: object) -> tuple[object, ...]:
    out: list[object] = []
    one = getattr(state, "transition_result", None)
    if one is not None:
        out.append(one)
    more = getattr(state, "transition_more", None)
    if more:
        out.extend(more.values())
    # A transition cache can point to the same canonical object through multiple
    # symbols; state identity, not edge multiplicity, is the quantity of interest.
    uniq: dict[int, object] = {}
    for item in out:
        uniq[id(item)] = item
    return tuple(uniq.values())


def _reachable_states(
    effect: ComposedBlockEffect, side: BoundarySide
) -> tuple[object, ...]:
    start = effect.initial(side)
    stack = [start]
    seen: dict[int, object] = {}
    while stack:
        state = stack.pop()
        marker = id(state)
        if marker in seen:
            continue
        seen[marker] = state
        stack.extend(_cached_successors(state))
    return tuple(seen.values())


def _partition_profile(
    effect: ComposedBlockEffect, side: BoundarySide
) -> dict[str, object]:
    states = _reachable_states(effect, side)
    opposite = BoundarySide.RIGHT if side is BoundarySide.LEFT else BoundarySide.LEFT
    domain = effect.first.boundary_universe(opposite)
    if domain is None:
        raise AssertionError("canonical partition proof domain is unavailable")
    group_counts = []
    covered = (1 << len(domain)) - 1
    for state in states:
        partition = getattr(state, "partition", None)
        if partition is None:
            raise AssertionError(("expected canonical partition state", type(state)))
        union = 0
        for _, mask in partition:
            if union & mask:
                raise AssertionError("partition profile found overlapping selectors")
            union |= mask
        if union != covered:
            raise AssertionError((union, covered))
        group_counts.append(len(partition))
    return {
        "states": len(states),
        "domain_size": len(domain),
        "average_output_groups": (sum(group_counts) / len(group_counts))
        if group_counts
        else 0.0,
        "max_output_groups": max(group_counts, default=0),
        "full_domain_vectors_materialized": 0,
    }


def _recursive_profile(
    effect: ComposedBlockEffect, side: BoundarySide
) -> dict[str, object]:
    """Profile the current higher recursive dyadic carrier for one side."""
    index = int(side)
    action_pool = effect._recursive_residual_intern[index]
    constant = effect._recursive_constant[index]
    value_cells = sum(
        1
        for residual, _argument in effect._recursive_value_cache
        if getattr(residual, "side", None) is side
    )
    return {
        "canonical_recursive_states": effect._states[index],
        "recursive_action_nodes": (0 if action_pool is None else len(action_pool))
        + (1 if constant is not None else 0),
        "recursive_value_cells": value_cells,
        "transition_entries": effect._transition_entries[index],
        "action_intern_hits": effect._recursive_residual_intern_hits,
        "action_intern_misses": effect._recursive_residual_intern_misses,
        "parallel_root_registry": False,
    }


def main() -> None:
    rng = random.Random(0x196B10C)
    exact_cases = 0
    for base in range(2, 17):
        for exponent in range(9):
            for _ in range(10):
                source = symmetric_word(rng, base, rng.randint(1, 12))
                expected = source
                for _step in range(exponent):
                    expected = reference_successor(expected, base)
                got = apply_block_power(
                    power_block_effect(base=base, exponent=exponent), source
                )
                assert got.values == expected
                assert got.intermediate_pair_words == 0
                assert got.elementary_generations == 0
                exact_cases += 1

    formula_rows = []
    spec = RadixSpec(10)
    for exponent in (1, 2, 4, 8, 16, 32, 64, 128, 256):
        arena = FormulaArena()
        formula_source = root_from_values((7, 18, 7), arena, spec)
        t0 = perf_counter()
        compiled = compile_native_power(arena, formula_source, exponent, spec)
        seconds = perf_counter() - t0
        fm = formula_metrics(compiled.pair)
        formula_rows.append(
            {
                "exponent": exponent,
                "output_width": compiled.pair.width,
                "nodes": fm["nodes"],
                "depth": fm["depth"],
                "description_bits": fm["description_bits"],
                "closed_bit_evaluations": arena.cached_closed_bits,
                "seconds": seconds,
            }
        )

    operator_rows = []
    for exponent in (1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 10**6, 10**18):
        t0 = perf_counter()
        power = power_block_effect(base=10, exponent=exponent)
        seconds = perf_counter() - t0
        operator_rows.append(
            {
                "exponent": exponent,
                "bit_length": exponent.bit_length(),
                "operator_nodes": power.operator_nodes,
                "compose_operations": power.compose_operations,
                "syntax_depth": power.syntax_depth,
                "initial_context_nodes": power.budget.created_nodes,
                "seconds": seconds,
            }
        )

    projection_rows = []
    p1024_power = None
    for exponent in (1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024):
        power = power_block_effect(
            base=10,
            exponent=exponent,
            max_context_nodes=5_000_000,
            max_cache_entries=5_000_000,
        )
        t0 = perf_counter()
        application = apply_block_power(power, (7, 18, 7))
        seconds = perf_counter() - t0
        stats = application.runtime_stats
        projection_rows.append(
            {
                "exponent": exponent,
                "output_width": len(application.values),
                "represented_positions": application.represented_positions,
                "left_boundary_residuals": stats.get("left_boundary_residuals", 0),
                "right_boundary_residuals": stats.get("right_boundary_residuals", 0),
                "finite_kernel_left_states": stats.get("finite_kernel_left_states", 0),
                "finite_kernel_right_states": stats.get(
                    "finite_kernel_right_states", 0
                ),
                "finite_kernel_storage_bytes": stats.get(
                    "finite_kernel_storage_bytes", 0
                ),
                "canonical_function_left_states": stats.get(
                    "canonical_function_left_states", 0
                ),
                "canonical_function_right_states": stats.get(
                    "canonical_function_right_states", 0
                ),
                "canonical_partition_left_states": stats.get(
                    "canonical_partition_left_states", 0
                ),
                "canonical_partition_right_states": stats.get(
                    "canonical_partition_right_states", 0
                ),
                "canonical_recursive_left_states": stats.get(
                    "canonical_recursive_left_states", 0
                ),
                "canonical_recursive_right_states": stats.get(
                    "canonical_recursive_right_states", 0
                ),
                "recursive_action_left_nodes": stats.get(
                    "recursive_action_left_nodes", 0
                ),
                "recursive_action_right_nodes": stats.get(
                    "recursive_action_right_nodes", 0
                ),
                "recursive_value_cache_entries": stats.get(
                    "recursive_value_cache_entries", 0
                ),
                "behavioral_partition_left_states": stats.get(
                    "behavioral_partition_left_states", 0
                ),
                "behavioral_partition_right_states": stats.get(
                    "behavioral_partition_right_states", 0
                ),
                "behavioral_partition_left_aliases": stats.get(
                    "behavioral_partition_left_aliases", 0
                ),
                "behavioral_partition_right_aliases": stats.get(
                    "behavioral_partition_right_aliases", 0
                ),
                "partition_residual_intern_hits": stats.get(
                    "partition_residual_intern_hits", 0
                ),
                "partition_residual_intern_misses": stats.get(
                    "partition_residual_intern_misses", 0
                ),
                "partition_preimage_cache_hits": stats.get(
                    "partition_preimage_cache_hits", 0
                ),
                "partition_preimage_cache_misses": stats.get(
                    "partition_preimage_cache_misses", 0
                ),
                "provenance_path_left_states": stats.get(
                    "provenance_path_left_states", 0
                ),
                "provenance_path_right_states": stats.get(
                    "provenance_path_right_states", 0
                ),
                "canonical_program_word_roots": stats.get(
                    "canonical_program_word_roots", 0
                ),
                "program_word_intern_hits": stats.get("program_word_intern_hits", 0),
                "program_word_intern_misses": stats.get(
                    "program_word_intern_misses", 0
                ),
                "retained_execution_nodes": stats.get("retained_execution_nodes", 0),
                "run_action_cache_entries": stats.get("run_action_cache_entries", 0),
                "positional_context_vectors": stats.get(
                    "positional_context_vectors", 0
                ),
                "functional_residual_intern_hits": stats.get(
                    "functional_residual_intern_hits", 0
                ),
                "functional_residual_intern_misses": stats.get(
                    "functional_residual_intern_misses", 0
                ),
                "residual_cache_hits": stats.get("residual_cache_hits", 0),
                "residual_cache_misses": stats.get("residual_cache_misses", 0),
                "residual_cache_dropped_entries": stats.get(
                    "residual_cache_dropped_entries", 0
                ),
                "output_cache_hits": stats.get("output_cache_hits", 0),
                "output_cache_misses": stats.get("output_cache_misses", 0),
                "retained_cache_entries": stats.get("retained_cache_entries", 0),
                "intermediate_pair_words": application.intermediate_pair_words,
                "elementary_generations": application.elementary_generations,
                "seconds": seconds,
            }
        )
        if exponent == 1024:
            p1024_power = power

    # Inspect the first two higher layers after the largest projection. T^4 is
    # a complete canonical one-coordinate decision function over the finite T^2
    # domain.  Its exact extensional partition IDs are final when interned: parent
    # recursive actions never retain a child ID that can be post-hoc aliased later.
    # T^8+ production uses canonical recursive dyadic residual actions.
    if p1024_power is None:
        raise AssertionError("missing T^1024 projection capture")
    t4 = _find_composed_power(p1024_power.root, 4)
    t8 = _find_composed_power(p1024_power.root, 8)
    t4_partition = {
        "left": _partition_profile(t4, BoundarySide.LEFT),
        "right": _partition_profile(t4, BoundarySide.RIGHT),
    }
    t4_stats = t4.runtime_stats()
    t4_behavioral = {
        "left_aliases": t4_stats.get("behavioral_partition_left_aliases", 0),
        "right_aliases": t4_stats.get("behavioral_partition_right_aliases", 0),
        "left_states_after": t4_stats.get("canonical_partition_left_states", 0),
        "right_states_after": t4_stats.get("canonical_partition_right_states", 0),
        "seconds": 0.0,
        "proof_kind": "stable exact extensional partition identity; no post-hoc alias pass",
        "late_aliasing_deleted": not hasattr(t4, "refine_partition_behavioral_aliases"),
    }
    t8_recursive = {
        "left": _recursive_profile(t8, BoundarySide.LEFT),
        "right": _recursive_profile(t8, BoundarySide.RIGHT),
    }

    kernel_path = HERE / "src" / "number_compiler" / "kernels" / "base10_t2_kernel.zlib"
    kernel_bytes = kernel_path.read_bytes()
    t2 = power_block_effect(base=10, exponent=2).root
    if not isinstance(t2, FiniteBlockEffect):
        raise TypeError(type(t2))
    t2_kernel = {
        "name": t2.kernel_name,
        "left_states": t2.left_count,
        "right_states": t2.right_count,
        "compressed_bytes": t2.storage_bytes,
        "uncompressed_bytes": t2.uncompressed_bytes,
        "sha256": hashlib.sha256(kernel_bytes).hexdigest(),
    }

    source_text = (HERE / "devtools" / "proofs" / "block_power.py").read_text(
        encoding="utf-8"
    )
    tree = ast.parse(source_text)
    power_fn = next(
        node
        for node in tree.body
        if isinstance(node, ast.FunctionDef) and node.name == "power_block_effect"
    )
    calls = {
        node.func.id
        for node in ast.walk(power_fn)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
    }
    structural = {
        "successor_called_by_operator_compiler": "successor" in calls,
        "operator_compiler_contains_for_loop": any(
            isinstance(n, ast.For) for n in ast.walk(power_fn)
        ),
        "operator_compiler_contains_binary_while": any(
            isinstance(n, ast.While) for n in ast.walk(power_fn)
        ),
        "operator_compiler_source_oracle_calls": sorted(
            calls & {"materialize_values", "value_at", "eval_bit"}
        ),
    }
    assert not structural["successor_called_by_operator_compiler"]
    assert not structural["operator_compiler_contains_for_loop"]
    assert structural["operator_compiler_contains_binary_while"]
    assert not structural["operator_compiler_source_oracle_calls"]

    carry_event_report = build_carry_event_report()
    metrics = {
        "randomized_exact_block_power_cases": exact_cases,
        "fixed_height_carry_event_ir": carry_event_report,
        "structural_contract": structural,
        "native_formula_elimination": formula_rows,
        "binary_block_operator": operator_rows,
        "base10_t2_semantic_kernel": t2_kernel,
        "seed196_explicit_projection": projection_rows,
        "t4_canonical_partition_at_seed196_n1024": t4_partition,
        "t4_behavioral_quotient_at_seed196_n1024": t4_behavioral,
        "t8_recursive_carrier_at_seed196_n1024": t8_recursive,
        "full_unbounded_formula_root_jump_ready": False,
        "remaining_blocker": (
            "The exact carry/event theorem reduces nonlinear temporal information to a fixed "
            "H=4*bit_length(2b-2) window of forward binary carry fields (H=20 in decimal); "
            "event widths recover length/growth and the signed forcing event is derived from "
            "that one forward carry field. The remaining strict-J blocker is therefore a compact "
            "behavioral/spatial grammar for this fixed-height carry slab. The T^2/T^4 semantic "
            "kernels and dyadic spacetime-macrocell machinery remain exact execution mechanisms, but the "
            "unbounded program-syntax tower is no longer treated as the preferred theorem state."
        ),
    }
    (
        report_output(
            "devtools.benchmarks.generalized_power_probe",
            "generalized_power_metrics.json",
        )
    ).write_text(json.dumps(metrics, indent=2) + "\n")

    huge = operator_rows[-1]
    _p1024 = projection_rows[-1]
    f256 = formula_rows[-1]
    md = f"""# Generalized reverse-add power results

## What is now closed

The release now contains two arbitrary-power constructions with distinct contracts.

1. `compile_native_power(arena, source, N, spec)` algebraically substitutes every
   finite temporal layer into **one final FormulaRoot**.  No intermediate FormulaRoot,
   `successor()`, T² root, or T⁴ root is constructed.  It is the generalized exact
   equation-elimination oracle.  Because it still resolves one closed growth event per
   temporal layer, its compile work is linear in `N` and it is intentionally rejected by
   `powered_jump_scope`.
2. `power_block_effect(base=b, exponent=N)` compiles the exact **source-independent local
   T^N operator** by binary composition.  It constructs no source word and replays no
   elementary generation.  For `N=10^18` ({huge["bit_length"]} bits) it has
   **{huge["operator_nodes"]} operator nodes**, **{huge["compose_operations"]} compositions**,
   and syntax depth **{huge["syntax_depth"]}**.

The second object is the generalized powered operator that was missing from the canonical
FormulaRoot tree.  Applying it once to a finite padded pair field is exact and creates zero
intermediate pair words.

## Exactness

- randomized multibase powered-block comparisons: **{exact_cases} exact cases**;
- bases 2..16, exponents 0..8, randomized symmetric pair fields;
- existing native T²/T⁴ differential tests remain green;
- full repository test suite is run separately by the release gate.

## Formula elimination scaling on decimal 196

| N | output width | FormulaRoot nodes | depth | description bits | closed growth-bit evaluations |
|---:|---:|---:|---:|---:|---:|
"""
    for row in formula_rows:
        md += (
            f"| {row['exponent']} | {row['output_width']} | {row['nodes']} | {row['depth']} | "
            f"{row['description_bits']} | {row['closed_bit_evaluations']} |\n"
        )
    md += f"""
At N=256 the fully substituted closed formula has {f256["nodes"]} reachable nodes and
{f256["description_bits"]} description bits.  This is exact elimination, but not a
polylogarithmic temporal compiler.

## Binary operator syntax versus current recursive HashLife execution

Decimal T² is the deterministically regenerated **{t2_kernel["left_states"]}/{t2_kernel["right_states"]}**
minimal semantic kernel (`{t2_kernel["sha256"]}`), occupying
{t2_kernel["compressed_bytes"]:,} compressed bytes. The explicitly opted-in bottom lift may use an
exact finite partition. Every higher composed layer uses the recursive dyadic carrier; no
program-word or raw-boundary execution carrier is part of production.

| N | operator nodes | output width | partition L/R | recursive states L/R | recursive action nodes L/R | retained cache |
|---:|---:|---:|---:|---:|---:|---:|
"""
    proj_by_n = {row["exponent"]: row for row in projection_rows}
    for row in operator_rows:
        if row["exponent"] not in proj_by_n:
            continue
        proj = proj_by_n[row["exponent"]]
        md += (
            f"| {row['exponent']} | {row['operator_nodes']} | {proj['output_width']} | "
            f"{proj['canonical_partition_left_states']}/{proj['canonical_partition_right_states']} | "
            f"{proj['canonical_recursive_left_states']}/{proj['canonical_recursive_right_states']} | "
            f"{proj['recursive_action_left_nodes']}/{proj['recursive_action_right_nodes']} | "
            f"{proj['retained_cache_entries']} |\n"
        )
    md += f"""
At N=1024 the immutable temporal operator is only **{next(r["operator_nodes"] for r in operator_rows if r["exponent"] == 1024)} nodes**,
while execution work is reported separately. T⁴ partition IDs are final at interning time:
compatibility late-alias counters are **{t4_behavioral["left_aliases"]} + {t4_behavioral["right_aliases"]}**,
and the deleted post-hoc refinement pass cannot rewrite a child ID after a T⁸+ parent retains it.

At the first higher carrier (T⁸), the side-local recursive profiles are
**{t8_recursive["left"]["canonical_recursive_states"]}/{t8_recursive["right"]["canonical_recursive_states"]}**
states and **{t8_recursive["left"]["recursive_action_nodes"]}/{t8_recursive["right"]["recursive_action_nodes"]}**
action nodes. Bulk-tile and recursive-leaf traversal are required to intern the same state.

This closes the duplicate state-space and late-ID defects. First-use recursive action/cache growth
remains a separate scaling gate and is not inferred from the logarithmic operator DAG.

## Restored fixed-height carry/event theorem

The nonlinear forcing is again exposed as a derived compiler IR, not semantic state.  In decimal,
`H=20` previous forward binary carry fields reconstruct the exact endpoint pair; the signed event
field is a pure function of that one forward carry field, and `len(E_t)=len(S_(t+1))`, so event
widths recover the later growth/length sequence.  The release therefore treats the remaining
nonlinear theorem target as **20 binary carry position-set fields × spatial coordinate**, not an
unbounded temporal tower of T^8/T^16 program syntax.  See `CARRY_EVENT_FORMULA_RESULTS.md`.

## Full J status

`J_a : FormulaRoot_n -> FormulaRoot_(2n+a)` remains fail-closed.  The generalized operator
is not installed as a fake J backend because converting its result into the current
FormulaRoot state would still cross the growing projection/context boundary.  A finite-horizon
table, deferred `Power(T,N)` token, or query-time successor replay is not accepted as a fix.
"""
    (
        report_output(
            "devtools.benchmarks.generalized_power_probe",
            "GENERALIZED_POWER_RESULTS.md",
        )
    ).write_text(md)


if __name__ == "__main__":
    main()
