"""Public powered block-effect algebra.

Implementation is split into focused modules so the exact finite kernels, semantic
composition machinery, and projection/exponentiation driver can evolve independently.
This file intentionally remains the stable import facade.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudget,
    BlockContextBudgetExceeded,
    BlockEffect,
    BlockEffectAdmissionAdapter,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
)
from number_compiler.arithmetic.contracts.block_power_types import (
    BlockApplication,
    BlockPower,
)
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from devtools.verification.block_composed import ComposedBlockEffect


def compose_block_effects(
    first: BlockEffect,
    second: BlockEffect,
    *,
    budget: BlockContextBudget,
    family_hooks: BlockEffectAdmissionAdapter | None = None,
) -> BlockEffect:
    from number_compiler.arithmetic.automata.guard import record_symbolic_op

    record_symbolic_op("BLOCK_COMPOSE")
    if first.base != second.base:
        raise ValueError((first.base, second.base))
    from devtools.verification.block_composed import ComposedBlockEffect

    return ComposedBlockEffect(first, second, budget=budget, family_hooks=family_hooks)


def _operator_depth(root: BlockEffect | None) -> int:
    from devtools.verification.block_composed import ComposedBlockEffect

    if root is None:
        return 0
    cache: dict[object, int] = {}
    stack: list[tuple[object, bool]] = [(root, False)]
    while stack:
        node, ready = stack.pop()
        if node in cache:
            continue
        if not isinstance(node, ComposedBlockEffect):
            cache[node] = 1
            continue
        if not ready:
            stack.append((node, True))
            if node.second not in cache:
                stack.append((node.second, False))
            if node.first not in cache:
                stack.append((node.first, False))
            continue
        cache[node] = 1 + max(cache[node.first], cache[node.second])
    return cache[root]


def power_block_effect(
    *,
    base: int,
    exponent: int,
    max_context_nodes: int | None = None,
    max_cache_entries: int | None = None,
) -> BlockPower:
    """Build the explicit compatibility/proof operator ``T**exponent``.

    The public lazy family runtime does not call this function. Decimal proof
    and differential callers build from the same primitive one-step law as
    production; no separate finite reverse machine is admitted.
    Construction performs no pair-generation replay and no source-word scan.
    Its immutable operator DAG has logarithmic depth/size in ``exponent``.
    Applying the resulting full nonlinear transduction is a separate operation;
    this module does not mislabel output/context work as logarithmic merely
    because the operator syntax is compact.
    """
    if type(base) is not int or type(exponent) is not int:
        raise TypeError("block power base and exponent must be exact integers")
    for name, limit in (
        ("max_context_nodes", max_context_nodes),
        ("max_cache_entries", max_cache_entries),
    ):
        if limit is not None and type(limit) is not int:
            raise TypeError(f"{name} must be an exact integer or None")
        if limit is not None and limit < 0:
            raise ValueError(f"{name} must be nonnegative")
    if base < 2 or exponent < 0:
        raise ValueError((base, exponent))
    budget = BlockContextBudget(max_context_nodes, max_cache_entries)
    from number_compiler.arithmetic.automata.guard import record_symbolic_op

    record_symbolic_op("BLOCK_POWER")
    if exponent == 0:
        return BlockPower(base, 0, None, 0, 0, 0, budget)

    result: BlockEffect | None = None
    operations = 0
    power: BlockEffect
    n: int
    power = BaseBlockEffect(base)
    n = exponent

    def combine(
        first: BlockEffect | None, second: BlockEffect | None
    ) -> BlockEffect | None:
        nonlocal operations
        if first is None:
            return second
        if second is None:
            return first
        operations += 1
        return compose_block_effects(first, second, budget=budget)

    result = binary_power(
        cast(BlockEffect, power),
        n,
        identity=cast(BlockEffect | None, None),
        compose=combine,
    ).value
    if result is None or result.exponent != exponent:
        raise AssertionError((None if result is None else result.exponent, exponent))
    return BlockPower(
        base=base,
        exponent=exponent,
        root=result,
        operator_nodes=result.operator_nodes(),
        compose_operations=operations,
        syntax_depth=_operator_depth(result),
        budget=budget,
    )


def apply_block_power(
    power: BlockPower, source: tuple[int, ...] | list[int]
) -> BlockApplication:
    """Lower one final endpoint through the index-owned shared runtime.

    Verified reverse programs use the primitive family compiler in every base.
    Other finite-interface programs keep their actual generic semantics. The
    compatibility proof operator owns no projection cache or intermediate word.
    """
    if type(power) is not BlockPower:
        raise TypeError("block projection requires a BlockPower")
    if type(power.base) is not int or type(power.exponent) is not int:
        raise TypeError("block power metadata must contain exact integers")
    if type(source) not in (tuple, list):
        raise TypeError("block source must be a tuple or list of exact integers")
    values = tuple(source)
    if any(type(value) is not int for value in values):
        raise TypeError("block source symbols must be exact integers")
    if not values:
        raise ValueError("empty pair field")
    if power.base < 2 or power.exponent < 0:
        raise ValueError("block power metadata is outside its valid domain")
    max_value = 2 * (power.base - 1)
    if any(v < 0 or v > max_value for v in values):
        raise ValueError((values, power.base))
    from number_compiler.arithmetic.automata.guard import forbid_in_powered_jump

    forbid_in_powered_jump("block_power_projection")
    if power.exponent == 0:
        if power.root is not None:
            raise ValueError("zero block power cannot contain a nonidentity operator")
        return BlockApplication(values, len(values), 0, 0, {})
    effect = power.root
    if effect is None:
        raise ValueError("positive block power requires an operator")
    if not all(
        hasattr(effect, name) for name in ("base", "exponent", "blank")
    ) or not all(
        callable(getattr(effect, name, None))
        for name in ("initial", "advance", "emit", "runtime_stats", "operator_nodes")
    ):
        raise TypeError("block projection requires a complete operator interface")
    if type(effect.base) is not int or type(effect.exponent) is not int:
        raise TypeError("block operator metadata must contain exact integers")
    if effect.base != power.base or effect.exponent != power.exponent:
        raise ValueError("block power metadata disagrees with its operator")
    represented_positions = len(values) + power.exponent
    if _is_reverse_pair_program(effect):
        return _apply_recursive_pair_power(power, values, represented_positions)

    # Uncertified programs preserve their actual operator semantics through
    # the generic lazy executor. Metadata alone never selects reverse/add.
    from number_compiler.hashlife.observation.hashlife_projection import (
        HashLifeBlockIndex,
    )

    ledger = _projection_ledger(power)
    index = HashLifeBlockIndex(
        effect,
        values,
        logical_length=represented_positions,
        ledger=ledger,
    )
    output = tuple(index.iter_direct_active())
    snapshot = ledger.snapshot()
    stats = effect.runtime_stats()
    stats.update(snapshot.counters)
    stats.update(
        retained_cache_entries=snapshot.entries,
        retained_nodes=snapshot.nodes,
        peak_cache_entries=snapshot.peak_entries,
        peak_nodes=snapshot.peak_nodes,
    )
    return BlockApplication(output, represented_positions, 0, 0, stats)


def _is_reverse_pair_program(effect: BlockEffect) -> bool:
    """Recognize primitive reverse operators and their immutable compositions."""
    from devtools.verification.block_composed import ComposedBlockEffect
    from number_compiler.hashlife.actions.lazy_compiler import ProgramComposition

    counts: dict[int, int] = {}
    active: set[int] = set()
    pending: list[tuple[BlockEffect, bool]] = [(effect, False)]
    while pending:
        current, ready = pending.pop()
        key = id(current)
        if key in counts:
            continue
        if (
            type(current.base) is not int
            or type(current.exponent) is not int
            or current.base != effect.base
            or current.blank != 2 * effect.base - 1
        ):
            return False
        if type(current) in (ComposedBlockEffect, ProgramComposition):
            composed = cast("ComposedBlockEffect | ProgramComposition", current)
            if not ready:
                if key in active:
                    raise ValueError("cyclic block power operator")
                active.add(key)
                pending.extend(
                    (
                        (current, True),
                        (composed.second, False),
                        (composed.first, False),
                    )
                )
                continue
            count = counts[id(composed.first)] + counts[id(composed.second)]
            active.remove(key)
        elif type(current) is BaseBlockEffect:
            count = 1
        else:
            return False
        if count != current.exponent:
            return False
        counts[key] = count
    return counts[id(effect)] == effect.exponent


def _projection_ledger(power: BlockPower) -> ResourceLedger:
    """Carry remaining compatibility limits into preallocation reservations."""
    node_limit = power.budget.max_nodes
    entry_limit = power.budget.max_cache_entries
    remaining_nodes = (
        None if node_limit is None else node_limit - power.budget.created_nodes
    )
    remaining_entries = (
        None if entry_limit is None else entry_limit - power.budget.cache_entries
    )
    if remaining_nodes is not None and remaining_nodes < 0:
        raise BlockContextBudgetExceeded(
            "block-effect node budget is already exhausted"
        )
    if remaining_entries is not None and remaining_entries < 0:
        raise BlockContextBudgetExceeded(
            "block-effect cache budget is already exhausted"
        )
    return ResourceLedger(remaining_nodes, remaining_entries)


def _apply_recursive_pair_power(
    power: BlockPower,
    values: tuple[int, ...],
    represented_positions: int,
) -> BlockApplication:
    """Lower one exact final pair field from the shared recursive executor."""
    from number_compiler.arithmetic.contracts.temporal_family import issue_certificate
    from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
    from number_compiler.hashlife.observation.hashlife_projection import (
        HashLifeBlockIndex,
    )
    from number_compiler.sequences.reverse_add.compilation import (
        compile_reverse_pair_power,
    )

    ledger = _projection_ledger(power)
    compiler = LazyCompiler(ledger)
    compiled = compile_reverse_pair_power(
        compiler,
        power.base,
        power.exponent,
    ).root
    if compiled is None:
        raise AssertionError("positive pair exponent has no executable action")
    certificate = issue_certificate(
        compiled,
        "reverse-add",
        power.exponent,
        ledger=ledger,
        output_encoding="pair",
    )
    index = HashLifeBlockIndex(
        compiled,
        values,
        logical_length=represented_positions,
        certificate=certificate,
        ledger=ledger,
        compiler=compiler,
    )

    # T commutes with reflection of the complete pair field. Original
    # palindromic pair sources therefore need only one half of the final
    # scalar observations; the other half is emitted from the requested
    # endpoint buffer, never from an intermediate generation.
    output = tuple(index.iter_direct_points(reflect_output=values == values[::-1]))
    snapshot = ledger.snapshot()
    stats = {} if power.root is None else power.root.runtime_stats()
    stats.update(snapshot.counters)
    query_entries = sum(
        item.entries for item in snapshot.inventory if item.role == "query_memo"
    )
    recursive_nodes = sum(
        item.nodes
        for item in snapshot.inventory
        if item.role
        in ("higher_semantic_expression", "field_cell_action", "field_action")
    )
    output_entries = sum(
        item.entries
        for item in snapshot.inventory
        if item.role == "completed_result_memo"
    )
    stats.update(
        {
            "projection_positions_visited": len(output),
            "source_run_count": sum(
                index == 0 or value != values[index - 1]
                for index, value in enumerate(values)
            ),
            "right_context_slots": 0,
            "run_action_cache_entries": 0,
            "positional_context_vectors": 0,
            "retained_cache_entries": snapshot.entries,
            "peak_cache_entries": snapshot.peak_entries,
            "peak_nodes": snapshot.peak_nodes,
            "residual_cache_dropped_entries": 0,
            "output_cache_slots": query_entries,
            "output_cache_occupied": query_entries,
            "canonical_recursive_left_states": recursive_nodes,
            "canonical_recursive_right_states": recursive_nodes,
            "recursive_action_left_nodes": recursive_nodes,
            "recursive_action_right_nodes": recursive_nodes,
            "spacetime_tile_output_entries": output_entries,
        }
    )
    return BlockApplication(output, represented_positions, 0, 0, stats)


def __getattr__(name: str) -> object:
    """Load the compatibility composed runtime only when explicitly requested."""
    if name == "ComposedBlockEffect":
        from devtools.verification.block_composed import ComposedBlockEffect

        return ComposedBlockEffect
    raise AttributeError(name)


__all__ = [
    "BaseBlockEffect",
    "BlockApplication",
    "BlockContextBudget",
    "BlockContextBudgetExceeded",
    "BlockEffect",
    "BlockPower",
    "BoundarySide",
    "ComposedBlockEffect",
    "FiniteBlockEffect",
    "apply_block_power",
    "compose_block_effects",
    "power_block_effect",
]
