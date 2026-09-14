"""Shared immutable result types for binary block-action compilation."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudget,
    BlockEffect,
)


@dataclass(frozen=True, slots=True)
class BlockPower:
    """One canonical binary-powered operator and its construction accounting."""

    base: int
    exponent: int
    root: BlockEffect | None
    operator_nodes: int
    compose_operations: int
    syntax_depth: int
    budget: BlockContextBudget


@dataclass(frozen=True, slots=True)
class BlockApplication:
    """Explicit projection of one powered block effect on one finite pair word."""

    values: tuple[int, ...]
    represented_positions: int
    intermediate_pair_words: int
    elementary_generations: int
    runtime_stats: dict[str, int]


__all__ = ["BlockApplication", "BlockPower"]
