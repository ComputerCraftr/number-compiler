"""Shared lazy construction bounds, distinct from endpoint execution evidence."""

from typing import Protocol

from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.query_types import CollatzTermQuery


class PowerComplexity(Protocol):
    @property
    def operator_nodes(self) -> int: ...
    @property
    def compose_operations(self) -> int: ...
    @property
    def syntax_depth_bound(self) -> int: ...


def assert_binary_power_bound(metrics: PowerComplexity, steps: int) -> None:
    assert metrics.operator_nodes <= 2 * steps.bit_length()
    assert metrics.compose_operations <= 2 * steps.bit_length()
    assert metrics.syntax_depth_bound <= steps.bit_length() + 2


def assert_collatz_radices(compiler: NumberCompiler) -> None:
    assert compiler.nth(CollatzTermQuery(10, seed=27, radix=2)) == 214
    assert compiler.nth(CollatzTermQuery(10, seed=27, radix=3)) == 214
    assert compiler.nth(CollatzTermQuery(10, seed=27, radix=6)) == 214
