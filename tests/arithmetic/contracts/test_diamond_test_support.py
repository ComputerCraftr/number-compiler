"""Shared test code must not share warmed execution state or import test cases."""

import ast
from pathlib import Path

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from tests.support.diamond_query import build as build_application
from tests.support.diamond_runtime import build as build_runtime


def test_diamond_test_helpers_do_not_depend_on_collected_test_modules() -> None:
    tests = Path(__file__).resolve().parent
    for path in (
        *tests.glob("test_diamond*.py"),
        *tests.joinpath("support").glob("*.py"),
    ):
        tree = ast.parse(path.read_text())
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom):
                assert not (node.module or "").startswith("tests.test_"), (
                    path,
                    node.lineno,
                )
            elif isinstance(node, ast.Import):
                assert all(
                    not alias.name.startswith("tests.test_") for alias in node.names
                ), (path, node.lineno)


def test_shared_runtime_factory_always_creates_a_fresh_execution_scope() -> None:
    effect = BaseBlockEffect(2)
    first, first_root = build_runtime(effect, (1, 2, 1), 4, 1)
    second, second_root = build_runtime(effect, (1, 2, 1), 4, 1)
    assert first.ledger is not second.ledger
    assert first_root.owner is not second_root.owner
    before = second.ledger.snapshot()
    first.point(first_root, 0)
    assert second.ledger.snapshot() == before


def test_shared_application_factory_always_creates_a_fresh_execution_scope() -> None:
    effect = BaseBlockEffect(2)
    first = build_application(effect, (1, 2, 1), 4, 1)
    second = build_application(effect, (1, 2, 1), 4, 1)
    assert first.ledger is not second.ledger
    assert first.root.owner is not second.root.owner
    before = second.ledger.snapshot()
    first.point(0)
    assert second.ledger.snapshot() == before
