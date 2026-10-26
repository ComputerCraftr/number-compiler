"""Embedded CLI benchmarks disable actual process reuse, not just priming."""

import json

import pytest

from devtools.benchmarks.public_query_comparison import cli_invocation
from number_compiler.api.number_api import NumberCompiler
from number_compiler.sequences.collatz import source_cylinder_cache


def test_embedded_cli_bypass_never_acquires_collatz_process_cache(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arguments = ["collatz", "--seed", "27", "--nth", "32", "--format", "json"]
    NumberCompiler.clear_shared_cache()
    _, code, expected, error = cli_invocation(arguments, fresh=False)
    assert code == 0, error

    def forbidden() -> None:
        raise AssertionError("bypassed CLI acquired the process cache")

    monkeypatch.setattr(source_cylinder_cache, "get_process_cache", forbidden)
    _, code, actual, error = cli_invocation(arguments, fresh=False, shared_cache=False)
    assert code == 0, error
    assert json.loads(actual) == json.loads(expected)


def test_fresh_cli_cannot_silently_ignore_bypass_policy() -> None:
    with pytest.raises(ValueError, match="embedded execution"):
        cli_invocation(["collatz", "--nth", "1"], fresh=True, shared_cache=False)
