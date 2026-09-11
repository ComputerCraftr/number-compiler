"""Removed reverse executors cannot return as implicit production fallbacks."""

from __future__ import annotations

from importlib.util import find_spec


def test_retired_reverse_executors_are_absent() -> None:
    assert find_spec("number_compiler.sequences.reverse_add.runtime") is None
    assert find_spec("number_compiler.sequences.reverse_add.field_observer") is None
    assert (
        find_spec("number_compiler.sequences.reverse_add.recursive_image_runtime")
        is None
    )


def test_retired_collatz_image_executors_are_absent() -> None:
    assert find_spec("number_compiler.hashlife.execution.radix_image_input") is None
    assert find_spec("number_compiler.sequences.collatz.field_observer") is None
    assert (
        find_spec("number_compiler.sequences.collatz.recursive_image_runtime") is None
    )
    assert find_spec("number_compiler.sequences.collatz.temporal_emission") is None
