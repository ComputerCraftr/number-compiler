import inspect

import devtools.verification.collatz_semantic_action as semantic_action
from devtools.verification.block_recursive import (
    _RecursiveBoundaryState,
    _RecursiveResidualAction,
)
from devtools.verification.collatz_forcing_morphism import CollatzForcingOccurrence
from devtools.verification.collatz_spacetime import (
    CollatzPhysicalField,
    CollatzRadixField,
)
from number_compiler.arithmetic.fields import causal_domain


def test_temporal_objects_do_not_retain_raw_scalar_tape_length() -> None:
    assert "length" not in _RecursiveResidualAction.__slots__
    assert "depth" not in _RecursiveResidualAction.__slots__
    assert "tail_span" not in CollatzForcingOccurrence.__slots__
    assert "frame_depth" not in CollatzForcingOccurrence.__slots__
    assert "valuation" not in CollatzForcingOccurrence.__slots__
    assert "active_length" not in CollatzRadixField.__slots__
    assert "active_length" not in CollatzPhysicalField.__slots__
    assert _RecursiveBoundaryState is _RecursiveResidualAction


def test_arithmetic_action_helpers_do_not_use_diagnostic_tile_ids_as_work_keys() -> (
    None
):
    for module in (causal_domain, semantic_action):
        source = inspect.getsource(module)
        assert ".node_id" not in source


def test_recursive_runtime_uses_only_bounded_dyadic_alignment_phase() -> None:
    import devtools.verification.block_spacetime_runtime as runtime

    source = inspect.getsource(runtime)
    assert "_recursive_residual_phase" in source
    assert "_recursive_residual_extent" not in source
    phase_source = inspect.getsource(runtime._recursive_residual_phase)
    assert "% modulus" in phase_source
