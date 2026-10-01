"""Completed spatial streaming, independently of temporal cutover acceptance."""

from __future__ import annotations

from collections.abc import Generator
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.actions.field_actions import CoordinateOutputMorphismID
from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpressionID,
)
from number_compiler.hashlife.execution.recursive_outputs import (
    _STREAM_FRAME_NODES,
    RecursiveCoordinateMorphismArena,
    RecursiveOutputBranch,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.resources.higher_payload_audit import audit_higher_payloads
from tests.support.reverse_higher_interface import _direct_step
from tests.support.reverse_higher_runtime import (
    _fixture,
    _macro_composer,
    _observed_macro,
)


def _spatial(
    word: tuple[int, ...],
) -> tuple[
    RecursiveCoordinateMorphismArena, CoordinateOutputMorphismID, object, object
]:
    _, primitive, semantics, runtime, interfaces, compiler, sources, binding = _fixture(
        word
    )
    outputs, _unused_composer_binding, macro, left, right = _observed_macro(
        semantics, interfaces, sources, primitive, compiler, runtime, binding
    )
    return outputs, macro.output, left, right


@pytest.mark.parametrize(
    "word", [(7, 18, 7, 19), (9, 9, 9, 9), (18, 0, 18, 0, 19, 19, 19, 19)]
)
def test_stream_crops_match_independent_primitive_fold(word: tuple[int, ...]) -> None:
    outputs, root, left, right = _spatial(word)
    expected = _direct_step(word, 10)
    for lo in range(len(word) + 1):
        for hi in range(lo, len(word) + 1):
            assert (
                tuple(outputs.iter_observe_range(root, lo, hi, left, right))
                == expected[lo:hi]
            )
    assert not outputs._stream_frames
    assert all(item.accounting_delta == 0 for item in outputs.ledger.inventory())


def test_stream_visits_each_spatial_occurrence_once() -> None:
    word = (7, 18, 7, 19) * 8
    outputs, root, left, right = _spatial(word)
    assert tuple(
        outputs.iter_observe_range(root, 0, len(word), left, right)
    ) == _direct_step(word, 10)
    counters = outputs.ledger.counters
    assert counters["recursive_output_stream_node_visits"] == 2 * len(word) - 1
    assert counters["recursive_output_stream_boundary_evaluations"] == 2 * (
        len(word) - 1
    )
    assert counters["recursive_output_stream_emitted_digits"] == len(word)
    assert counters.get("spatial_observation_descents", 0) == 0
    assert counters["recursive_output_stream_frame_peak"] <= 3 * len(word).bit_length()


def test_retained_branch_completion_is_independently_audited() -> None:
    outputs, root, _left, _right = _spatial((7, 18))
    branch = outputs.resolve(root)
    assert type(branch) is RecursiveOutputBranch
    assert branch.spatial_complete
    assert id(branch) in audit_higher_payloads(outputs.ledger).approved
    object.__setattr__(branch, "spatial_complete", False)
    try:
        assert (outputs._node_owner, id(branch)) in audit_higher_payloads(
            outputs.ledger
        ).invalid
    finally:
        object.__setattr__(branch, "spatial_complete", True)


def test_partial_interleaved_streams_release_only_their_frames() -> None:
    word = (7, 18, 7, 19) * 2
    outputs, root, left, right = _spatial(word)
    first = outputs.iter_observe_range(root, 0, 8, left, right)
    second = outputs.iter_observe_range(root, 1, 7, left, right)
    assert next(first) == _direct_step(word, 10)[0]
    assert next(second) == _direct_step(word, 10)[1]
    first.close()
    assert outputs._stream_frames
    assert tuple(second) == _direct_step(word, 10)[2:7]
    assert not outputs._stream_frames
    assert all(item.accounting_delta == 0 for item in outputs.ledger.inventory())


def test_stream_failed_allocation_releases_pending_frames() -> None:
    outputs, root, left, right = _spatial((7, 18, 7, 19))
    owner = outputs.ledger.inventory()[outputs._stream_owner]
    assert owner.entries == owner.nodes == 0
    outputs.ledger.max_nodes = outputs.ledger.nodes + _STREAM_FRAME_NODES
    with pytest.raises(BlockContextBudgetExceeded):
        tuple(outputs.iter_observe_range(root, 0, 4, left, right))
    assert not outputs._stream_frames
    assert all(item.accounting_delta == 0 for item in outputs.ledger.inventory())


def _started_stream() -> tuple[
    tuple[int, ...],
    RecursiveCoordinateMorphismArena,
    CoordinateOutputMorphismID,
    object,
    object,
    Generator[int, None, None],
]:
    word = (7, 18, 7, 19)
    outputs, root, left, right = _spatial(word)
    first = outputs.iter_observe_range(root, 0, len(word), left, right)
    assert next(first) == _direct_step(word, 10)[0]
    return word, outputs, root, left, right, first


def test_failed_second_stream_preserves_live_first_stream() -> None:
    word, outputs, root, left, right, first = _started_stream()
    live_keys = set(outputs._stream_frames)
    assert live_keys
    outputs.ledger.max_nodes = outputs.ledger.nodes
    with pytest.raises(BlockContextBudgetExceeded):
        next(outputs.iter_observe_range(root, 0, len(word), left, right))
    assert set(outputs._stream_frames) == live_keys
    first.close()
    assert not outputs._stream_frames
    assert all(item.accounting_delta == 0 for item in outputs.ledger.inventory())


def test_stream_callback_failure_after_yield_releases_frames() -> None:
    (
        _unused_word_binding,
        outputs,
        _unused_root_binding,
        _unused_left_binding,
        _unused_right_binding,
        stream,
    ) = _started_stream()

    def failed_boundary(*_args: object) -> Never:
        raise LookupError("boundary evaluation failed")

    outputs._evaluate = failed_boundary
    with pytest.raises(LookupError, match="boundary evaluation failed"):
        tuple(stream)
    assert not outputs._stream_frames
    assert all(item.accounting_delta == 0 for item in outputs.ledger.inventory())


@pytest.mark.parametrize("cancel", (False, True))
def test_first_emission_does_not_evaluate_pending_right_branches(
    monkeypatch: pytest.MonkeyPatch, cancel: bool
) -> None:
    word = (7, 18, 7, 19) * 4
    outputs, root, left, right = _spatial(word)
    component = outputs._component

    def demanded_component(
        interface: LocalInterfaceID, role: str
    ) -> HigherExpressionID:
        if role == "boundary_left":
            raise AssertionError("undemanded right branch evaluated eagerly")
        return component(interface, role)

    stream = outputs.iter_observe_range(root, 0, len(word), left, right)
    try:
        with monkeypatch.context() as patch:
            patch.setattr(outputs, "_component", demanded_component)
            assert next(stream) == _direct_step(word, 10)[0]
            assert (
                outputs.ledger.counters["recursive_output_stream_boundary_evaluations"]
                == len(word).bit_length() - 1
            )
        if not cancel:
            assert tuple(stream) == _direct_step(word, 10)[1:]
            assert outputs.ledger.counters[
                "recursive_output_stream_boundary_evaluations"
            ] == 2 * (len(word) - 1)
    finally:
        stream.close()
    assert not outputs._stream_frames
    assert all(item.accounting_delta == 0 for item in outputs.ledger.inventory())


def test_stream_out_of_range_releases_frames() -> None:
    outputs, root, left, right = _spatial((7, 18, 7, 19))
    with pytest.raises(IndexError):
        tuple(outputs.iter_observe_range(root, 0, 5, left, right))
    assert not outputs._stream_frames
    assert all(item.accounting_delta == 0 for item in outputs.ledger.inventory())


def test_stream_temporal_witness_is_never_observed() -> None:
    actions, primitive, semantics, _, interfaces, compiler, *_ = _fixture((7,))

    def forbidden(*_args: object) -> Never:
        pytest.fail("stream reopened a temporal witness")

    outputs = RecursiveCoordinateMorphismArena(
        interfaces,
        evaluate=semantics.evaluate,
        validate_action=actions.resolve,
        compose_actions=actions.compose,
        complete_temporal_action=lambda _provider, action: action,
        evaluate_temporal=forbidden,
    )
    interface = compiler.compile(primitive).interface
    temporal = outputs.temporal(outputs.leaf(interface), primitive, interface)
    with pytest.raises(TypeError, match="completed spatial"):
        tuple(outputs.iter_observe_range(temporal, 0, 1, 0, 0))
    assert not outputs._stream_frames


def test_partial_stream_rejects_temporal_sibling_without_traversing_it() -> None:
    actions, primitive, semantics, runtime, interfaces, compiler, sources, binding = (
        _fixture((7, 18))
    )

    def forbidden(*_args: object) -> Never:
        pytest.fail("stream reopened a temporal witness")

    outputs = RecursiveCoordinateMorphismArena(
        interfaces,
        evaluate=semantics.evaluate,
        validate_action=actions.resolve,
        compose_actions=actions.compose,
        complete_temporal_action=lambda _provider, action: action,
        evaluate_temporal=forbidden,
    )
    outputs, composer = _macro_composer(
        semantics, interfaces, sources, primitive, compiler, outputs
    )
    macro = composer.compile(binding)
    temporal = outputs.temporal(macro.output, primitive, macro.interface)
    root = outputs.branch(
        macro.output, temporal, macro.interface, macro.interface, macro.width
    )
    nested = outputs.branch(
        macro.output, root, macro.interface, macro.interface, macro.width
    )
    left = semantics.evaluate(runtime.initial(primitive, 0))
    right = semantics.evaluate(runtime.initial(primitive, 1))
    with pytest.raises(TypeError, match="completed spatial"):
        tuple(outputs.iter_observe_range(root, 0, 1, left, right))
    with pytest.raises(TypeError, match="completed spatial"):
        tuple(outputs.iter_observe_range(nested, 0, 1, left, right))
    with pytest.raises(ValueError, match="completion disagrees"):
        outputs._intern(
            RecursiveOutputBranch(
                macro.output,
                temporal,
                macro.interface,
                macro.interface,
                macro.width,
                spatial_complete=True,
            )
        )
    assert not outputs._stream_frames


def test_stream_rejects_foreign_handles_and_invalid_ranges() -> None:
    outputs, root, left, right = _spatial((7, 18))
    foreign, *_ = _spatial((7, 18))
    with pytest.raises(ValueError):
        tuple(foreign.iter_observe_range(root, 0, 1, left, right))
    for lo, hi in ((-1, 1), (2, 1), (True, 1)):
        with pytest.raises(ValueError, match="output range"):
            tuple(outputs.iter_observe_range(root, lo, hi, left, right))
    assert not outputs._stream_frames
