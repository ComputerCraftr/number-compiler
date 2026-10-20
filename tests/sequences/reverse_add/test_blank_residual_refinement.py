"""Exhaustive primitive blank residual checks for reverse/add.

The finite kernels here are independent of the recursive source-cell owner.
They pin down the exact left/right port action and the one possible terminal
digit, so a Hashlife shortcut can be checked against the literal local law.
"""

from __future__ import annotations

from typing import Never, cast

import pytest

from number_compiler.arithmetic.carry.reverse_port_functions import (
    ReverseLeftTransfer,
    ReversePortCodec,
    ReverseRightTransfer,
)
from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    BaseLeftState,
    BaseRightState,
)
from number_compiler.hashlife.execution.field_images import (
    SourceCellArena,
    SourceCellID,
)
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.sequences.reverse_add.higher_schema import (
    ReverseHigherActionSchema,
)
from tests.support.reverse_higher_runtime import macro_composer, reverse_higher_fixture


def test_decimal_blank_pair_residual_is_left_idempotent_and_right_identity() -> None:
    base = 10
    blank = 2 * base - 1
    kernel = BaseBlockEffect(base)
    codec = ReversePortCodec(base)
    left_transfer = ReverseLeftTransfer.leaf(base, blank)
    right_transfer = ReverseRightTransfer.leaf(base, blank)

    left_states = tuple(codec.decode_left(index) for index in range(codec.left_count))
    right_states = tuple(
        codec.decode_right(index) for index in range(codec.right_count)
    )
    assert len(left_states) == 43
    assert len(right_states) == 5
    assert left_transfer != ReverseLeftTransfer.identity(base)
    assert right_transfer == ReverseRightTransfer.identity(base)
    assert left_transfer.then(left_transfer) == left_transfer

    for state in left_states:
        once = cast(BaseLeftState, kernel.advance(BoundarySide.LEFT, state, blank))
        twice = cast(BaseLeftState, kernel.advance(BoundarySide.LEFT, once, blank))
        assert left_transfer.apply(state) == once
        assert left_transfer.apply(once) == twice == once
        assert codec.decode_left(codec.encode_left(once)) == once

    for right_state in right_states:
        advanced = cast(
            BaseRightState,
            kernel.advance(BoundarySide.RIGHT, right_state, blank),
        )
        assert advanced == right_state
        assert right_transfer.apply(right_state) == right_state


def test_first_blank_can_emit_once_and_later_pair_blanks_are_dead() -> None:
    base = 10
    blank = 2 * base - 1
    kernel = BaseBlockEffect(base)
    codec = ReversePortCodec(base)
    left_states = tuple(codec.decode_left(index) for index in range(codec.left_count))
    right_states = tuple(
        codec.decode_right(index) for index in range(codec.right_count)
    )

    live_first_outputs = 0
    for left in left_states:
        after_first = kernel.advance(BoundarySide.LEFT, left, blank)
        assert kernel.advance(BoundarySide.LEFT, after_first, blank) == after_first
        for right in right_states:
            first = kernel.emit(left, blank, right)
            later = kernel.emit(after_first, blank, right)
            assert later == blank
            if first != blank:
                live_first_outputs += 1
                assert not left.sink
                assert not left.blank_seen
                assert left.previous_pair >= 0
                assert left.carry == 1
                assert first == left.previous_pair % base + 1

    assert live_first_outputs > 0


def test_digit_terminal_blank_residual_has_one_live_boundary_cell() -> None:
    effect = DigitNormalizeBlockEffect(10)
    left_states = effect.boundary_universe(BoundarySide.LEFT)
    right_states = effect.boundary_universe(BoundarySide.RIGHT)
    assert len(left_states) == 4
    assert right_states == (0,)
    assert effect.blank_left_tail == 1
    assert effect.blank_right_tail == 0
    assert effect.stable_blank_output

    live_first_outputs = 0
    for left in left_states:
        after_first = effect.advance(BoundarySide.LEFT, left, effect.blank)
        assert effect.advance(BoundarySide.LEFT, after_first, effect.blank) == (
            after_first
        )
        first = effect.emit(left, effect.blank, 0)
        later = effect.emit(after_first, effect.blank, 0)
        assert later == effect.blank
        if first != effect.blank:
            live_first_outputs += 1
            assert first == 1

    assert live_first_outputs == 1


@pytest.mark.parametrize(
    ("source", "terminal", "expected", "source_extent", "expected_extent", "squares"),
    (
        ((19,) * 8, False, (19,) * 8, 0, 0, 3),
        ((19,) * 8, True, (19,) * 8, 0, 0, 3),
        (
            (18, 18, 18, 18, 19, 19, 19, 19),
            False,
            (9, 18, 18, 18, 9, 19, 19, 19),
            4,
            5,
            2,
        ),
        (
            (18, 18, 18, 18, 19, 19, 19, 19),
            True,
            (8, 9, 9, 9, 1, 19, 19, 19),
            4,
            5,
            2,
        ),
    ),
)
def test_blank_macro_preserves_first_output_and_stream_without_runtime_replay(
    source: tuple[int, ...],
    terminal: bool,
    expected: tuple[int, ...],
    source_extent: int,
    expected_extent: int,
    squares: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        _actions,
        primitive,
        semantics,
        runtime,
        interfaces,
        compiler,
        sources,
        binding,
    ) = reverse_higher_fixture(source)
    assert type(sources) is SourceCellArena
    schema = cast(ReverseHigherActionSchema, semantics.schema)
    action = schema.terminal if terminal else primitive
    left = semantics.evaluate(runtime.initial(action, 0))
    right = semantics.evaluate(runtime.initial(action, 1))
    source_children = sources.children
    traversed_active_nodes = 0

    def guarded_children(
        source_id: SourceCellID,
    ) -> tuple[SourceCellID, SourceCellID]:
        nonlocal traversed_active_nodes
        source_node = sources.resolve(source_id)
        if source_node.uniform_symbol == 19:
            raise AssertionError("uniform blank subtree was recursively opened")
        traversed_active_nodes += 1
        return source_children(source_id)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("blank spatial construction reopened the runtime")

    monkeypatch.setattr(sources, "children", guarded_children)
    for name in ("step", "emit", "boundary"):
        monkeypatch.setattr(runtime, name, forbidden)

    outputs, composer = macro_composer(
        semantics,
        interfaces,
        sources,
        action,
        compiler,
    )
    macro = composer.compile(binding)
    assert macro.width == len(source)
    assert macro.source_extent == source_extent
    assert semantics.ledger.counters["higher_blank_run_squares"] == squares
    assert semantics.ledger.counters["higher_blank_run_publications"] == 1

    record = interfaces.resolve(macro.interface)
    signature = interfaces.interface(record.signature)
    ports = {port.role: port.variable for port in signature.inputs}
    bound = {ports["left-boundary"]: left, ports["right-boundary"]: right}
    assert semantics.evaluate(macro.extent, bound) == expected_extent
    encoded_growth = semantics.evaluate(macro.growth, bound)
    assert type(encoded_growth) is int
    assert encoded_growth - macro.width == expected_extent - source_extent
    assert (
        tuple(
            outputs.observe(macro.output, coordinate, left, right)
            for coordinate in range(macro.width)
        )
        == expected
    )
    if source_extent:
        assert expected[4] == (1 if terminal else 9)
        assert expected[5:] == (19, 19, 19)
    else:
        assert expected == (19,) * 8
    if source_extent:
        assert traversed_active_nodes > 0
    else:
        assert traversed_active_nodes == 0

    stream = outputs.iter_observe_range(macro.output, 0, macro.width, left, right)
    assert next(stream) == expected[0]
    stream.close()
    assert outputs.audit_snapshot().stream_frame_count == 0
    assert (
        tuple(outputs.iter_observe_range(macro.output, 0, macro.width, left, right))
        == expected
    )
    assert outputs.audit_snapshot().stream_frame_count == 0
    assert all(item.accounting_delta == 0 for item in semantics.ledger.inventory())


def test_blank_hook_rejects_composite_and_foreign_action_authorities() -> None:
    actions, primitive, semantics, _runtime, _interfaces, _compiler, *_rest = (
        reverse_higher_fixture((19,))
    )
    schema = cast(ReverseHigherActionSchema, semantics.schema)
    composite = actions.compose(primitive, primitive)
    assert schema.primitive_blank_run(primitive)
    assert not schema.primitive_blank_run(composite)
    with pytest.raises(ValueError, match="temporal composites"):
        ReverseHigherActionSchema(actions, composite, schema.terminal)
    with pytest.raises(ValueError, match="temporal composites"):
        ReverseHigherActionSchema(actions, primitive, composite)

    _foreign_actions, foreign_primitive, *_ = reverse_higher_fixture((1,))
    with pytest.raises(ValueError, match="different arena"):
        schema.primitive_blank_run(foreign_primitive)
