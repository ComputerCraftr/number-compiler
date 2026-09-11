"""Exhaustive contracts for closed reverse-add interval functions."""

from __future__ import annotations

from dataclasses import replace
from typing import Literal, cast

import pytest

from number_compiler.arithmetic.carry.reverse_port_functions import (
    ReverseLeftTransfer,
    ReversePortCodec,
    ReversePortFunction,
    ReverseRightTransfer,
)
from number_compiler.arithmetic.contracts.block_effect import (
    BoundarySide,
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    _BaseLeftState,
    _BaseRightState,
)
from number_compiler.arithmetic.functions.finite_function_types import FinitePort
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.tile_reverse_functions import (
    reverse_leaf_components,
    reverse_parent_components,
)
from number_compiler.hashlife.interfaces.closed_interface_admission import (
    validate_reverse_channel_roles,
)
from number_compiler.resources.closed_interface_workspace import (
    ClosedInterfaceWorkspace,
)
from number_compiler.resources.ledger import ResourceLedger


def _ports(codec: ReversePortCodec) -> tuple[FinitePort, ...]:
    return (
        FinitePort(PortVariable(0, 0, "tile-left", 0), codec.left_count),
        FinitePort(PortVariable(0, 1, "tile-right", 0), codec.right_count),
    )


@pytest.mark.parametrize("base", range(2, 16))
def test_reverse_port_codec_matches_the_admitted_primitive_domains(base: int) -> None:
    effect = BaseBlockEffect(base)
    codec = ReversePortCodec(base)
    left = effect.boundary_universe(BoundarySide.LEFT)
    right = effect.boundary_universe(BoundarySide.RIGHT)
    assert left is not None and right is not None
    left_states = cast(tuple[_BaseLeftState, ...], left)
    right_states = cast(tuple[_BaseRightState, ...], right)
    assert tuple(codec.decode_left(index) for index in range(codec.left_count)) == left
    assert (
        tuple(codec.decode_right(index) for index in range(codec.right_count)) == right
    )
    assert tuple(codec.encode_left(state) for state in left_states) == tuple(
        range(codec.left_count)
    )
    assert tuple(codec.encode_right(state) for state in right_states) == tuple(
        range(codec.right_count)
    )


@pytest.mark.parametrize("base", range(2, 16))
def test_reverse_closed_leaf_transfers_and_outputs_match_exact_kernel(
    base: int,
) -> None:
    effect = BaseBlockEffect(base)
    codec = ReversePortCodec(base)
    ports = _ports(codec)
    ledger = ResourceLedger()
    workspace = ClosedInterfaceWorkspace(ledger, "reverse-test")
    for symbol in range(effect.blank + 1):
        with workspace.scope("leaf"):
            components = reverse_leaf_components(
                ports, base, symbol, ledger
            ).functions()
        assert all(type(item) is ReversePortFunction for item in components)
        functions = tuple(
            item for item in components if type(item) is ReversePortFunction
        )
        for left in range(codec.left_count):
            left_state = codec.decode_left(left)
            advanced_left = cast(
                _BaseLeftState,
                effect.advance(BoundarySide.LEFT, left_state, symbol),
            )
            for right in range(codec.right_count):
                right_state = codec.decode_right(right)
                concrete = left, right
                advanced_right = cast(
                    _BaseRightState,
                    effect.advance(BoundarySide.RIGHT, right_state, symbol),
                )
                expected = effect.emit(left_state, symbol, right_state)
                active = int(expected != effect.blank)
                assert tuple(
                    function.evaluate(concrete, ledger) for function in functions
                ) == (
                    codec.encode_left(advanced_left),
                    codec.encode_right(advanced_right),
                    expected,
                    active,
                    active,
                    active,
                    active,
                    expected,
                    expected,
                    active,
                    1 - active,
                    0,
                    0,
                )
    assert ledger.nodes == 0
    assert ledger.counters.get("reverse_port_predicate_state_evaluations", 0) == 0


@pytest.mark.parametrize("base", range(2, 16))
def test_reverse_activity_mask_is_the_exact_closed_port_predicate(base: int) -> None:
    codec = ReversePortCodec(base)
    blank = 2 * base - 1
    for symbol in range(blank + 1):
        truth = codec.active_truth_bits(symbol)
        for index in range(codec.left_count):
            state = codec.decode_left(index)
            expected = not state.sink and (
                symbol != blank
                or (
                    not state.blank_seen
                    and state.previous_pair >= 0
                    and state.carry == 1
                )
            )
            assert ((truth >> index) & 1) == int(expected)


def test_reverse_activity_mask_does_not_decode_the_left_state_domain(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codec = ReversePortCodec(10)

    def forbidden(*_args: object, **_kwargs: object) -> _BaseLeftState:
        raise AssertionError("closed activity mask enumerated left states")

    monkeypatch.setattr(ReversePortCodec, "decode_left", forbidden)
    assert codec.active_truth_bits(0).bit_count() == codec.left_count - 1
    assert codec.active_truth_bits(19).bit_count() == 10


@pytest.mark.parametrize("base", (2, 3, 10, 15))
def test_reverse_transfer_composition_is_closed_in_both_directions(
    base: int,
) -> None:
    effect = BaseBlockEffect(base)
    codec = ReversePortCodec(base)
    for first in range(effect.blank + 1):
        for second in range(effect.blank + 1):
            left = ReverseLeftTransfer.leaf(base, first).then(
                ReverseLeftTransfer.leaf(base, second)
            )
            right = ReverseRightTransfer.leaf(base, second).then(
                ReverseRightTransfer.leaf(base, first)
            )
            for index in range(codec.left_count):
                left_state = codec.decode_left(index)
                expected_left = cast(
                    _BaseLeftState,
                    effect.advance(BoundarySide.LEFT, left_state, first),
                )
                expected_left = cast(
                    _BaseLeftState,
                    effect.advance(BoundarySide.LEFT, expected_left, second),
                )
                assert left.apply(left_state) == expected_left
            for index in range(codec.right_count):
                right_state = codec.decode_right(index)
                expected_right = cast(
                    _BaseRightState,
                    effect.advance(BoundarySide.RIGHT, right_state, second),
                )
                expected_right = cast(
                    _BaseRightState,
                    effect.advance(BoundarySide.RIGHT, expected_right, first),
                )
                assert right.apply(right_state) == expected_right


@pytest.mark.parametrize("base", (2, 3, 10, 15))
def test_reverse_predicate_preimage_matches_every_left_state(base: int) -> None:
    codec = ReversePortCodec(base)
    limit = (1 << codec.left_count) - 1
    predicates = (0, limit, 0x1555555555555555 & limit) + tuple(
        1 << index for index in range(codec.left_count)
    )
    symbols = tuple(range(2 * base))
    transfers = {
        ReverseLeftTransfer.identity(base),
        *(ReverseLeftTransfer.leaf(base, symbol) for symbol in symbols),
        *(
            ReverseLeftTransfer.leaf(base, first).then(
                ReverseLeftTransfer.leaf(base, second)
            )
            for first in symbols
            for second in symbols
        )
    }
    for transfer in transfers:
        for truth in predicates:
            pulled = transfer.predicate_preimage(truth)
            for index in range(codec.left_count):
                target = codec.encode_left(transfer.apply(codec.decode_left(index)))
                assert ((pulled >> index) & 1) == ((truth >> target) & 1)


@pytest.mark.parametrize("base", (2, 3, 10, 15))
def test_reverse_parent_channels_match_two_cell_exact_bimachine(base: int) -> None:
    effect = BaseBlockEffect(base)
    codec = ReversePortCodec(base)
    ports = _ports(codec)
    ledger = ResourceLedger()
    workspace = ClosedInterfaceWorkspace(ledger, "reverse-test")
    blank = effect.blank
    cases = ((0, blank - 1), (base - 1, base), (blank - 1, blank), (blank, 0))
    for first, second in cases:
        with workspace.scope("leaf"):
            first_components = reverse_leaf_components(ports, base, first, ledger)
        with workspace.scope("leaf"):
            second_components = reverse_leaf_components(ports, base, second, ledger)
        with workspace.scope("parent"):
            parent = reverse_parent_components(
                first_components, second_components, ledger
            ).functions()
        functions = tuple(item for item in parent if type(item) is ReversePortFunction)
        assert len(functions) == 13
        for left in range(codec.left_count):
            left_state = codec.decode_left(left)
            left_mid = effect.advance(BoundarySide.LEFT, left_state, first)
            left_out = effect.advance(BoundarySide.LEFT, left_mid, second)
            for right in range(codec.right_count):
                right_state = codec.decode_right(right)
                right_mid = effect.advance(BoundarySide.RIGHT, right_state, second)
                right_out = effect.advance(BoundarySide.RIGHT, right_mid, first)
                concrete = left, right
                first_output = effect.emit(left_state, first, right_mid)
                second_output = effect.emit(left_mid, second, right_state)
                assert functions[0].evaluate(concrete, ledger) == codec.encode_left(
                    cast(_BaseLeftState, left_out)
                )
                assert functions[1].evaluate(concrete, ledger) == codec.encode_right(
                    cast(_BaseRightState, right_out)
                )
                assert functions[2].evaluate(concrete, ledger) == first_output
                assert functions[7].evaluate(concrete, ledger) == first_output
                assert functions[8].evaluate(concrete, ledger) == second_output
                assert functions[3].evaluate(concrete, ledger) == int(
                    first_output != effect.blank or second_output != effect.blank
                )
                assert functions[4].evaluate(concrete, ledger) == int(
                    first_output != effect.blank
                )
                assert functions[5].evaluate(concrete, ledger) == int(
                    second_output != effect.blank
                )
    assert ledger.nodes == 0
    assert ledger.counters["reverse_port_carry_compositions"] > 0
    assert ledger.counters["reverse_port_construction_workspace_peak"] == 512


@pytest.mark.parametrize("base", (1, 16, 32))
def test_reverse_closed_codec_rejects_uncertified_base(base: int) -> None:
    with pytest.raises(ValueError, match="radix 2 through 15"):
        ReversePortCodec(base)


def test_reverse_channel_roles_reject_summary_and_output_aliases() -> None:
    codec = ReversePortCodec(10)
    ports = _ports(codec)
    ledger = ResourceLedger()
    workspace = ClosedInterfaceWorkspace(ledger, "reverse-role-test")
    with workspace.scope("leaf"):
        components = reverse_leaf_components(ports, 10, 9, ledger)
    values = components.functions()
    validate_reverse_channel_roles(values)
    with pytest.raises(ValueError, match="output or halo"):
        validate_reverse_channel_roles(values[:7] + (values[3],) + values[8:])
    activity = cast(ReversePortFunction, values[3])
    forged_extent = replace(activity, truth_bits=activity.truth_bits ^ 1)
    with pytest.raises(ValueError, match="activity summaries"):
        validate_reverse_channel_roles(values[:6] + (forged_extent,) + values[7:])


@pytest.mark.parametrize(("kind", "limit"), (("leaf", 0), ("parent", 511)))
def test_reverse_workspace_rejects_before_construction(
    kind: Literal["leaf", "parent"], limit: int
) -> None:
    ledger = ResourceLedger(max_nodes=limit)
    workspace = ClosedInterfaceWorkspace(ledger, "reverse-budget-test")
    with pytest.raises(BlockContextBudgetExceeded):
        with workspace.scope(kind):
            raise AssertionError("exhausted workspace entered construction")
    assert ledger.nodes == 0
    assert workspace.nodes == 0
