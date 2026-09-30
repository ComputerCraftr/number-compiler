from __future__ import annotations

from tests.support.local_codec_assertions import assert_publication_refused

from typing import Never, cast

import pytest

from devtools.experiments.reverse_add.field_action import (
    ProofMachineStateID,
)
from devtools.experiments.reverse_add.local_interface import (
    ReverseLocalInterfaceArena,
    ReversePortStateID,
)
from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.arithmetic.contracts.block_effect import (
    BoundarySide,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken, ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.execution.field_images import (
    SourceCellArena,
    SourceCellID,
    SourceForestID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.powered_local_codec import (
    ReverseLocalActionID,
    ReversePoweredLocalCodec,
)
from tests.support.reverse_field_action import _source_cells


@pytest.mark.representation
def test_source_forest_binds_the_complete_non_power_of_two_occurrence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    values = (7, 18, 7)
    ledger = ResourceLedger()
    geometry = SourceGeometry(
        ledger,
        ExactSource(values, 10, blank=19, extent=11, alphabet_size=20),
    )
    geometry.span(values, 19, 11)
    cells = SourceCellArena(geometry)
    forest = cells.forest(0, 11)
    assert type(forest) is SourceForestID
    assert cells.forest(0, 11) == forest
    assert (
        sum(cells.resolve(cell).width for cell in cells.resolve_forest(forest).cells)
        == 11
    )
    assert tuple(cells.forest_read(forest, index) for index in range(11)) == (
        7,
        18,
        7,
        19,
        19,
        19,
        19,
        19,
        19,
        19,
        19,
    )
    assert cells.binding_extent(forest) == 11

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("bound source coordinate escaped to SourceGeometry")

    monkeypatch.setattr(SourceGeometry, "read", forbidden)
    monkeypatch.setattr(SourceGeometry, "range_tiles", forbidden)
    assert tuple(cells.binding_read(forest, index) for index in range(11)) == (
        7,
        18,
        7,
        19,
        19,
        19,
        19,
        19,
        19,
        19,
        19,
    )
    roles = {item.role for item in ledger.inventory()}
    assert "source_forest" in roles
    assert "source_forest_interner" in roles


@pytest.mark.algebra
def test_powered_local_codec_compiles_complete_source_forest() -> None:
    values = (7, 18, 7, 19, 19, 19, 19, 19, 19, 19, 19)
    ledger = ResourceLedger()
    geometry = SourceGeometry(
        ledger,
        ExactSource(values[:3], 10, blank=19, extent=len(values), alphabet_size=20),
    )
    geometry.span(values[:3], 19, len(values))
    cells = SourceCellArena(geometry)
    forest = cells.forest(0, len(values))
    codec = ReversePoweredLocalCodec(10, cells)
    action = codec.source_action(forest)
    for side in (BoundarySide.LEFT, BoundarySide.RIGHT):
        for reverse in (False, True):
            state = codec.kernel.initial(side)
            symbols = tuple(reversed(values)) if reverse else values
            for symbol in symbols:
                state = codec.kernel.advance(side, state, symbol)
            assert (
                codec.apply(action, side, codec.kernel.initial(side), reverse=reverse)
                == state
            )


@pytest.mark.representation
def test_source_cell_and_forest_local_bindings_cannot_integer_alias() -> None:
    ledger, cells, _root = _source_cells((1, 2))
    root = cells.intern(0, 0)
    forest = cells.forest(0, 1)
    assert root.local_id == forest.local_id == 0
    codec = ReversePoweredLocalCodec(10, cells, ledger=ledger)
    assert codec.source_action(root) == codec.source_action(forest)
    assert codec.metrics().source_bindings == 2
    assert all(
        type(key) in (SourceCellID, SourceForestID) for key in codec._source_actions
    )
    foreign = SourceForestID(ArenaToken("foreign"), "source-forest", 0)
    with pytest.raises(ValueError):
        codec.source_action(foreign)


@pytest.mark.algebra
@pytest.mark.parametrize("base", (2, 3, 4, 5, 10))
def test_powered_local_codec_matches_exact_directed_scans(base: int) -> None:
    word = tuple(value % (2 * base) for value in (1, 7, 4, 3, 6, 2, 5, 0))
    ledger, cells, root = _source_cells(word, base)
    codec = ReversePoweredLocalCodec(base, cells, ledger=ledger)
    action = codec.source_action(root)
    kernel = codec.kernel
    for side in (BoundarySide.LEFT, BoundarySide.RIGHT):
        for reverse in (False, True):
            expected = kernel.initial(side)
            symbols = tuple(reversed(word)) if reverse else word
            for symbol in symbols:
                expected = kernel.advance(side, expected, symbol)
            assert (
                codec.apply(
                    action,
                    side,
                    kernel.initial(side),
                    reverse=reverse,
                )
                == expected
            )
    assert codec.metrics().source_bindings > 0
    assert codec.metrics().action_count <= codec.metrics().source_bindings


@pytest.mark.algebra
def test_powered_local_codec_alias_does_not_imply_output_equivalence() -> None:
    """The four directed K maps are not a complete spacetime quotient.

    These two canonical dyadic source cells induce the same left/right word
    action in both orientations.  Their emitted successor words nevertheless
    differ under the same admissible exterior ports.  A powered tile compiler
    must therefore retain an independent output-substitution component; using
    ``ReverseLocalActionID`` as the completed tile identity would be unsound.
    """
    first = (0, 0, 0, 0)
    second = (0, 0, 1, 0)
    ledger, cells, root = _source_cells(first + second, base=2)
    left_source, right_source = cells.children(root)
    codec = ReversePoweredLocalCodec(2, cells, ledger=ledger)

    first_action = codec.source_action(left_source)
    second_action = codec.source_action(right_source)
    assert first != second
    assert first_action == second_action
    assert codec.resolve(first_action) == codec.resolve(second_action)

    kernel = codec.kernel
    exterior_left = kernel.initial(BoundarySide.LEFT)
    exterior_right = kernel.initial(BoundarySide.RIGHT)

    def emitted(word: tuple[int, ...]) -> tuple[int, ...]:
        left_states = []
        state = exterior_left
        for symbol in word:
            left_states.append(state)
            state = kernel.advance(BoundarySide.LEFT, state, symbol)
        right_states = [exterior_right] * len(word)
        state = exterior_right
        for index in range(len(word) - 1, -1, -1):
            right_states[index] = state
            state = kernel.advance(BoundarySide.RIGHT, state, word[index])
        return tuple(
            kernel.emit(left_states[index], symbol, right_states[index])
            for index, symbol in enumerate(word)
        )

    assert emitted(first) == (0, 0, 0, 0)
    assert emitted(second) == (0, 0, 2, 0)
    assert emitted(first) != emitted(second)


@pytest.mark.algebra
def test_powered_local_codec_is_associative_and_mirror_canonical() -> None:
    _, cells, _ = _source_cells((1, 2, 3, 4, 5, 6, 7, 8))
    codec = ReversePoweredLocalCodec(10, cells)
    a, b, c = (codec.leaf(value) for value in (2, 7, 12))
    assert codec.compose(codec.compose(a, b), c) == codec.compose(
        a, codec.compose(b, c)
    )
    ab = codec.compose(a, b)
    mirrored = codec.compose(
        codec.transformed(b, ActionTransform.MIRROR),
        codec.transformed(a, ActionTransform.MIRROR),
    )
    assert mirrored == codec.transformed(ab, ActionTransform.MIRROR)


@pytest.mark.representation
def test_powered_local_codec_rejects_unscoped_and_proof_ids() -> None:
    _, cells, root = _source_cells((1, 2))
    codec = ReversePoweredLocalCodec(10, cells)
    action = codec.source_action(root)
    before = codec.metrics()
    for invalid in (
        action.local_id,
        True,
        ProofMachineStateID(
            action.owner,
            "proof-machine-state",
            action.local_id,
        ),
    ):
        with pytest.raises((TypeError, ValueError)):
            codec.compose(cast(ReverseLocalActionID, invalid), action)
    assert codec.metrics() == before
    assert type(action) is ReverseLocalActionID
    record = codec.resolve(action)
    assert not hasattr(record, "digits")
    assert not hasattr(record, "tile")
    assert not hasattr(record, "carry_rows")
    assert all(
        type(value) is int
        for mapping in (
            record.left_forward,
            record.left_reverse,
            record.right_forward,
            record.right_reverse,
        )
        for value in mapping
    )


@pytest.mark.representation
def test_powered_local_codec_probes_canonical_source_before_child_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, cells, root = _source_cells((1, 2, 2, 1))
    codec = ReversePoweredLocalCodec(10, cells)
    first = codec.source_action(root)
    before = codec.metrics()

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("warm canonical source action descended to children")

    monkeypatch.setattr(codec, "leaf", forbidden)
    monkeypatch.setattr(codec, "compose", forbidden)
    assert codec.source_action(root) == first
    assert codec.metrics() == before


@pytest.mark.accounting
def test_reverse_local_codec_rejects_leaf_and_parent_publication_atomically() -> None:
    ledger, cells, _ = _source_cells((1, 2))
    codec = ReversePoweredLocalCodec(10, cells, ledger=ledger)
    assert_publication_refused(
        ledger,
        (codec._nodes, codec._keys, codec._leaf_actions, codec._compose),
        lambda: codec.leaf(3),
    )

    ledger, cells, _ = _source_cells((1, 2))
    codec = ReversePoweredLocalCodec(10, cells, ledger=ledger)
    left, right = codec.leaf(2), codec.leaf(7)
    assert_publication_refused(
        ledger,
        (codec._nodes, codec._keys, codec._compose),
        lambda: codec.compose(left, right),
    )


@pytest.mark.algebra
def test_mirrored_source_cells_share_one_semantic_local_action() -> None:
    _, cells, root = _source_cells((1, 2, 2, 1))
    codec = ReversePoweredLocalCodec(10, cells)
    left, right = cells.children(root)
    forward = codec.source_action(left)
    reverse = codec.source_action(right)
    assert forward.local_id == reverse.local_id
    assert reverse == codec.transformed(forward, ActionTransform.MIRROR)


@pytest.mark.parametrize("base", (2, 3, 4, 5, 10))
@pytest.mark.algebra
def test_reverse_local_interface_matches_primitive_without_proof_domains(
    base: int,
) -> None:
    ports = ReverseLocalInterfaceArena(base)
    kernel = ports.kernel
    left = ports.initial(BoundarySide.LEFT)
    right = ports.initial(BoundarySide.RIGHT)
    raw_left = kernel.initial(BoundarySide.LEFT)
    raw_right = kernel.initial(BoundarySide.RIGHT)
    word = tuple(range(2 * base - 1)) + (ports.blank,)
    for symbol in word:
        assert ports.emit(left, symbol, right) == kernel.emit(
            raw_left, symbol, raw_right
        )
        left = ports.advance(BoundarySide.LEFT, left, symbol)
        right = ports.advance(BoundarySide.RIGHT, right, symbol)
        raw_left = kernel.advance(BoundarySide.LEFT, raw_left, symbol)
        raw_right = kernel.advance(BoundarySide.RIGHT, raw_right, symbol)
        assert ports.resolve(BoundarySide.LEFT, left) == raw_left
        assert ports.resolve(BoundarySide.RIGHT, right) == raw_right
    metrics = ports.metrics()
    assert metrics.left_states < 757
    assert metrics.right_states <= 9


@pytest.mark.representation
def test_reverse_local_interface_rejects_foreign_and_wrong_side_ids_before_warm_hit() -> (
    None
):
    ports = ReverseLocalInterfaceArena(10)
    left = ports.initial(BoundarySide.LEFT)
    ports.advance(BoundarySide.LEFT, left, 7)
    before = ports.metrics()
    wrong_side = ReversePortStateID(ports.owner, "reverse-port-right", left.local_id)
    foreign = ReversePortStateID(ArenaToken("foreign"), left.kind, left.local_id)
    for invalid in (wrong_side, foreign, left.local_id, True):
        with pytest.raises((TypeError, ValueError)):
            ports.advance(BoundarySide.LEFT, cast(ReversePortStateID, invalid), 7)
    assert ports.metrics() == before
