"""Cold and warm scope attacks plus exact geometric/finite-port automorphisms."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import fields
from itertools import product
from typing import TypeVar, cast

import pytest

from number_compiler.arithmetic.automata.symmetry_powering import (
    ActionTransform,
    BinaryLiftEngine,
    FiniteKernel,
    OrientedFiniteActionArena,
)
from number_compiler.arithmetic.carry.carry_symmetry import (
    collatz_mul3_carry_action_arena,
    reverse_add_carry_action_arena,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    ArenaToken,
    CarryBit,
    ExactSource,
    FrameTransform,
    TransferSummaryID,
    WordLimb,
)
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.collatz_diamond_fixtures import build_collatz_diamond_runtime
from tests.support.diamond_actions import arenas

HandleT = TypeVar("HandleT", bound=ArenaHandle)


def forged(reference: HandleT, **changes: object) -> HandleT:
    result = object.__new__(type(reference))
    for field in fields(reference):
        object.__setattr__(
            result, field.name, changes.get(field.name, getattr(reference, field.name))
        )
    return result


@pytest.mark.parametrize("warm", (False, True))
@pytest.mark.parametrize(
    "change",
    (
        {"local_id": True},
        {"local_id": -1},
        {"local_id": 0.0},
        {"local_id": 10**9},
        {"kind": "other"},
        {"owner": ArenaToken("other")},
    ),
)
def test_scoped_action_source_formal_and_boundary_handles_reject_forgery(
    warm: bool, change: dict[str, object]
) -> None:
    runtime, action = build_collatz_diamond_runtime(
        CollatzPhysicalBlockEffect(), (0, 1, 0, 1), 4, 1
    )
    source = runtime.cells.source(0, 1)
    formal = runtime.cells.formal_symbol(1)
    state = runtime.boundaries.literal(action, 1, 0)
    function = runtime.boundaries.constant(state, action, 0)

    def sample(
        handle: HandleT, resolve: Callable[[HandleT], object]
    ) -> Callable[[bool], object]:
        return lambda corrupt: resolve(forged(handle, **change) if corrupt else handle)

    samples = (
        sample(action, runtime.actions.resolve),
        sample(source, runtime.cells.resolve),
        sample(formal, runtime.cells.validate_input),
        sample(state, runtime.boundaries.state),
        sample(function, runtime.boundaries.action),
    )
    if warm:
        for resolve in samples:
            resolve(False)
    before = runtime.ledger.snapshot()
    for resolve in samples:
        with pytest.raises(ValueError):
            resolve(True)
        assert runtime.ledger.snapshot() == before
    with pytest.raises(ValueError):
        runtime.actions.power(forged(action, **change), 0)
    assert runtime.ledger.snapshot() == before


def test_mirror_slice_is_a_geometric_alias_without_commuting_evolution() -> None:
    _, _, _, cells, action, _ = arenas()
    source = cells.source(0, 4)
    reflected = cells.mirror(source)
    assert cells.join(*cells.split(reflected)) == reflected
    for position in range(16):
        leaf = cells.slice(reflected, position, 0)
        assert leaf == cells.source(15 - position, 0)
        assert cells.source_symbol(leaf) == cells.source_geometry.read(15 - position)
    for level in range(4):
        width = 1 << level
        for start in range(0, 16, width):
            assert cells.slice(reflected, start, level) == cells.mirror(
                cells.slice(source, 16 - start - width, level)
            )
    image = cells.image(action, source)
    assert cells.slice(cells.mirror(image), 0, 2) == cells.mirror(
        cells.slice(image, 12, 2)
    )
    assert cells.mirror(cells.mirror(image)) == image
    assert cells.join(*cells.split(cells.mirror(image))) == cells.mirror(image)
    # M(A(C)) keeps A and its original port wiring inside the image. This is
    # geometry, not a claim that reverse-add's evolution commutes with mirror.
    assert cells.node(cells.mirror(image)).left == image.local_id


@pytest.mark.parametrize(
    "factory", (reverse_add_carry_action_arena, collatz_mul3_carry_action_arena)
)
def test_mirror_conjugacy_and_combination_match_all_finite_ports_after_eviction(
    factory: Callable[[int], OrientedFiniteActionArena],
) -> None:
    arena = factory(4)
    arena.compose_cache_limit = 1
    kernel = arena.kernel
    transforms = (
        ActionTransform.IDENTITY,
        ActionTransform.MIRROR,
        ActionTransform.CONJUGATE,
        ActionTransform.MIRROR | ActionTransform.CONJUGATE,
    )
    for word in product((0, 1, kernel.alphabet_size - 1), repeat=3):
        action = arena.compose(
            arena.compose(arena.leaf(word[0]), arena.leaf(word[1])), arena.leaf(word[2])
        )
        for transform in transforms:
            moved = arena.transformed(action, transform)
            expected_word = (
                tuple(reversed(word)) if transform & ActionTransform.MIRROR else word
            )
            if transform & ActionTransform.CONJUGATE:
                assert kernel.symbol_conjugate is not None
                expected_word = tuple(
                    kernel.symbol_conjugate[symbol] for symbol in expected_word
                )
            for reverse in (False, True):
                for incoming in range(kernel.state_count):
                    state = incoming
                    for symbol in reversed(expected_word) if reverse else expected_word:
                        state = kernel.transition(state, symbol)
                    assert arena.apply(moved, incoming, reverse=reverse) == state
            assert arena.transformed(moved, transform) == action


@pytest.mark.parametrize(
    "change",
    (
        {"local_id": True},
        {"local_id": -1},
        {"transform": ActionTransform(4)},
        {"transform": 1},
    ),
)
def test_oriented_warm_action_revalidates_forged_id_and_transform(
    change: dict[str, object],
) -> None:
    arena = reverse_add_carry_action_arena()
    action = arena.leaf(1)
    arena.compose(action, action)
    before = arena.metrics(), arena.retained_entries
    with pytest.raises(ValueError):
        arena.transformed(forged(action, **change), ActionTransform.IDENTITY)
    assert (arena.metrics(), arena.retained_entries) == before


def test_handle_subclass_cannot_override_scope_validation() -> None:
    class Bypass(TransferSummaryID):
        def validate(self, *args: object, **kwargs: object) -> Bypass:
            return self

    arena, other = reverse_add_carry_action_arena(), reverse_add_carry_action_arena()
    arena.leaf(0)
    foreign = other.oriented_pair(other.leaf(18))[0]
    before = arena.metrics(), arena.retained_entries
    with pytest.raises(TypeError):
        arena.mapping(Bypass(foreign.owner, foreign.kind, foreign.local_id))
    assert (arena.metrics(), arena.retained_entries) == before


def test_same_kernel_name_or_digest_never_substitutes_semantics() -> None:
    first = FiniteKernel(2, 2, lambda q, a: q ^ a, name="same")
    second = FiniteKernel(2, 2, lambda q, a: a, name="same")
    object.__setattr__(second, "semantic_digest", first.semantic_digest)
    assert first != second
    invalid = FiniteKernel(
        2, 2, lambda q, a: 0, state_conjugate=(1, 0), symbol_conjugate=(1, 0)
    )
    with pytest.raises(ValueError):
        OrientedFiniteActionArena(invalid)


@pytest.mark.parametrize("alias", (True, 1.0))
def test_shared_powering_rejects_numeric_cache_limit_alias(alias: bool | float) -> None:
    with pytest.raises(TypeError):
        BinaryLiftEngine(
            step=lambda state: (state, 0),
            key=lambda state: state,
            identity_weight=0,
            combine_weight=lambda left, right: left + right,
            jump_cache_limit=cast("int", alias),
        )


@pytest.mark.parametrize("value", (True, 0.0))
def test_scalar_contracts_reject_numeric_aliases(value: bool | float) -> None:
    invalid = cast("int", value)
    for constructor in (
        lambda: CarryBit(invalid),
        lambda: WordLimb(invalid),
        lambda: WordLimb(0, invalid),
        lambda: FrameTransform(invalid),
        lambda: FrameTransform(0, cast("bool", 0)),
        lambda: ExactSource((invalid,), 2),
        lambda: ExactSource((0,), invalid),
        lambda: ExactSource((0,), 2, blank=invalid),
        lambda: ExactSource((0,), 2, extent=invalid),
        lambda: ExactSource((0,), 2, alphabet_size=invalid),
    ):
        with pytest.raises(TypeError):
            constructor()


@pytest.mark.parametrize("exponent", (False, True, 0.0, 1.0))
def test_binary_power_rejects_numeric_exponent_alias_before_warm_hit(
    exponent: bool | float,
) -> None:
    from number_compiler.arithmetic.automata.action_power import ActionPowerArena

    owner = ArenaToken("two-element-monoid")
    actions = tuple(ActionProgramID(owner, "test-action", index) for index in range(2))
    arena = ActionPowerArena(
        actions[0],
        lambda a, b: actions[a.local_id ^ b.local_id],
        validate=lambda a: a.validate(owner, "test-action", size=2).local_id,
    )
    arena.power(actions[1], 0)
    arena.power(actions[1], 1)
    before = arena.metrics()
    with pytest.raises(ValueError):
        arena.power(actions[1], cast("int", exponent))
    assert arena.metrics() == before


@pytest.mark.parametrize("value", (True, 0.5, 1.0, -1))
def test_finite_port_ordinals_do_not_coerce_to_warm_symbols_or_states(
    value: bool | float,
) -> None:
    invalid = cast("int", value)
    arena = reverse_add_carry_action_arena()
    action = arena.leaf(0)
    before = arena.metrics(), arena.retained_entries
    for operation in (
        lambda: arena.leaf(invalid),
        lambda: arena.apply(action, invalid),
        lambda: arena.kernel.transition(invalid, 0),
        lambda: arena.kernel.transition(0, invalid),
    ):
        with pytest.raises(ValueError):
            operation()
        assert (arena.metrics(), arena.retained_entries) == before
