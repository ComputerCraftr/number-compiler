"""Adversarial scheduler admission must precede every cache/work mutation."""

from __future__ import annotations

from tests.support.assertions import assert_rejected_atomically

from dataclasses import replace
from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.diamond_actions import CellID
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    Evaluate,
    Initial,
    Output,
    Substitute,
    Task,
    Transfer,
)
from number_compiler.hashlife.interfaces.diamond_boundary import (
    ContinuationStep,
    ImageBinding,
)
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.observation.diamond_observers import NonblankBlockEffect
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.interfaces.diamond_boundary import (
        BoundaryStateID,
    )


def setup() -> tuple[
    DiamondRuntime, ActionProgramID, ImageBinding, BoundaryStateID, BoundaryStateID
]:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    atom = compiler.atom(CollatzPhysicalBlockEffect())
    geometry = SourceGeometry(
        ledger, ExactSource((1, 1, 0, 1, 1), 2, blank=2, extent=8)
    )
    geometry.span((1, 1, 0, 1, 1), 2, 8)
    runtime = DiamondRuntime(compiler, geometry)
    action = runtime.actions.intern(atom)
    identity = runtime.actions.identity
    unit_left = runtime.execute(Initial(identity, 0))
    unit_right = runtime.execute(Initial(identity, 1))
    provider = ImageBinding(identity, runtime.cells.source(0, 3), unit_left, unit_right)
    left = runtime.execute(Initial(action, 0))
    right = runtime.execute(Initial(action, 1))
    return runtime, action, provider, left, right


def assert_rejected(
    runtime: DiamondRuntime,
    request: Task,
) -> None:
    before = assert_rejected_atomically(
        runtime.ledger, lambda: runtime.execute(request), (TypeError, ValueError)
    )
    with pytest.raises((TypeError, ValueError)):
        runtime._probe(request)
    assert runtime.ledger.snapshot() == before


@pytest.mark.parametrize("warm", [False, True])
def test_foreign_scope_boolean_direction_and_provider_rejected_before_work(
    warm: bool,
) -> None:
    runtime, action, provider, left, right = setup()
    foreign, other_action, other_provider, other_left, other_right = setup()
    if warm:
        runtime.execute(Transfer(provider, action, left, 0))
        runtime.execute(Transfer(provider, action, right, 1))
    bad_provider = replace(provider, cell=other_provider.cell)
    assert isinstance(provider.cell, CellID)
    image_provider = replace(provider, cell=runtime.cells.image(action, provider.cell))
    requests: list[Task] = [
        Initial(other_action, 0),
        Initial(action, True),
        Transfer(provider, action, left, False),
        Transfer(provider, action, other_left, 0),
        Transfer(bad_provider, action, left, 0),
        Transfer(image_provider, action, left, 0),
        Transfer(provider, other_action, other_right, 1),
        Transfer(provider, runtime.actions.identity, provider.left, True),
        Output(provider, action, left, right),
    ]
    for request in requests:
        assert_rejected(runtime, request)
    before = foreign.ledger.snapshot()
    runtime.execute(Transfer(provider, action, left, 0))
    assert foreign.ledger.snapshot() == before


@pytest.mark.parametrize("warm", [False, True])
def test_continuation_domain_and_substitution_codomain_checked_before_warm_lookup(
    warm: bool,
) -> None:
    runtime, action, provider, left, right = setup()
    foreign, _, _, foreign_left, _ = setup()
    function = runtime.boundaries.constant(left, action, 1)
    foreign_function = foreign.boundaries.constant(
        foreign_left,
        foreign_left_action := foreign.boundaries.state(foreign_left).action,
        1,
    )
    wrong_domain = runtime.boundaries.constant(left, action, 0)
    wrong_codomain = runtime.boundaries.constant(provider.left, action, 1)
    step = ContinuationStep(action, action, 0, function, provider, left)
    if warm:
        runtime.execute(Evaluate(function, right))
        runtime.execute(Substitute(step, right))
    requests: list[Task] = [
        Evaluate(function, left),
        Evaluate(function, provider.right),
        Evaluate(foreign_function, right),
        Evaluate(function, foreign_left),
        Substitute(replace(step, previous=wrong_domain), right),
        Substitute(replace(step, previous=wrong_codomain), right),
        Substitute(replace(step, provider=replace(provider, left=right)), right),
        Substitute(step, provider.right),
    ]
    assert foreign_left_action != action
    for request in requests:
        assert_rejected(runtime, request)


def test_alphabet_mismatch_is_rejected_before_source_proof_or_image_publication() -> (
    None
):
    runtime, _, provider, _, _ = setup()
    other = runtime.actions.compiler.atom(BaseBlockEffect(3))
    other_action = runtime.actions.intern(other)
    other_left = runtime.execute(Initial(other_action, 0))
    other_right = runtime.execute(Initial(other_action, 1))
    assert_rejected(runtime, Transfer(provider, other_action, other_left, 0))
    incompatible_provider = ImageBinding(
        other_action, provider.cell, other_left, other_right
    )
    assert_rejected(
        runtime,
        Transfer(incompatible_provider, runtime.actions.identity, provider.left, 0),
    )


def test_warm_spatial_transfer_returns_without_dispatch_or_scalar_response_cache(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, action, provider, left, _ = setup()
    task = Transfer(provider, action, left, 0)
    expected = runtime.execute(task)
    before = runtime.ledger.snapshot()

    def forbidden(*args: object) -> Never:
        raise AssertionError("warm parent descended into its execution program")

    monkeypatch.setattr(runtime, "_program", forbidden)
    assert runtime.execute(task) == expected
    after = runtime.ledger.snapshot()
    assert (
        after.counters["spatial_parent_cache_hits"]
        == before.counters["spatial_parent_cache_hits"] + 1
    )
    assert (
        after.counters["scalar_observation_requests"]
        == before.counters["scalar_observation_requests"]
    )
    assert after.nodes == before.nodes and after.entries == before.entries


def test_unknown_task_subclasses_cannot_reuse_known_interface_dispatch() -> None:
    runtime, action, _, _, _ = setup()

    class AliasInitial(Initial):
        pass

    assert_rejected(runtime, AliasInitial(action, 0))


@pytest.mark.parametrize(
    "effect", [NonblankBlockEffect(2, 1 << 1000), DigitNormalizeBlockEffect(1 << 1000)]
)
def test_oversized_primitive_alphabets_reject_before_admission_work(
    effect: NonblankBlockEffect | DigitNormalizeBlockEffect,
) -> None:
    arena = DiamondKernelArena()
    arena.intern(CollatzPhysicalBlockEffect())
    assert_rejected_atomically(
        arena.ledger, lambda: arena.intern(effect), ValueError, match="64-bit"
    )
