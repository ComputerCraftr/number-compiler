"""Complete declared primitive-cell behavior, including every non-carry channel."""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

from number_compiler.hashlife.interfaces.semantic_structures import (
    LocalInterfaceID,
)
from tests.support.semantic_oracles import macro_oracle as oracle

if TYPE_CHECKING:
    import number_compiler.hashlife.execution.continuations.diamond_runtime
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    import number_compiler.hashlife.execution.continuations.diamond_tasks

from array import array
from collections.abc import Callable
from itertools import product
from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ExactSource,
)
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.hashlife.interfaces.semantic_primitive_macro import (
    PrimitiveMacroArena,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    COMPONENT_ROLES,
)
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import (
        TransferSummaryID,
    )
    from number_compiler.hashlife.interfaces.diamond_boundary import BoundaryStateID
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID
    from number_compiler.hashlife.interfaces.semantic_structures import StructureID


def primitive(mode: str = "nontrivial", left_count: int = 2) -> FiniteBlockEffect:
    if mode == "nontrivial":
        left = [(q + s) % left_count for q in range(left_count) for s in range(4)]
        right = [q ^ (s == 1) for q in range(2) for s in range(4)]
        output = [
            (a + s + 2 * r) % 4
            for a in range(left_count)
            for s in range(4)
            for r in range(2)
        ]
    else:
        left = right = [q for q in range(2) for _ in range(4)]
        output = [
            ((a + r) % 2 if mode == "forget-source" else s)
            for a in range(left_count)
            for s in range(4)
            for r in range(2)
        ]
    return FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=left_count,
        right_count=2,
        alphabet_size=4,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", left),
        right_transitions=array("I", right),
        outputs=bytes(output),
        kernel_name="test-fixed-cell",
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=False,
    )


def setup(
    effect: FiniteBlockEffect, source: tuple[int, ...]
) -> tuple[DiamondRuntime, PrimitiveMacroArena, ActionProgramID]:
    ledger = ResourceLedger()
    geometry = SourceGeometry(
        ledger,
        ExactSource(
            source,
            effect.base,
            blank=effect.blank,
            extent=len(source),
            alphabet_size=effect.blank + 1,
        ),
    )
    geometry.span(source, effect.blank, len(source))
    runtime = DiamondRuntime(LazyCompiler(ledger), geometry)
    kernel = runtime.kernels.intern(effect)
    arena = cast(
        "Callable[[], PrimitiveMacroArena]",
        object.__getattribute__(runtime, "_primitive_macro_arena"),
    )()
    return runtime, arena, kernel


def observe(
    arena: PrimitiveMacroArena,
    quotient: LocalInterfaceID,
    left: int,
    right: int,
    coordinate: int,
) -> dict[str, int | None]:
    record = arena.quotients.resolve(quotient)
    inputs = arena.quotients.interface(record.signature).inputs
    values = {
        port.variable: {
            "macro-left": left,
            "macro-right": right,
            "macro-coordinate": coordinate,
        }[port.variable.role]
        for port in inputs
    }
    return dict(
        zip(
            COMPONENT_ROLES,
            (
                arena.bits.evaluate(function, values)
                for function in arena.interface_components(quotient)
            ),
            strict=True,
        )
    )


@pytest.mark.parametrize(
    "word", [(0,), (3,), (0, 1), (3, 3), (0, 1, 3, 0), (3, 0, 3, 3)]
)
def test_all_ports_coordinates_and_thirteen_channels(
    word: tuple[int, int, int, int] | tuple[int, int] | tuple[int],
) -> None:
    effect = primitive()
    runtime, arena, kernel = setup(effect, word)
    cell = runtime.cells.source(0, len(word).bit_length() - 1)
    quotient = arena.compile(kernel, cell)
    for left, right, coordinate in product(range(2), range(2), range(len(word))):
        assert observe(arena, quotient, left, right, coordinate) == oracle(
            effect, word, left, right, coordinate
        )


def test_distinct_original_cells_can_share_complete_effect() -> None:
    runtime, arena, kernel = setup(primitive("forget-source"), (0, 1))
    first, second = runtime.cells.source(0, 0), runtime.cells.source(1, 0)
    assert first != second
    assert arena.compile(kernel, first) == arena.compile(kernel, second)
    assert len(arena.bindings) == 2


def test_equal_exits_do_not_merge_distinct_outputs_or_edge_symbols() -> None:
    runtime, arena, kernel = setup(primitive("identity"), (0, 1))
    first, second = (
        arena.compile(kernel, runtime.cells.source(i, 0)) for i in range(2)
    )
    a, b = observe(arena, first, 0, 1, 0), observe(arena, second, 0, 1, 0)
    assert (
        a["boundary_left"] == b["boundary_left"]
        and a["boundary_right"] == b["boundary_right"]
    )
    assert a["output"] != b["output"] and a["halo_left"] != b["halo_left"]
    assert first != second


def test_warm_parent_skips_children_but_validates_foreign_inputs(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, arena, kernel = setup(primitive(), (0, 1, 3, 0))
    cell = runtime.cells.source(0, 2)
    quotient = arena.compile(kernel, cell)

    def poison(*args: object, **kwargs: object) -> Never:
        raise AssertionError("warm parent replayed semantic construction")

    monkeypatch.setattr(PrimitiveMacroArena, "_parent", poison)
    monkeypatch.setattr(PrimitiveMacroArena, "_leaf", poison)
    assert arena.compile(kernel, cell) == quotient
    other, _, foreign = setup(primitive(), (0, 1, 3, 0))
    before = runtime.ledger.snapshot()
    with pytest.raises(ValueError):
        arena.compile(foreign, cell)
    with pytest.raises(ValueError):
        arena.compile(kernel, other.cells.source(0, 2))
    forged = object.__new__(ActionProgramID)
    for field, value in (
        ("owner", kernel.owner),
        ("kind", kernel.kind),
        ("local_id", True),
    ):
        object.__setattr__(forged, field, value)
    with pytest.raises(ValueError):
        arena.compile(forged, cell)
    assert runtime.ledger.snapshot() == before


def test_blank_termination_negative_growth_and_identity_channels() -> None:
    effect = primitive("identity")
    runtime, arena, kernel = setup(effect, (3, 3))
    quotient = arena.compile(kernel, runtime.cells.source(0, 1))
    value = observe(arena, quotient, 1, 0, 1)
    assert value["activity"] == value["extent"] == 0
    assert value["first_active"] == value["last_active"] == 2
    assert value["termination"] == 1
    assert (
        value["normalization"]
        == value["output"]
        == value["halo_left"]
        == value["halo_right"]
        == 3
    )
    assert value["frame"] == 1 and value["growth"] == 2  # Biased zero change.
    # Nontrivial kernel may create/erase activity depending on incoming ports.
    effect = primitive()
    runtime, arena, kernel = setup(effect, (3, 0))
    quotient = arena.compile(kernel, runtime.cells.source(0, 1))
    changes: set[int] = set()
    for a, b in product(range(2), repeat=2):
        growth = observe(arena, quotient, a, b, 0)["growth"]
        assert growth is not None
        changes.add(growth - 2)
    assert min(changes) < 0


def test_parent_binding_reservation_rolls_back_on_semantic_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, arena, kernel = setup(primitive(), (0, 1))
    for position in range(2):
        arena.compile(kernel, runtime.cells.source(position, 0))
    parent = runtime.cells.source(0, 1)
    before = runtime.ledger.snapshot()

    def poison(*args: object) -> Never:
        raise ValueError("synthetic parent construction failure")

    monkeypatch.setattr(PrimitiveMacroArena, "_parent", poison)
    with pytest.raises(ValueError, match="synthetic"):
        arena.compile(kernel, parent)
    after = runtime.ledger.snapshot()
    assert after.nodes == before.nodes and after.entries == before.entries
    assert len(arena.bindings) == 2
    assert all(item.accounting_delta == 0 for item in runtime.ledger.inventory())


def test_exhausted_budget_rejects_before_source_descent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    runtime, arena, kernel = setup(primitive(), (0, 1))
    cell = runtime.cells.source(0, 1)
    runtime.ledger.max_cache_entries = runtime.ledger.entries

    def poison(*args: object) -> Never:
        raise AssertionError("exhausted parent budget descended source")

    monkeypatch.setattr(type(runtime.cells), "split", poison)
    before = runtime.ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        arena.compile(kernel, cell)
    after = runtime.ledger.snapshot()
    assert after.entries == before.entries and after.nodes == before.nodes
    assert not arena.bindings


def test_image_and_foreign_family_certificate_are_not_primitive_source_adapters() -> (
    None
):
    runtime, arena, kernel = setup(primitive(), (0, 1))
    cell = runtime.cells.source(0, 1)
    action = runtime.actions.intern(runtime.actions.compiler.atom(primitive()))
    image = runtime.cells.image(action, cell)
    before = runtime.ledger.snapshot()
    with pytest.raises(ValueError):
        arena.compile(kernel, image)
    with pytest.raises(TypeError):
        arena.compile(cast("ActionProgramID", object()), cell)
    assert runtime.ledger.snapshot() == before


def test_complete_nonpower_boundary_admission_is_shared_by_every_channel() -> None:
    effect = primitive(left_count=3)
    runtime, arena, kernel = setup(effect, (0, 1))
    quotient = arena.compile(kernel, runtime.cells.source(0, 1))
    for left, right, position in product(range(3), range(2), range(2)):
        assert observe(arena, quotient, left, right, position) == oracle(
            effect, (0, 1), left, right, position
        )
    assert set(observe(arena, quotient, 3, 0, 0).values()) == {None}


def test_primitive_macro_uses_one_shared_scheduler_and_semantic_arena(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.interfaces.semantic_primitive_tasks import (
        PrimitiveMacroKey,
    )
    from number_compiler.hashlife.interfaces.semantic_structures import (
        DiamondQuotientID,
    )

    runtime, arena, kernel = setup(primitive(), (0, 1, 3, 0))
    active, calls = False, 0
    original = DiamondRuntime.execute

    def tracked(
        self: number_compiler.hashlife.execution.continuations.diamond_runtime.DiamondRuntime,
        task: number_compiler.hashlife.execution.continuations.diamond_tasks.Initial
        | number_compiler.hashlife.execution.continuations.diamond_tasks.Transfer
        | number_compiler.hashlife.execution.continuations.diamond_tasks.ResetTransfer
        | number_compiler.hashlife.execution.continuations.diamond_tasks.Substitute
        | number_compiler.hashlife.execution.continuations.diamond_tasks.Evaluate,
    ) -> (
        BoundaryStateID
        | TransferSummaryID
        | ExprID
        | StructureID
        | LocalInterfaceID
        | int
    ):
        nonlocal active, calls
        assert not active, "nested scheduler execution"
        active, calls = True, calls + 1
        try:
            return original(self, task)
        finally:
            active = False

    monkeypatch.setattr(DiamondRuntime, "execute", tracked)
    quotient = runtime.compile_primitive_macro(kernel, runtime.cells.source(0, 2))
    assert type(quotient) is DiamondQuotientID and calls == 1
    assert runtime.semantic_quotients is arena.quotients
    assert runtime.semantic_compiler.structures is arena.structures
    assert (
        runtime.execute(PrimitiveMacroKey(kernel, runtime.cells.source(0, 2)))
        == quotient
    )
    assert calls == 2
    assert runtime.ledger.counters["scheduler_transitions"] > len(arena.bindings)


def test_warm_complete_parent_precedes_laws_source_split_and_semantic_reductions(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, arena, kernel = setup(primitive(), (0, 1, 3, 0))
    source = runtime.cells.source(0, 2)
    quotient = runtime.compile_primitive_macro(kernel, source)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("warm complete parent replayed a dependency")

    monkeypatch.setattr(type(arena.primitives), "compile", forbidden)
    monkeypatch.setattr(type(runtime.cells), "split", forbidden)
    monkeypatch.setattr(type(runtime.cells), "source_symbol", forbidden)
    monkeypatch.setattr(type(arena.bits), "substitute", forbidden)
    assert runtime.compile_primitive_macro(kernel, source) == quotient


def test_scalar_observations_use_compiled_functions_for_unseen_ports_and_coordinates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    effect = primitive()
    word = (0, 1, 3, 0)
    runtime, arena, kernel = setup(effect, word)
    quotient = runtime.compile_primitive_macro(kernel, runtime.cells.source(0, 2))
    before = runtime.ledger.entries, runtime.ledger.nodes, len(arena.bindings)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("observation replayed a construction recipe")

    monkeypatch.setattr(type(arena.primitives), "compile", forbidden)
    monkeypatch.setattr(type(runtime.cells), "source_symbol", forbidden)
    monkeypatch.setattr(type(runtime.cells), "split", forbidden)
    monkeypatch.setattr(PrimitiveMacroArena, "_parent", forbidden)
    monkeypatch.setattr(type(arena.bits), "substitute", forbidden)
    for left, right, coordinate in product(range(2), range(2), range(4)):
        expected = oracle(effect, word, left, right, coordinate)
        for channel in COMPONENT_ROLES:
            assert (
                runtime.observe_primitive_macro(
                    quotient, channel, left=left, right=right, coordinate=coordinate
                )
                == expected[channel]
            )
    assert (runtime.ledger.entries, runtime.ledger.nodes, len(arena.bindings)) == before
    assert runtime.ledger.counters["primitive_macro_observation_evaluations"] == 208


def test_invalid_public_requests_leave_lazy_semantic_arenas_unallocated() -> None:
    effect, source = primitive(), (0, 1)
    ledger = ResourceLedger()
    geometry = SourceGeometry(
        ledger,
        ExactSource(
            source,
            effect.base,
            blank=effect.blank,
            extent=2,
            alphabet_size=effect.blank + 1,
        ),
    )
    geometry.span(source, effect.blank, 2)
    runtime = DiamondRuntime(LazyCompiler(ledger), geometry)
    kernel = runtime.kernels.intern(effect)
    own = runtime.cells.source(0, 1)
    other, _, foreign_kernel = setup(effect, source)
    foreign_cell = other.cells.source(0, 1)
    before = ledger.snapshot()
    for k, cell in ((foreign_kernel, own), (kernel, foreign_cell)):
        with pytest.raises(ValueError):
            runtime.compile_primitive_macro(k, cell)
    assert ledger.snapshot() == before
    assert runtime.semantic_compiler.structures is None
    assert runtime.semantic_quotients is None and runtime.primitive_macros is None
    quotient = runtime.compile_primitive_macro(kernel, own)
    assert runtime.semantic_quotients is not None
    assert runtime.semantic_compiler.structures is runtime.semantic_quotients.structures
    assert (
        runtime.observe_primitive_macro(quotient, left=0, right=0, coordinate=1)
        == oracle(effect, source, 0, 0, 1)["output"]
    )


def test_observation_foreign_handles_and_invalid_ports_reject_before_evaluation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, arena, kernel = setup(primitive(), (0, 1))
    quotient = runtime.compile_primitive_macro(kernel, runtime.cells.source(0, 1))
    other, _, foreign_kernel = setup(primitive(), (0, 1))
    foreign = other.compile_primitive_macro(foreign_kernel, other.cells.source(0, 1))

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("invalid observation evaluated a semantic function")

    monkeypatch.setattr(type(arena.bits), "evaluate", forbidden)
    before = runtime.ledger.snapshot()
    for q, channel, left, right, coordinate in (
        (foreign, "output", 0, 0, 0),
        (quotient, "unknown", 0, 0, 0),
        (quotient, "output", True, 0, 0),
        (quotient, "output", 0, -1, 0),
        (quotient, "output", 0, 0, 2),
    ):
        with pytest.raises(ValueError):
            runtime.observe_primitive_macro(
                q, channel, left=left, right=right, coordinate=coordinate
            )
    assert runtime.ledger.snapshot() == before


def test_wrong_or_foreign_quotient_publication_is_rejected_before_mutation() -> None:
    from number_compiler.hashlife.interfaces.semantic_primitive_tasks import (
        PrimitiveMacroKey,
    )

    runtime, _arena, kernel = setup(primitive(), (0, 1))
    cell = runtime.cells.source(0, 1)
    runtime.compile_primitive_macro(kernel, cell)
    other, _, foreign_kernel = setup(primitive(), (0, 1))
    foreign = other.compile_primitive_macro(foreign_kernel, other.cells.source(0, 1))
    before = runtime.ledger.snapshot()
    for result in (0, kernel, foreign):
        with pytest.raises(ValueError):
            runtime.publish_task(
                PrimitiveMacroKey(kernel, cell), cast(LocalInterfaceID, result)
            )
    assert runtime.ledger.snapshot() == before
