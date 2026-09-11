"""Transient exact construction is rejected below every point/lowering facade."""

import gc
import weakref
from collections.abc import Callable
from copy import copy
from typing import Never, cast

import pytest

from devtools.paths import repository_root
from devtools.proofs.spacetime_boundary import tile_uniform_symbol
from number_compiler.api.number_api import NumberCompiler, PoweredCollatzTermPayload
from number_compiler.arithmetic.contracts.exact_tree_context import (
    ExactTreeConstructionForbidden,
    OriginalSourceConstruction,
    endpoint_construction,
    source_reads_only,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaToken,
    ExactSource,
    LoweringCapability,
)
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.fields.dyadic_tile import (
    DyadicChunk,
    DyadicSpan,
    DyadicTile,
    join,
    leaf,
    mirror_tile,
    source_span,
    tile_arena_metrics,
    uniform,
)
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.projection.tile_radix import TileRadixObservation
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def _builders() -> tuple[Callable[[], object], ...]:
    original = leaf(7)
    parent = join(original, original)
    mirror_tile(parent)
    return (
        lambda: leaf(7),  # Warm exact interning is still construction authority.
        lambda: leaf(987654321),
        lambda: join(original, original),
        lambda: uniform(7, 1),
        lambda: mirror_tile(parent),
        lambda: DyadicTile(0, 0, 7),
        lambda: DyadicChunk(0, original),
        lambda: DyadicSpan(0, 0, ()),
        lambda: source_span((7,), blank=0, logical_length=1),
    )


def test_point_scope_rejects_all_low_level_exact_constructors_before_warm_lookup() -> (
    None
):
    @source_reads_only
    def query(build: Callable[[], object]) -> object:
        return build()

    builders = _builders()
    before = tile_arena_metrics()
    for build in builders:
        with pytest.raises(ExactTreeConstructionForbidden):
            query(build)
    after = tile_arena_metrics()
    assert after["intern_hits"] == before["intern_hits"]
    assert after["intern_misses"] == before["intern_misses"]
    # Leaving the failed query restores the original-input construction scope.
    assert leaf(7).symbol == 7


@pytest.mark.parametrize("family", ["reverse", "collatz"])
@pytest.mark.parametrize("observer", ["digit", "width"])
def test_public_point_and_width_reject_discarded_exact_future_tree(
    monkeypatch: pytest.MonkeyPatch,
    family: str,
    observer: str,
) -> None:
    term = (
        ReverseAddPoweredTerm(196, 4)
        if family == "reverse"
        else PoweredCollatzTerm(27, 4)
    )
    index = term._point_index()

    def eager_callback(*args: object) -> int:
        # Bypasses every endpoint-lowering API, and would discard its output.
        source_span((1, 0, 1), blank=0, logical_length=3)
        return 1

    method = "point" if observer == "digit" else "active_width"
    monkeypatch.setattr(type(index._lazy_application), method, eager_callback)
    with pytest.raises(ExactTreeConstructionForbidden):
        if observer == "digit":
            term.digit(0)
        else:
            term.width()


@pytest.mark.parametrize("radix", [2, 3, 6, 12])
def test_public_radix_queries_reject_transient_construction_in_callback(
    monkeypatch: pytest.MonkeyPatch,
    radix: int,
) -> None:
    result = NumberCompiler().project_nth("collatz", 4, seed=27, radix=radix)
    assert isinstance(result.payload, PoweredCollatzTermPayload)
    term = result.payload.term
    index = term._point_index()

    def eager_callback(*args: object) -> int:
        DyadicSpan(0, 0, ())
        return 1

    if radix == 2:
        monkeypatch.setattr(type(index._lazy_application), "point", eager_callback)
    else:
        monkeypatch.setattr(
            TileRadixObservation,
            "_application",
            eager_callback,
        )
    with pytest.raises(ExactTreeConstructionForbidden):
        result.digit(0)


@pytest.mark.parametrize("method", ("point", "width", "interface"))
def test_direct_tile_application_guards_active_callbacks(
    monkeypatch: pytest.MonkeyPatch,
    method: str,
) -> None:
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine

    projection = PoweredCollatzTerm(27, 4)._point_index()._lazy_application
    assert type(projection) is LazyProjection
    application = projection._open()

    def eager_callback(*args: object, **kwargs: object) -> int:
        DyadicSpan(0, 0, ())
        return 1

    if method == "interface":
        monkeypatch.setattr(CausalTileEngine, "interface", eager_callback)
    else:
        monkeypatch.setattr(type(application.scheduler), method, eager_callback)
    calls: dict[str, Callable[[], object]] = {
        "point": lambda: application.point(0),
        "width": application.width,
        "interface": application.interface,
    }
    with pytest.raises(ExactTreeConstructionForbidden):
        calls[method]()


@pytest.mark.parametrize("method", ("source", "point", "width", "interface"))
def test_copied_tile_application_rejects_before_scheduler_work(
    monkeypatch: pytest.MonkeyPatch, method: str
) -> None:
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine

    projection = PoweredCollatzTerm(27, 4)._point_index()._lazy_application
    assert type(projection) is LazyProjection
    application = projection._open()
    forged = copy(application)

    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("forged application reached scheduler execution")

    monkeypatch.setattr(type(application.scheduler), "point", forbidden)
    monkeypatch.setattr(type(application.scheduler), "width", forbidden)
    monkeypatch.setattr(CausalTileEngine, "interface", forbidden)
    before = projection.ledger.snapshot()
    calls: dict[str, Callable[[], object]] = {
        "source": lambda: forged.source,
        "point": lambda: forged.point(0),
        "width": forged.width,
        "interface": forged.interface,
    }
    with pytest.raises(ValueError, match="issued"):
        calls[method]()
    assert projection.ledger.snapshot() == before


def test_direct_radix_observation_guards_active_callback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    projection = PoweredCollatzTerm(27, 4)._point_index()._lazy_application
    assert type(projection) is LazyProjection
    observation = TileRadixObservation(projection, 3)

    def eager_callback(*args: object, **kwargs: object) -> int:
        DyadicSpan(0, 0, ())
        return 1

    monkeypatch.setattr(type(observation), "_application", eager_callback)
    with pytest.raises(ExactTreeConstructionForbidden):
        observation.digit(0)


def test_zero_and_exterior_paths_reject_argument_coercion_before_work() -> None:
    class PoisonPosition:
        def __int__(self) -> Never:
            raise AssertionError("point input validation invoked arbitrary coercion")

    for term in (ReverseAddPoweredTerm(196, 0), PoweredCollatzTerm(27, 0)):
        with pytest.raises(TypeError, match="must be an integer"):
            term.digit(cast("int", PoisonPosition()))
        with pytest.raises(IndexError):
            term.digit(-1)


def test_original_source_authority_validates_payload_and_cannot_leak_into_queries() -> (
    None
):
    original = ExactSource((1, 2), 10, blank=10, extent=8)
    geometry = SourceGeometry(ResourceLedger(), original)

    @source_reads_only
    def source_query() -> DyadicSpan:
        return geometry.span(original.digits, original.blank, 8)

    assert source_query().length == 8
    with pytest.raises(ValueError, match="authorized original source"):
        geometry.span((2, 1), 10, 8)
    with pytest.raises(ValueError, match="authorized original source"):
        geometry.span((1, 2), 10, 9)
    with OriginalSourceConstruction(original).allow(original.digits, original.blank, 8):
        with pytest.raises(ExactTreeConstructionForbidden):
            source_reads_only(lambda: leaf(1))()


def test_endpoint_capability_cannot_override_a_point_scope() -> None:
    owner = ArenaToken("explicit-output")
    capability = LoweringCapability(owner)

    @source_reads_only
    def disguised_lowering() -> None:
        with endpoint_construction(owner, capability):
            source_span((1, 2), blank=0, logical_length=2)

    with pytest.raises(ExactTreeConstructionForbidden):
        disguised_lowering()
    with pytest.raises(ValueError, match="capability"):
        with endpoint_construction(ArenaToken("foreign"), capability):
            pass


def test_explicit_endpoint_and_uniform_observer_do_not_pin_global_exact_trees() -> None:
    owner = ArenaToken("explicit-output")
    capability = LoweringCapability(owner)
    with endpoint_construction(owner, capability):
        endpoint = source_span(
            (819273641, 819273642, 819273643, 819273644), blank=0, logical_length=4
        )
    root = endpoint.chunks[0].tile
    assert tile_uniform_symbol(root) is None
    saved_root = weakref.ref(root)
    saved_children = (weakref.ref(root.left), weakref.ref(root.right))
    old_id = root.node_id
    del root, endpoint
    gc.collect()
    assert saved_root() is None
    assert all(saved() is None for saved in saved_children)
    with endpoint_construction(owner, capability):
        rebuilt = source_span(
            (819273641, 819273642, 819273643, 819273644), blank=0, logical_length=4
        )
    assert rebuilt.chunks[0].tile.node_id > old_id


def test_point_callback_cannot_relabel_future_digits_as_a_new_original_source() -> None:
    @source_reads_only
    def relabel() -> None:
        OriginalSourceConstruction(ExactSource((1, 0, 1), 2))

    with pytest.raises(ExactTreeConstructionForbidden, match="mint original-source"):
        relabel()


def test_public_explicit_lowering_releases_exact_global_arena_in_fresh_process() -> (
    None
):
    import os
    import subprocess
    import sys

    root = repository_root()
    script = """
import gc
from number_compiler import ReverseAddPoweredTerm
from number_compiler.arithmetic.fields.dyadic_tile import tile_arena_metrics
assert tile_arena_metrics()['canonical_nodes'] == 0
term = ReverseAddPoweredTerm(196, 16)
output = term.digits()
assert output and tile_arena_metrics()['canonical_nodes'] > 0
del output, term
gc.collect()
assert tile_arena_metrics()['canonical_nodes'] == 0
"""
    result = subprocess.run(
        [sys.executable, "-c", script],
        cwd=root,
        env=dict(os.environ),
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_direct_lowering_capability_and_endpoint_constructors_reject_point_scope() -> (
    None
):
    from number_compiler.arithmetic.contracts.scoped_handles import (
        ActionProgramID,
        ArenaHandle,
        LazyFieldRef,
        MaterializedEndpoint,
    )

    owner = ArenaToken("endpoint")
    capability = LoweringCapability(owner)
    field = LazyFieldRef(
        ArenaHandle(owner, "source", 0), ActionProgramID(owner, "program", 0)
    )
    with pytest.raises(ExactTreeConstructionForbidden):
        source_reads_only(lambda: LoweringCapability(owner))()
    with pytest.raises(ExactTreeConstructionForbidden):
        source_reads_only(
            lambda: MaterializedEndpoint(field, (1, 0, 1), 2, capability)
        )()


def test_private_source_allocator_rejects_before_reserving_without_source_scope() -> (
    None
):
    ledger = ResourceLedger()
    geometry = SourceGeometry(ledger, ExactSource((1,), 2, blank=2, extent=4))
    before = ledger.snapshot()
    with pytest.raises(ExactTreeConstructionForbidden):
        source_reads_only(lambda: geometry._leaf(1))()
    assert ledger.snapshot() == before
