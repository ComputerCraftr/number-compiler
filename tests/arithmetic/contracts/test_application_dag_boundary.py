"""Early root identity, bounded response reuse, and source DAG execution."""

from __future__ import annotations

from typing import TYPE_CHECKING, Never, TypedDict

import pytest

from devtools.proofs.carry_interval_effects import CarryActionQuotientArena
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.arithmetic.fields.dyadic_tile import DyadicTile
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.lazy_compiler import (
    CompilerCompositionKey,
    LazyCompiler,
    ProgramComposition,
)
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.projection.point_response import PointResponseRegister
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

if TYPE_CHECKING:
    from number_compiler.arithmetic.fields.dyadic_tile import DyadicTile


class _IndexLimits(TypedDict, total=False):
    max_cache_entries: int
    max_tile_nodes: int


def test_compiler_parent_keys_use_admitted_canonical_children_before_construction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    compiler = LazyCompiler(ResourceLedger())
    first = compiler.compose(BaseBlockEffect(10), BaseBlockEffect(10))
    assert isinstance(first, ProgramComposition)
    keys = [key for key in compiler.ids if isinstance(key, CompilerCompositionKey)]
    assert len(keys) == 1
    assert keys[0].first == keys[0].second
    assert compiler.resolve(keys[0].first) is first.first

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("duplicate parent construction")

    monkeypatch.setattr(ProgramComposition, "__init__", forbidden)
    assert compiler.compose(BaseBlockEffect(10), BaseBlockEffect(10)) is first


def test_compiler_rejected_parent_cannot_publish_new_children() -> None:
    ledger = ResourceLedger(max_cache_entries=3)
    compiler = LazyCompiler(ledger)
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        compiler.compose(BaseBlockEffect(10), BaseBlockEffect(10))
    after = ledger.snapshot()
    assert after.inventory == before.inventory
    assert after.entries == after.nodes == 0
    assert not compiler.nodes and not compiler.ids


def test_warm_reverse_point_bypasses_projection_and_retains_one_response(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = ReverseAddPoweredTerm(196, 2)
    expected = term.digit(0)
    workspace = term._source_workspace()
    core = workspace.scheduler._source_image_core()
    assert len(core._projections) == 1
    before = dict(term._ledger.counters)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("warm point replayed the source-image projection")

    monkeypatch.setattr(type(workspace.adapter), "project", forbidden)
    assert term.digit(0) == expected
    changes = {
        key: value - before.get(key, 0)
        for key, value in term._ledger.counters.items()
        if value != before.get(key, 0)
    }
    assert changes == {
        "source_image_seal_validation_visits": 18,
        "source_image_projection_hits": 1,
    }
    assert len(core._projections) == 1


def test_warm_collatz_point_bypasses_projection_and_retains_one_response(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = PoweredCollatzTerm(27, 32)
    expected = term.digit(0)
    workspace = term._source_image()
    assert len(term._microblocks.blocks) == 1
    before = dict(term._ledger.counters)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("warm point replayed the source-image projection")

    monkeypatch.setattr(PoweredCollatzTerm, "radix_digit", forbidden)
    assert term.digit(0) == expected
    changes = {
        key: value - before.get(key, 0)
        for key, value in term._ledger.counters.items()
        if value != before.get(key, 0)
    }
    assert changes == {
        "direct_powered_point_queries": 1,
        "microblock_requests": 1,
        "microblock_hits": 1,
    }
    assert len(term._microblocks.blocks) == 1
    view = workspace.scheduler._source_image_core().view(workspace.root_image)
    assert view.payload == workspace.root_payload


def test_response_register_never_becomes_an_output_tape_and_eviction_releases_charge() -> (
    None
):
    compiler = LazyCompiler(ResourceLedger())
    effect = compiler.atom(DigitNormalizeBlockEffect(10))
    register = PointResponseRegister(compiler)
    handle = compiler.reference(effect)
    for position in range(257):
        assert register.query(handle, position, lambda p: p % 10) == position % 10
        assert len(register._value) == 1
    owner = next(
        item for item in compiler.ledger.inventory() if item.owner == register.owner
    )
    assert owner.entries == owner.nodes == 1
    compiler.ledger.evict_query_memos()
    assert not register._value
    owner = next(
        item for item in compiler.ledger.inventory() if item.owner == register.owner
    )
    assert owner.entries == owner.nodes == 0


def test_response_register_validates_foreign_handle_before_warm_lookup() -> None:
    compiler = LazyCompiler(ResourceLedger())
    effect = compiler.atom(DigitNormalizeBlockEffect(10))
    register = PointResponseRegister(compiler)
    handle = compiler.reference(effect)
    register.query(handle, 0, lambda _: 2)
    before = compiler.ledger.snapshot()
    foreign = ActionProgramID(
        ArenaToken("operator-compiler"), handle.kind, handle.local_id
    )
    with pytest.raises(ValueError):
        register.query(foreign, 0, lambda _: 9)
    assert compiler.ledger.snapshot() == before


def test_response_budget_rejects_before_evaluation_and_failed_evaluation_releases() -> (
    None
):
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    effect = compiler.atom(DigitNormalizeBlockEffect(10))
    register = PointResponseRegister(compiler)
    handle = compiler.reference(effect)
    ledger.max_cache_entries = ledger.entries

    def forbidden(_: object) -> Never:
        raise AssertionError("evaluation happened before budget rejection")

    with pytest.raises(BlockContextBudgetExceeded):
        register.query(handle, 0, forbidden)
    ledger.max_cache_entries = None
    entries, nodes = ledger.entries, ledger.nodes
    with pytest.raises(AssertionError):
        register.query(handle, 0, forbidden)
    assert ledger.entries == entries and ledger.nodes == nodes
    assert not register._value


def test_explicit_projection_uses_its_registered_source_geometry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    index = HashLifeBlockIndex(
        DigitNormalizeBlockEffect(10),
        (2, 4, 2),
        logical_length=8,
    )
    reads = []
    original = index._source_geometry.tile_at

    def counted(position: int, level: int) -> DyadicTile | None:
        reads.append((position, level))
        return original(position, level)

    monkeypatch.setattr(index._source_geometry, "tile_at", counted)
    index.direct_powered_point(0)
    assert not reads
    assert index._ledger.counters.get("source_tile_lookup_requests", 0) >= len(reads)


def test_source_image_families_use_their_registered_source_authority() -> None:
    reverse = ReverseAddPoweredTerm(196, 2)
    assert reverse.digit(0) == 5
    reverse_workspace = reverse._source_workspace()
    reverse_image = reverse_workspace._image
    assert reverse_image is not None
    reverse_view = reverse_workspace.scheduler._source_image_core().view(reverse_image)
    assert reverse_view.binding.source == reverse_workspace.source
    assert reverse_view.binding.action == reverse_workspace.root_action

    collatz = PoweredCollatzTerm(27, 8)
    assert collatz.digit(0) == 0
    collatz_workspace = collatz._source_image()
    collatz_view = collatz_workspace.scheduler._source_image_core().view(
        collatz_workspace.root_image
    )
    assert collatz_view.binding.source == collatz_workspace.root_source
    assert collatz_view.binding.action == collatz_workspace.root_action
    assert collatz_view.payload == collatz_workspace.root_payload


def test_boundary_effect_alias_does_not_establish_output_complete_temporal_equivalence() -> (
    None
):
    arena = CarryActionQuotientArena()
    port = PortVariable(0, 0, "carry", 0)
    assert arena.interval_word((2, 2), base=10, port=port) == arena.interval_word(
        (4, 4), base=10, port=port
    )
    # Equal complete carry boundary functions still emit different digits and
    # have different next pair fields. They cannot key an entire temporal jump.
    assert ReverseAddPoweredTerm(11, 2).digit(0) == 4
    assert ReverseAddPoweredTerm(22, 2).digit(0) == 8


def test_generic_equal_source_parent_uses_tile_identity_before_cell_walk(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.observation.tile_projection import LazyProjection

    index = HashLifeBlockIndex(
        DigitNormalizeBlockEffect(10), (2,) * 32, logical_length=32
    )
    assert index.direct_powered_point(15) == 2
    projection = index._lazy_application
    assert type(projection) is LazyProjection
    engine = projection.scheduler
    parent = engine.tiles.resolve(projection._application.source)
    assert parent.left == parent.right

    def guarded(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError(
            "equal source subtree was evaluated before its canonical lookup"
        )

    monkeypatch.setattr(engine.adapter, "_leaf_components", guarded)
    monkeypatch.setattr(engine.adapter, "_parent_components", guarded)
    assert index.direct_powered_point(31) == 2
    assert index._ledger.counters["powered_interface_early_hits"] > 0


def test_certificate_issuer_checks_actual_kernel_language() -> None:
    from number_compiler.arithmetic.contracts.temporal_family import _issue_certificate
    from tests.arithmetic.contracts.test_lazy_generic import finite

    compiler = LazyCompiler(ResourceLedger())
    identity = compiler.atom(finite())
    terminal = compiler.atom(DigitNormalizeBlockEffect(10))
    impostor = compiler.compose(identity, terminal)
    with pytest.raises(ValueError, match="certified arithmetic"):
        _issue_certificate(impostor, "reverse-add", 1)
    reversed_order = compiler.compose(terminal, BaseBlockEffect(10))
    with pytest.raises(ValueError, match="normalization must follow"):
        _issue_certificate(reversed_order, "reverse-add", 1)
    doubled_terminal = compiler.compose(terminal, terminal)
    with pytest.raises(ValueError, match="declared semantics"):
        _issue_certificate(doubled_terminal, "reverse-add", 0)


def test_source_geometry_rejects_another_input_before_application_retention() -> None:
    index = HashLifeBlockIndex(DigitNormalizeBlockEffect(10), (2, 2), logical_length=8)
    before = index._ledger.snapshot()
    with pytest.raises(ValueError, match="original input"):
        index._source_geometry.require_source((4, 4), index.effect.blank)
    assert index._ledger.snapshot() == before


def test_import_admits_entire_dag_before_publishing_siblings() -> None:
    from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError

    class Impostor(BaseBlockEffect):
        pass

    compiler = LazyCompiler(ResourceLedger())
    handle = ActionProgramID(ArenaToken(), "action-program", 0)
    bad = ProgramComposition(BaseBlockEffect(10), Impostor(10), handle)
    before = compiler.ledger.snapshot()
    with pytest.raises(UnsupportedInterfaceError):
        compiler.import_effect(bad)
    assert compiler.ledger.snapshot() == before
    object.__setattr__(bad, "second", bad)
    with pytest.raises(UnsupportedInterfaceError, match="cyclic"):
        compiler.import_effect(bad)
    assert compiler.ledger.snapshot() == before


def test_certificate_rejects_mixed_alphabets() -> None:
    from number_compiler.arithmetic.contracts.temporal_family import _issue_certificate

    handle = ActionProgramID(ArenaToken(), "action-program", 0)
    bad = ProgramComposition(BaseBlockEffect(10), DigitNormalizeBlockEffect(2), handle)
    with pytest.raises(ValueError, match="mixed alphabets"):
        _issue_certificate(bad, "reverse-add", 1)


@pytest.mark.parametrize("limit", ({"max_cache_entries": 0}, {"max_tile_nodes": 0}))
def test_explicit_index_limits_cannot_be_ignored_by_an_external_ledger(
    limit: _IndexLimits,
) -> None:
    ledger = ResourceLedger()
    with pytest.raises(BlockContextBudgetExceeded):
        HashLifeBlockIndex(
            DigitNormalizeBlockEffect(10),
            (2,),
            logical_length=4,
            ledger=ledger,
            **limit,
        )
    assert ledger.entries == ledger.nodes == 0


def test_failed_limit_tightening_does_not_mutate_existing_limits_or_inventory() -> None:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    compiler.atom(BaseBlockEffect(10))
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        ledger.tighten_limits(0, 0)
    assert ledger.snapshot() == before
    assert ledger.max_nodes is ledger.max_cache_entries is None


def test_preexisting_source_authority_cannot_lend_an_unrestricted_point_scope() -> None:
    from number_compiler.arithmetic.contracts.exact_tree_context import (
        ExactTreeConstructionForbidden,
        OriginalSourceConstruction,
        source_reads_only,
    )
    from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
    from number_compiler.arithmetic.fields.dyadic_tile import leaf

    authority = OriginalSourceConstruction(ExactSource((1,), 10))

    @source_reads_only
    def disguised_future() -> DyadicTile:
        with authority.allow(authority.source.digits, authority.source.blank, 1):
            return leaf(9)

    with pytest.raises(ExactTreeConstructionForbidden, match="unrestricted"):
        disguised_future()


def test_invalid_generic_source_rejects_before_ledger_mutation() -> None:
    ledger = ResourceLedger()
    before = ledger.snapshot()
    with pytest.raises(ValueError):
        HashLifeBlockIndex(
            DigitNormalizeBlockEffect(10),
            (-1,),
            logical_length=1,
            ledger=ledger,
        )
    assert ledger.snapshot() == before
