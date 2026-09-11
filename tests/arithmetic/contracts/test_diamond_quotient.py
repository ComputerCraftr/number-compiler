"""Publication tests distinguish complete semantic results from recipes."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING, Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ExactSource,
)
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.actions.diamond_actions import (
    ImageCellArena,
    TemporalActionArena,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.interfaces.diamond_quotient import (
    COMPONENT_ROLES,
    DiamondKey,
    DiamondQuotientArena,
    DiamondQuotientID,
    LocalInterfaceID,
    MacroComponents,
    MacroInterface,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.ownership import audit_execution_ownership

if TYPE_CHECKING:
    from number_compiler.arithmetic.functions.finite_function_types import (
        FinitePort,
        SemanticFunctionID,
    )
    from number_compiler.arithmetic.functions.semantic_functions import (
        SemanticFunctionArena,
    )
    from number_compiler.hashlife.actions.diamond_actions import (
        ImageCellArena,
        PortSignatureID,
    )
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondQuotientArena,
        MacroComponents,
    )
    from number_compiler.resources.ledger import ResourceLedger


def setup_arena() -> tuple[
    ResourceLedger,
    SemanticFunctionArena,
    DiamondQuotientArena,
    ImageCellArena,
    FinitePort,
    PortSignatureID,
    MacroComponents,
    SemanticFunctionID,
    SemanticFunctionID,
    SemanticFunctionID,
]:
    ledger = ResourceLedger()
    functions = SemanticFunctionArena(ledger)
    source = SourceGeometry(ledger, ExactSource((1, 0), 2, blank=2, extent=2))
    source.span((1, 0), 2, 2)
    cells = ImageCellArena(TemporalActionArena(LazyCompiler(ledger)), source)
    arena = DiamondQuotientArena(functions, cells)
    port = FinitePort(PortVariable(0, 0, "carry", 0), 2)
    inputs = (port,)
    signature = FunctionSignature(inputs, BOOL)
    zero, one = functions.atom(signature, 0), functions.atom(signature, 1)
    variable = functions.variable(inputs, port, BOOL)
    interface = MacroInterface(
        SemanticIdentity("test-v1", ("complete-test-kernel",)),
        inputs,
        (BOOL,) * len(COMPONENT_ROLES),
        one,
    )
    declared = arena.intern_interface(interface)
    components = MacroComponents(*(zero for _ in COMPONENT_ROLES))
    return (
        ledger,
        functions,
        arena,
        cells,
        port,
        declared,
        components,
        zero,
        one,
        variable,
    )


def forbidden(*args: object, **kwargs: object) -> Never:
    raise AssertionError("warm parent lookup replayed its construction")


def test_complete_macro_name_is_the_same_scoped_semantic_type() -> None:
    assert DiamondQuotientID is LocalInterfaceID


def test_already_masked_atoms_publish_without_another_decision_rewrite(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _, arena, _, port, signature, components, _, _, _ = setup_arena()
    bit = arena.structures.bits.constant(FunctionSignature((port,), BOOL), 0)
    atom = arena.structures.atom(bit)
    atoms = MacroComponents(*(atom for _ in COMPONENT_ROLES))
    # The independent existing normalization route has the same normal form.
    assert arena.normalize(signature, components) == atoms
    monkeypatch.setattr(arena, "_prepare_normalization", forbidden)
    result = arena.intern(signature, atoms)
    assert arena.resolve(result).components == atoms
    assert arena.normalize(signature, atoms) == atoms
    assert ledger.counters["quotient_atomic_mask_elisions"] == 2


def test_atomic_shortcut_does_not_erase_a_different_validity_domain() -> None:
    from number_compiler.hashlife.interfaces.atomic_quotient_normalization import (
        atomic_product_is_masked,
    )

    _, _, arena, _, port, signature, _, _, _, variable = setup_arena()
    bit = arena.structures.bits.constant(FunctionSignature((port,), BOOL), 0)
    atom = arena.structures.atom(bit)
    atoms = MacroComponents(*(atom for _ in COMPONENT_ROLES))
    interface = replace(arena.interface(signature), admissible=variable)
    restricted = arena.intern_interface(interface)
    assert not atomic_product_is_masked(arena, interface, atoms)
    normalized = arena.normalize(restricted, atoms)
    assert normalized != atoms
    assert arena.normalize(restricted, normalized) == normalized


def test_equal_semantics_from_different_derivations_share_complete_quotient() -> None:
    _, functions, arena, _, _, signature, components, zero, one, variable = (
        setup_arena()
    )
    complement = functions.ite(variable, zero, one)
    alias = functions.ite(complement, zero, one)
    left = arena.intern(signature, replace(components, output=variable))
    right = arena.intern(signature, replace(components, output=alias))
    assert variable == alias
    assert left == right


def test_equal_boundary_exits_cannot_merge_different_output_semantics() -> None:
    _, _, arena, _, _, signature, components, _, one, variable = setup_arena()
    a = arena.intern(signature, replace(components, output=one))
    b = arena.intern(signature, replace(components, output=variable))
    assert (
        arena.resolve(a).components.boundary_left
        == arena.resolve(b).components.boundary_left
    )
    assert a != b


@pytest.mark.parametrize("role", COMPONENT_ROLES)
def test_every_complete_semantic_component_participates_in_identity(role: str) -> None:
    _, _, arena, _, _, signature, components, _, one, _ = setup_arena()
    original = arena.intern(signature, components)
    changed = arena.intern(
        signature,
        MacroComponents(
            *(
                one if name == role else value
                for name, value in zip(
                    COMPONENT_ROLES, components.functions(), strict=True
                )
            )
        ),
    )
    assert changed != original


def test_inadmissible_boundary_assignments_do_not_split_equivalence() -> None:
    _, functions, arena, _, _, signature, components, zero, one, variable = (
        setup_arena()
    )
    allowed = functions.ite(variable, zero, one)
    restricted = arena.intern_interface(
        replace(arena.interface(signature), admissible=allowed)
    )
    assert arena.intern(restricted, components) == arena.intern(
        restricted, replace(components, output=variable)
    )


def test_pre_normalized_alias_memo_skips_repeat_reduction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, functions, arena, _, _, signature, components, zero, one, variable = (
        setup_arena()
    )
    allowed = functions.ite(variable, zero, one)
    restricted = arena.intern_interface(
        replace(arena.interface(signature), admissible=allowed)
    )
    alias = replace(components, output=variable)
    canonical = arena.intern(restricted, components)
    assert arena.intern(restricted, alias) == canonical
    before = ledger.snapshot()
    monkeypatch.setattr(arena, "_prepare_normalization", forbidden)
    assert arena.intern(restricted, alias) == canonical
    assert (ledger.entries, ledger.nodes) == (before.entries, before.nodes)
    assert ledger.counters["quotient_normalization_memo_hits"] == 1


def test_normalization_memo_eviction_preserves_semantic_identity() -> None:
    ledger, functions, arena, _, _, signature, components, zero, one, variable = (
        setup_arena()
    )
    allowed = functions.ite(variable, zero, one)
    restricted = arena.intern_interface(
        replace(arena.interface(signature), admissible=allowed)
    )
    alias = replace(components, output=variable)
    quotient = arena.intern(restricted, alias)
    evicted = ledger.evict_query_memos()
    assert evicted
    assert arena.intern(restricted, alias) == quotient
    assert not audit_execution_ownership(ledger).violations


def test_normalization_alias_reservation_is_atomic() -> None:
    ledger, functions, arena, _, _, signature, components, zero, one, variable = (
        setup_arena()
    )
    allowed = functions.ite(variable, zero, one)
    restricted = arena.intern_interface(
        replace(arena.interface(signature), admissible=allowed)
    )
    canonical = arena.intern(restricted, components)
    alias = replace(components, output=variable)
    ledger.tighten_limits(None, ledger.entries)
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        arena.intern(restricted, alias)
    assert (ledger.entries, ledger.nodes) == (before.entries, before.nodes)
    assert arena.resolve(canonical).signature == restricted


def test_parent_hit_skips_semantic_reduction_and_descendant_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, functions, arena, cells, _, signature, components, _, _, _ = setup_arena()
    quotient = arena.intern(signature, components)
    cell = cells.source_span(0, 2)[0][1]
    request = DiamondKey(quotient, quotient, cell, 1, 0, 0, signature)
    assert arena.probe(request) is None
    arena.publish(request, quotient)
    monkeypatch.setattr(functions, "ite", forbidden)
    monkeypatch.setattr(functions, "evaluate", forbidden)
    monkeypatch.setattr(arena, "normalize", forbidden)
    monkeypatch.setattr(cells, "split", forbidden)
    monkeypatch.setattr(cells, "source_symbol", forbidden)
    assert arena.probe(request) == quotient
    assert ledger.counters["quotient_parent_early_hits"] == 1


def test_canonical_component_hit_skips_normalization_before_a_new_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _, arena, cells, _, signature, components, _, _, _ = setup_arena()
    quotient = arena.intern(signature, components)
    canonical = arena.resolve(quotient).components
    cell = cells.source_span(0, 2)[0][1]
    request = DiamondKey(quotient, quotient, cell, 1, 0, 0, signature)
    before = ledger.snapshot()
    monkeypatch.setattr(arena, "_prepare_normalization", forbidden)
    assert arena.intern(signature, canonical) == quotient
    assert arena.normalize_and_publish(request, canonical) == quotient
    assert ledger.entries == before.entries + 1  # Only the new parent binding.
    assert ledger.nodes == before.nodes
    assert ledger.counters["quotient_normal_form_early_hits"] == 2


@pytest.mark.parametrize(
    "field,value",
    (("local_id", True), ("local_id", 0.0), ("kind", "semantic-function")),
)
def test_component_early_hit_validates_all_handles_before_lookup(
    field: str, value: bool | float | str
) -> None:
    ledger, _, arena, _, _, signature, components, _, _, _ = setup_arena()
    quotient = arena.intern(signature, components)
    canonical = arena.resolve(quotient).components
    original = canonical.output
    forged = object.__new__(type(original))
    for name in ("owner", "kind", "local_id"):
        object.__setattr__(
            forged, name, value if field == name else getattr(original, name)
        )
    before = ledger.snapshot()
    with pytest.raises(ValueError):
        arena.intern(signature, replace(canonical, output=forged))
    assert ledger.snapshot() == before


def test_only_complete_result_handles_can_enter_parent_cache() -> None:
    ledger, functions, arena, cells, _, signature, components, zero, _, _ = (
        setup_arena()
    )
    quotient = arena.intern(signature, components)
    cell = cells.source_span(0, 2)[0][1]
    request = DiamondKey(quotient, quotient, cell, 1, 0, 0, signature)
    invalid = (
        zero,
        ActionProgramID(quotient.owner, "diamond-quotient", quotient.local_id),
    )
    for value in invalid:
        before = ledger.snapshot()
        with pytest.raises((TypeError, ValueError)):
            arena.publish(request, cast("LocalInterfaceID", value))
        assert ledger.snapshot() == before
        assert not arena.parents
    other = SemanticFunctionArena(ledger)
    foreign = other.atom(functions.signature(zero), 0)
    before = ledger.snapshot()
    with pytest.raises((TypeError, ValueError)):
        arena.normalize_and_publish(request, replace(components, output=foreign))
    assert ledger.snapshot() == before


@pytest.mark.parametrize("warm", (False, True))
@pytest.mark.parametrize("alias", (True, 0.0, -1))
def test_forged_quotient_ids_reject_before_cold_and_warm_lookup(
    warm: bool, alias: bool | float | int
) -> None:
    ledger, _, arena, cells, _, signature, components, _, _, _ = setup_arena()
    quotient = arena.intern(signature, components)
    cell = cells.source_span(0, 2)[0][1]
    request = DiamondKey(quotient, quotient, cell, 1, 0, 0, signature)
    if warm:
        arena.publish(request, quotient)
    forged = DiamondQuotientID(quotient.owner, quotient.kind, quotient.local_id)
    object.__setattr__(forged, "local_id", alias)
    before = ledger.snapshot()
    with pytest.raises((TypeError, ValueError)):
        arena.probe(replace(request, before=forged))
    assert ledger.snapshot() == before


def test_eviction_preserves_canonical_quotients_and_reconciles_ownership() -> None:
    ledger, _, arena, cells, _, signature, components, _, _, _ = setup_arena()
    quotient = arena.intern(signature, components)
    cell = cells.source_span(0, 2)[0][1]
    request = DiamondKey(quotient, quotient, cell, 1, 0, 0, signature)
    arena.publish(request, quotient)
    entries = ledger.entries
    arena.clear_bindings()
    assert ledger.entries == entries - 1
    assert not arena.parents
    assert arena.intern(signature, components) == quotient
    assert not audit_execution_ownership(ledger).violations
    assert all(row.accounting_delta == 0 for row in ledger.inventory())


def test_atomic_parent_publication_rejects_exhausted_budget_without_mutation() -> None:
    ledger, _, arena, cells, _, signature, components, _, _, _ = setup_arena()
    quotient = arena.intern(signature, components)
    cell = cells.source_span(0, 2)[0][1]
    request = DiamondKey(quotient, quotient, cell, 1, 0, 0, signature)
    ledger.tighten_limits(None, ledger.entries)
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        arena.publish(request, quotient)
    counters = dict(before.counters)
    counters["quotient_publication_failures"] = (
        counters.get("quotient_publication_failures", 0) + 1
    )
    assert ledger.snapshot() == replace(before, counters=counters)
    assert not arena.parents
