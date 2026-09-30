from __future__ import annotations

from dataclasses import replace
from typing import cast

import pytest

from devtools.experiments.reverse_add.coordinate_program import (
    ReverseCoordinateProgramArena,
)
from devtools.experiments.reverse_add.field_action import (
    ProofMachineStateID,
    ReverseActionAutomorphisms,
    ReverseFieldActionArena,
    ReverseGeometry,
)
from devtools.experiments.reverse_add.local_interface import (
    ReverseLocalInterfaceArena,
)
from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.arithmetic.carry.carry_monoid import CarryFn, compose_carry_fn
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaToken,
)
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
)
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID as RuntimeCoordinateOutputMorphismID,
)
from number_compiler.hashlife.actions.field_actions import (
    FieldCellActionID as RuntimeFieldCellActionID,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.compilation import compile_reverse_pair_power
from number_compiler.sequences.reverse_add.powered_local_codec import (
    ReversePoweredLocalCodec,
)
from tests.support.assertions import assert_associative
from tests.support.reverse_field_action import (
    _arena,
    _atom,
    _concatenate,
    _source_cells,
)


def test_reverse_actions_use_shared_runtime_handle_sorts() -> None:
    arena = _arena()
    record = arena.resolve(arena.identity)
    assert type(arena.identity) is RuntimeFieldCellActionID
    assert type(record.output) is RuntimeCoordinateOutputMorphismID
    assert arena.action_kind == "field-cell-action"
    assert arena.output_owner is arena.owner
    assert arena.output_kind == "coordinate-output-morphism"
    arena.validate_action(arena.identity)
    arena.validate_output(record.output)
    assert arena.output_semantics(record.output) == ""


def test_coordinate_program_actions_reject_uncertified_port_automorphisms() -> None:
    ledger = ResourceLedger()
    programs = ReverseCoordinateProgramArena(10, ledger)
    arena = ReverseFieldActionArena(
        base=10,
        order=8,
        residual_identity="identity",
        output_identity="identity",
        residual_compose=_concatenate,
        output_compose=_concatenate,
        automorphisms=ReverseActionAutomorphisms.trivial(),
        ledger=ledger,
        coordinate_programs=programs,
    )
    before = ledger.snapshot()
    assert arena.transformed(arena.identity, ActionTransform.IDENTITY) == arena.identity
    with pytest.raises(ValueError, match="no certified mirror/conjugacy"):
        arena.transformed(arena.identity, ActionTransform.MIRROR)
    with pytest.raises(ValueError, match="no certified mirror/conjugacy"):
        arena.transformed(arena.identity, ActionTransform.CONJUGATE)
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


@pytest.mark.parametrize(
    "payload",
    (("nested", 1), ("nested", True), ("nested", 1.0), ("x",) * 257),
)
def test_reverse_coordinate_atoms_reject_untyped_or_unbounded_nested_payloads(
    payload: object,
) -> None:
    ledger = ResourceLedger()
    programs = ReverseCoordinateProgramArena(10, ledger)
    before = ledger.snapshot()
    with pytest.raises((TypeError, ValueError)):
        programs.atom(payload)
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


@pytest.mark.algebra
def test_reverse_field_composition_is_associative_and_chronological() -> None:
    arena = _arena()
    a = _atom(arena, "a", growth=0, forward=CarryFn.ID, backward=CarryFn.CONST0)
    b = _atom(arena, "b", growth=1, forward=CarryFn.CONST1, backward=CarryFn.ID)
    c = _atom(arena, "c", growth=0, forward=CarryFn.CONST0, backward=CarryFn.CONST1)

    left = assert_associative(arena.compose, a, b, c)

    record = arena.resolve(left)
    assert record.residual == arena.intern_residual("abc")
    assert record.output == arena.intern_output("abc")
    assert record.carry_forward is compose_carry_fn(
        CarryFn.CONST0,
        compose_carry_fn(CarryFn.CONST1, CarryFn.ID),
    )
    expected = (
        arena._block(arena.resolve(a))
        .then(arena._block(arena.resolve(b)))
        .then(arena._block(arena.resolve(c)))
    )
    assert (record.radial.canonical_key, record.innovation) == (
        expected.radial.canonical_key,
        expected.innovation,
    )
    assert arena.action_children(left) == (arena.compose(a, b), c)


@pytest.mark.algebra
def test_equal_alternate_derivations_keep_first_construction_witness() -> None:
    arena = _arena()
    a = _atom(arena, "a", growth=0, forward=CarryFn.ID, backward=CarryFn.ID)
    b = _atom(arena, "b", growth=0, forward=CarryFn.ID, backward=CarryFn.ID)
    c = _atom(arena, "c", growth=0, forward=CarryFn.ID, backward=CarryFn.ID)
    ab = arena.compose(a, b)
    first = arena.compose(ab, c)
    first_witness = arena.action_children(first)
    bc = arena.compose(b, c)
    alternate = arena.compose(a, bc)
    assert alternate == first
    assert arena.action_children(alternate) == first_witness == (ab, c)


@pytest.mark.algebra
def test_reverse_field_power_is_binary_and_validates_exact_exponents() -> None:
    arena = _arena()
    action = _atom(
        arena,
        "a",
        growth=0,
        forward=CarryFn.ID,
        backward=CarryFn.CONST0,
    )
    powered = arena.power(action, 37)
    assert arena.resolve(powered).radial.steps == 37
    assert arena.metrics().compose_requests <= 2 * (37).bit_length()
    assert arena.power(action, 0) == arena.identity
    for invalid in (True, 1.5):
        with pytest.raises(TypeError):
            arena.power(action, cast(int, invalid))
    with pytest.raises(ValueError):
        arena.power(action, -1)


@pytest.mark.algebra
def test_typed_coordinate_program_is_canonical_across_power_derivations() -> None:
    ledger = ResourceLedger()
    programs = ReverseCoordinateProgramArena(10, ledger)
    left = programs.compose(programs.primitive, programs.primitive)
    by_squaring = programs.compose(left, left)
    direct = programs.power(programs.primitive, 4)
    assert by_squaring == direct
    assert programs.resolve(direct).pair_steps == 4
    output = programs.compose(direct, programs.terminal)
    assert programs.resolve(output).normalized
    with pytest.raises(ValueError, match="cannot follow terminal"):
        programs.compose(output, programs.primitive)

    rows = {
        row.role: row
        for row in ledger.inventory()
        if row.role
        in {
            "reverse_output_morphism",
            "reverse_output_interner",
            "reverse_output_composition",
        }
    }
    assert rows["reverse_output_morphism"].observed_nodes == programs.metrics().programs
    assert rows["reverse_output_composition"].composition_entries == 3
    assert all(
        row.entries == row.observed_entries and row.payloads_registered
        for row in rows.values()
    )


@pytest.mark.algebra
def test_geometry_composition_and_automorphisms_are_involutive() -> None:
    arena = _arena()
    action = _atom(
        arena,
        "x",
        growth=0,
        forward=CarryFn.CONST0,
        backward=CarryFn.CONST1,
        geometry=ReverseGeometry(4, 0, 2, 5, 1, 3),
    )
    mirrored = arena.transformed(action, ActionTransform.MIRROR)
    assert arena.resolve(mirrored).carry_forward is CarryFn.CONST1
    assert arena.resolve(mirrored).geometry.halo_left == 3
    assert arena.transformed(mirrored, ActionTransform.MIRROR) == action
    conjugated = arena.transformed(action, ActionTransform.CONJUGATE)
    assert arena.resolve(conjugated).carry_forward is CarryFn.CONST1
    assert arena.transformed(conjugated, ActionTransform.CONJUGATE) == action


@pytest.mark.representation
def test_source_death_is_canonical_and_retains_no_source_or_digit_payload() -> None:
    arena = _arena()
    residual = arena.intern_residual("q")
    output = arena.intern_output("o")

    def no_growth(steps: int) -> FieldCellActionID:
        return arena.intern(
            base=10,
            innovation=ReverseAddCyclotomicInnovationBlock(
                8,
                5,
                steps,
                0,
                (0, 0, 0, 0),
            ),
            carry_forward=CarryFn.ID,
            carry_backward=CarryFn.ID,
            residual=residual,
            output=output,
            geometry=ReverseGeometry(0),
        )

    live = no_growth(3)
    dead = arena.compose(live, live)
    record = arena.resolve(dead)
    assert record.source_annihilated
    assert arena.metrics().source_annihilation_derivations == 1
    assert (
        arena.ledger.counters.get(
            "reverse_field_action_source_annihilation_derivations",
            0,
        )
        == 1
    )
    assert arena.ledger.counters.get("source_annihilations", 0) == 0
    assert not hasattr(record, "digits")
    assert not hasattr(record, "slab")
    assert not hasattr(record, "carry_rows")
    assert record.innovation == (0, 0, 0, 0)


@pytest.mark.representation
def test_proof_states_foreign_handles_and_scalar_aliases_reject_before_cache_hit() -> (
    None
):
    arena = _arena()
    action = _atom(
        arena,
        "a",
        growth=0,
        forward=CarryFn.ID,
        backward=CarryFn.ID,
    )
    assert arena.compose(action, action) == arena.compose(action, action)
    before = arena.metrics()
    proof = ProofMachineStateID(arena.owner, "proof-machine-state", action.local_id)
    foreign = replace(action, owner=ArenaToken("reverse-field-actions"))
    forged_kind = replace(action, kind="proof-machine-state")
    for invalid in (proof, foreign, forged_kind, action.local_id, True):
        with pytest.raises((TypeError, ValueError)):
            arena.compose(cast(FieldCellActionID, invalid), action)
    after = arena.metrics()
    assert after.compose_requests == before.compose_requests
    assert after.compose_early_hits == before.compose_early_hits
    with pytest.raises(TypeError):
        arena.intern_residual(proof)
    with pytest.raises(TypeError):
        arena.intern_residual(("nested-proof", proof))
    with pytest.raises(TypeError):
        arena.intern_residual(("packed-digits", 1 << 4096))
    with pytest.raises(TypeError):
        arena.intern_output(0)
    with pytest.raises(TypeError):
        arena.resolve(
            cast(
                "FieldCellActionID",
                CoordinateOutputMorphismID(
                    arena.owner,
                    "coordinate-output-morphism",
                    0,
                ),
            )
        )


@pytest.mark.accounting
def test_reverse_action_publication_is_ledger_owned_and_zero_budget_is_atomic() -> None:
    with pytest.raises(BlockContextBudgetExceeded):
        _arena(ledger=ResourceLedger(max_nodes=0, max_cache_entries=0))

    ledger = ResourceLedger(max_nodes=100, max_cache_entries=100)
    arena = _arena(ledger=ledger)
    action = _atom(
        arena,
        "a",
        growth=0,
        forward=CarryFn.ID,
        backward=CarryFn.ID,
    )
    assert arena.ledger is ledger
    assert arena.owner is arena.identity.owner
    assert arena.resolve(action).base == 10
    snapshot = ledger.snapshot()
    assert snapshot.nodes == (
        arena.metrics().action_count
        + arena.metrics().residual_count
        + arena.metrics().output_morphism_count
    )


@pytest.mark.representation
def test_residual_and_semantic_records_are_bounded() -> None:
    arena = ReverseFieldActionArena(
        base=10,
        order=8,
        residual_identity="identity",
        output_identity="identity",
        residual_compose=_concatenate,
        output_compose=_concatenate,
        automorphisms=ReverseActionAutomorphisms.trivial(),
        max_residual_classes=2,
    )
    arena.intern_residual("one-defect")
    with pytest.raises(ValueError):
        arena.intern_residual("second-defect")
    with pytest.raises(ValueError):
        arena.intern_output("x" * 257)


@pytest.mark.representation
def test_reverse_diamond_compiles_primitive_law_without_t2_proof_states() -> None:
    import number_compiler.arithmetic.contracts.block_kernel as kernels
    from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect

    assert not hasattr(kernels, "_load_base10_t2_kernel")
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    power = compile_reverse_pair_power(compiler, 10, 4)
    assert power.root is not None and power.root.exponent == 4
    assert not any(type(node) is FiniteBlockEffect for node in compiler.nodes)
    assert ledger.counters.get("family_bisimulation_machine_applications", 0) == 0
    assert ledger.counters.get("family_bisimulation_symbol_visits", 0) == 0
    assert ledger.counters.get("sequential_generation_advances", 0) == 0


def test_reverse_family_stores_are_independently_inventoried() -> None:
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    ledger, cells, root = _source_cells((1, 2, 3, 4))
    codec = ReversePoweredLocalCodec(10, cells)
    codec.source_action(root)
    ports = ReverseLocalInterfaceArena(10, ledger)
    ports.advance(BoundarySide.LEFT, ports.identity[0], 1)
    ports.emit(ports.identity[0], 1, ports.identity[1])
    arena = _arena(ledger=ledger)
    action = _atom(
        arena,
        "a",
        growth=0,
        forward=CarryFn.ID,
        backward=CarryFn.CONST0,
    )
    arena.compose(action, action)
    relevant = {
        "reverse_local_state_index",
        "reverse_local_action",
        "reverse_local_action_interner",
        "reverse_local_action_composition",
        "reverse_local_leaf_binding",
        "reverse_local_source_binding",
        "reverse_port_state",
        "reverse_port_interner",
        "reverse_port_transition",
        "reverse_leaf_output",
        "reverse_residual_node",
        "reverse_residual_interner",
        "reverse_output_morphism",
        "reverse_output_interner",
        "reverse_field_action",
        "reverse_action_interner",
        "reverse_action_composition",
        "reverse_action_transform",
        "reverse_action_construction_witness",
    }
    rows = [row for row in ledger.inventory() if row.role in relevant]
    assert relevant <= {row.role for row in rows}
    assert all(row.observed_entries == row.entries for row in rows)
    assert all(row.payloads_registered for row in rows)
    assert all(not row.evictable for row in rows)
    node_roles = {
        "reverse_local_action",
        "reverse_port_state",
        "reverse_residual_node",
        "reverse_output_morphism",
        "reverse_field_action",
    }
    assert all(
        row.observed_nodes == row.nodes for row in rows if row.role in node_roles
    )
    report = collect_ledger_metrics(ledger)
    assert report.algebraic_component_nodes == (
        codec.metrics().action_count + arena.metrics().output_morphism_count
    )
    assert report.finite_port_state_nodes == (
        ports.metrics().left_states + ports.metrics().right_states
    )
