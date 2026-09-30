from tests.support.arithmetic_fixtures import wide_innovation_operators

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.symbolic_innovation import (
    MAX_PRIMITIVE_IDENTITY_UNITS,
    RadialMultiplier,
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import ResourceLedger


def _atom(name: str) -> SemanticIdentity:
    return SemanticIdentity("test", ("primitive-innovation", name))


def test_signed_normal_form_cancels_before_projection() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    left = arena.atom(_atom("left"))
    right = arena.atom(_atom("right"))

    expression = arena.linear_combination(
        ((3, left), (1, right), (-2, left), (-1, right), (-1, left))
    )

    assert expression == arena.zero
    assert ledger.counters["symbolic_innovation_normalization_visits"] == 5


def test_interval_is_one_canonical_source_free_node() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)

    assert arena.interval(0) == arena.zero
    one = arena.interval(1)
    huge_length = (1 << 512) + 7
    huge = arena.interval(huge_length)

    assert one == arena.interval(1)
    assert huge == arena.interval(huge_length)
    assert arena.node_count == 3
    node_row = next(
        row for row in ledger.inventory() if row.role == "innovation_action"
    )
    assert node_row.entries == 3
    assert node_row.nodes == 1 + 1 + 9
    assert ledger.counters["symbolic_innovation_interval_retained_bits"] == 514


@pytest.mark.parametrize("length", [-1, True, 1.5])
def test_interval_rejects_invalid_lengths(length: object) -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    with pytest.raises((TypeError, ValueError)):
        arena.interval(length)  # type: ignore[arg-type]


def test_zero_interval_rejects_a_closed_arena() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    arena.close()

    with pytest.raises(ValueError, match="disposed symbolic innovation arena"):
        arena.interval(0)


def test_interval_composes_and_projects_without_expanding_its_length() -> None:
    from number_compiler.arithmetic.polynomials.cyclotomic_ring import CyclotomicRing

    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    interval = arena.interval(4)
    expression = arena.linear_combination(
        (
            (3, interval),
            (1, arena.chart(interval, CylinderChart(1, -1))),
            (1, arena.radial(interval, RadialMultiplier(1, 1))),
        )
    )
    projected = arena.project_cyclotomic(
        arena.action(RadialMultiplier(), expression),
        order=8,
        bits=8,
        atoms={},
    )
    # 3E4 + zE4 + 2(1+z)E4.
    expected_polynomial = (5, 8, 8, 8, 3)
    ring = CyclotomicRing(8, 1 << 8)
    assert projected.innovation == ring.reduce(expected_polynomial)


def test_huge_interval_projection_uses_only_the_bounded_quotient_degree() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    length = 10**200 + 6
    projected = arena.project_cyclotomic(
        arena.action(RadialMultiplier(), arena.interval(length)),
        order=8,
        bits=5,
        atoms={},
    )

    remainder = length % 8
    expected = tuple(
        (int(index < remainder) - int(index + 4 < remainder)) % 32 for index in range(4)
    )
    assert projected.innovation == expected
    assert ledger.counters["symbolic_innovation_interval_projection_coefficients"] == 4
    assert (
        ledger.counters["symbolic_innovation_interval_projection_operand_bits"]
        == length.bit_length()
    )


def test_wide_interval_budget_refusal_publishes_no_node() -> None:
    ledger = ResourceLedger(max_nodes=2)
    arena = SymbolicInnovationArena(ledger)
    before = ledger.snapshot()

    with pytest.raises(BlockContextBudgetExceeded):
        arena.interval(1 << 512)

    after = ledger.snapshot()
    assert arena.node_count == 1
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


def test_wide_operator_metadata_charges_exact_integer_limbs() -> None:
    ledger, arena = wide_innovation_operators()

    node_row = next(
        row for row in ledger.inventory() if row.role == "innovation_action"
    )
    # Zero and E_1 use one unit each. Scale, radial and chart metadata use
    # ceil(131/64), ceil((131+130)/64), and ceil((1+131+1+1)/64).
    assert node_row.entries == 5
    assert node_row.nodes == 1 + 1 + 3 + 5 + 3


def test_relative_chart_must_be_bound_before_it_enters_identity() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    atom = arena.atom(_atom("seam"))
    relative = CylinderChart(-1, -1, 1, 1)

    with pytest.raises(ValueError, match="bind the chart"):
        arena.chart(atom, relative)

    closed = arena.bind_chart(relative, extent=8, growth=1)
    assert closed == CylinderChart(-1, 8)
    assert arena.chart(atom, closed) == arena.chart(atom, closed)


def test_reflection_transports_growth_radial_before_interning() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    atom = arena.atom(_atom("boundary"))
    radial = RadialMultiplier(3, 2)

    reflected_after_growth = arena.chart(
        arena.radial(atom, radial), CylinderChart(-1, 7)
    )
    growth_after_reflected = arena.radial(
        arena.chart(atom, CylinderChart(-1, 5)), radial
    )

    assert reflected_after_growth == growth_after_reflected


def test_chart_fusion_uses_coefficient_pullback_order() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    atom = arena.atom(_atom("charted"))
    first = CylinderChart(-1, 9)
    second = CylinderChart(1, 2)

    nested = arena.chart(arena.chart(atom, first), second)
    # first(second(i)) = 9 - (i + 2) = 7 - i
    assert nested == arena.chart(atom, CylinderChart(-1, 7))


def test_affine_substitution_projects_to_existing_cyclotomic_owner() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    first_atom_key = _atom("first")
    second_atom_key = _atom("second")
    first_atom = arena.atom(first_atom_key)
    second_atom = arena.atom(second_atom_key)
    first = arena.action(RadialMultiplier(1, 0), first_atom)
    second = arena.action(RadialMultiplier(0, 1), second_atom)
    composed = arena.then(first, second)
    atoms = {
        first_atom_key: (1, 2, 3, 4),
        second_atom_key: (4, 1, 0, 2),
    }

    first_projection = arena.project_cyclotomic(first, order=8, bits=5, atoms=atoms)
    second_projection = arena.project_cyclotomic(second, order=8, bits=5, atoms=atoms)
    composed_projection = arena.project_cyclotomic(
        composed, order=8, bits=5, atoms=atoms
    )

    assert (
        composed_projection.canonical_key
        == first_projection.then(second_projection).canonical_key
    )
    assert composed.multiplier == RadialMultiplier(1, 1)


def test_projection_refuses_an_unresolved_formal_atom() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    action = arena.action(RadialMultiplier(), arena.atom(_atom("missing")))

    with pytest.raises(ValueError, match="unresolved atom"):
        arena.project_cyclotomic(action, order=8, bits=5, atoms={})


def test_mutated_handle_cannot_alias_another_innovation_node() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    first = arena.atom(_atom("first-handle"))
    second = arena.atom(_atom("second-handle"))
    object.__setattr__(first, "local_id", second.local_id)

    with pytest.raises(ValueError, match="handle seal"):
        arena.resolve(first)


def test_atom_is_detached_from_mutable_caller_identity() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    semantic = _atom("detached")
    reference = arena.atom(semantic)
    object.__setattr__(semantic, "behavior", ("changed",))

    # The retained primitive identity is an independent immutable snapshot.
    arena.resolve(reference)


def test_close_releases_stores_and_invalidates_handles() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    reference = arena.atom(_atom("disposed"))
    arena.close()

    with pytest.raises(ValueError, match="disposed"):
        arena.resolve(reference)
    inventory = {
        item.name: item for item in ledger.snapshot().inventory if item.disposed
    }
    assert any(name.endswith("-nodes") for name in inventory)
    assert any(name.endswith("-keys") for name in inventory)


def test_formal_power_is_logarithmic_but_claims_no_source_admission() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    atom_key = _atom("powered")
    action = arena.action(RadialMultiplier(1, 0), arena.atom(atom_key))
    before = arena.node_count
    exponent = 10**30

    powered = arena.power(action, exponent)

    operations = exponent.bit_count() + exponent.bit_length() - 1
    assert powered.multiplier == RadialMultiplier(exponent, 0)
    assert arena.node_count - before <= 3 * operations
    assert ledger.counters["symbolic_innovation_substitutions"] == operations


def test_formal_power_agrees_with_bounded_observer_repetition() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    atom_key = _atom("bounded-power")
    action = arena.action(RadialMultiplier(1, 0), arena.atom(atom_key))
    atoms = {atom_key: (1, 2, 3, 4)}
    projected = arena.project_cyclotomic(action, order=8, bits=5, atoms=atoms)
    repeated = projected.identity(order=8, bits=5)
    for _ in range(13):
        repeated = repeated.then(projected)

    powered = arena.project_cyclotomic(
        arena.power(action, 13), order=8, bits=5, atoms=atoms
    )

    assert powered.canonical_key == repeated.canonical_key


def test_primitive_identity_is_bounded_before_detachment() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    too_large = SemanticIdentity(
        "ignored",
        tuple("x" for _ in range(MAX_PRIMITIVE_IDENTITY_UNITS + 1)),
    )

    with pytest.raises(ValueError, match="finite bound"):
        arena.atom(too_large)


@pytest.mark.parametrize(("order", "bits"), ((32, 5), (8, 65), (3, 5)))
def test_cyclotomic_projection_has_a_bounded_observer_domain(
    order: int, bits: int
) -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    key = _atom("projection-bound")
    action = arena.action(RadialMultiplier(), arena.atom(key))

    with pytest.raises(ValueError, match="bounded observer"):
        arena.project_cyclotomic(action, order=order, bits=bits, atoms={key: (0,)})
