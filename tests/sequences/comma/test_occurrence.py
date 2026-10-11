from __future__ import annotations

import pytest

from number_compiler.sequences.comma import occurrence as occurrence_module
from number_compiler.sequences.comma.arithmetic import comma_children, decimal_sector
from number_compiler.sequences.comma.boundary_quotient import (
    AffineWeight,
    BoundaryState,
    construct_macro,
)
from number_compiler.sequences.comma.carry_generator import C1Phase
from number_compiler.sequences.comma.occurrence import (
    BoundaryOccurrence,
    OccurrencePrefixReturn,
)


def test_boundary_occurrence_derives_low_phase_and_high_from_exact_exponent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    near = BoundaryOccurrence(BoundaryState("N", 2, 5), 5)
    zero = BoundaryOccurrence(BoundaryState("Z", 3, 6), 6)

    def poisoned_value(*_args: object, **_kwargs: object) -> int:
        pytest.fail("finite suffix and phase projections allocated the occurrence")

    monkeypatch.setattr(BoundaryOccurrence, "value", poisoned_value)
    assert near.low_suffix() == 99
    assert near.c1_phase() == C1Phase.from_suffix(1, 99)
    assert near.high_prefix() == 1_999
    assert zero.low_suffix() == 0
    assert zero.c1_phase() == C1Phase.from_suffix(3, 0)
    assert zero.high_prefix() == 30_000


def test_occurrence_value_preflights_large_physical_exponents() -> None:
    class BudgetExceeded(RuntimeError):
        pass

    occurrence = BoundaryOccurrence(
        BoundaryState("Z", 3, 5),
        5 + 924 * 10**20,
    )
    charged: list[int] = []

    def charge_bits(bits: int) -> None:
        charged.append(bits)
        if bits > 10_000:
            raise BudgetExceeded

    with pytest.raises(BudgetExceeded):
        occurrence.value(charge_bits=charge_bits)
    assert charged[-1] > 10_000


def test_boundary_occurrence_rejects_mutated_state_fields() -> None:
    source = BoundaryOccurrence(BoundaryState("N", 2, 5), 5)
    object.__setattr__(source.state, "a", 8)

    with pytest.raises(ValueError, match="exact snapshot"):
        source.value()


def test_boundary_occurrence_rejects_mutated_same_residue_exponent() -> None:
    source = BoundaryOccurrence(BoundaryState("N", 2, 5), 5)
    object.__setattr__(source, "exponent", 929)

    with pytest.raises(ValueError, match="exact snapshot"):
        source.c1_phase()


def test_macro_child_kind_requires_exact_string_before_materializing_children(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = BoundaryOccurrence(BoundaryState("N", 9, 5), 5)
    prefix = OccurrencePrefixReturn(
        source,
        construct_macro(source.state, grouped_near=True),
    )

    class NKindAlias:
        def __eq__(self, other: object) -> bool:
            return other == "N"

    def reject_materialization(*_args: object, **_kwargs: object) -> object:
        pytest.fail("invalid child kind reached literal-child materialization")

    monkeypatch.setattr(
        OccurrencePrefixReturn,
        "ordered_literal_children",
        reject_materialization,
    )
    with pytest.raises(ValueError, match="child kind must be N or Z"):
        prefix.child(NKindAlias())  # type: ignore[arg-type]


@pytest.mark.parametrize(
    ("leading", "outcome"),
    ((2, "landmine"), (9, "fork")),
)
def test_powered_prefix_matches_literal_path_and_keeps_terminal_distinct(
    leading: int, outcome: str
) -> None:
    state = BoundaryState("N", leading, 5)
    source = BoundaryOccurrence(state, 5)
    template = construct_macro(state, grouped_near=True)
    prefix = OccurrencePrefixReturn(source, template)
    current = source.value()

    for _ in range(prefix.transition_count):
        children = comma_children(current)
        assert len(children) == 1
        current = children[0]

    assert prefix.terminal_value == current
    assert prefix.outcome == outcome
    assert prefix.width_delta == decimal_sector(current).exponent - source.exponent
    assert prefix.c1_count == current // 100 - source.value() // 100
    assert prefix.terminal_low_suffix == current % 100
    assert prefix.terminal_c1_phase.suffix == current % 100

    terminal_children = comma_children(current)
    if outcome == "landmine":
        assert terminal_children == ()
        assert prefix.ordered_children() == ()
        with pytest.raises(ValueError, match="no literal child"):
            prefix.child("N")
    else:
        occurrences = prefix.ordered_children()
        assert tuple(child.state.kind for child in occurrences) == ("N", "Z")
        assert tuple(child.value() for child in occurrences) == terminal_children
        assert current not in terminal_children
        assert prefix.transition_count > 0
        assert set(terminal_children).isdisjoint(comma_children(source.value()))
        n_edge = prefix.child("N")
        assert n_edge.prefix is prefix
        assert n_edge.c1_count() == n_edge.target.high_prefix() - source.high_prefix()
        assert n_edge.weighted_action().exponent_delta == prefix.width_delta


def test_terminal_coordinates_reuse_the_validated_exact_width_and_phase(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = BoundaryOccurrence(BoundaryState("N", 9, 5), 5)
    prefix = OccurrencePrefixReturn(
        source, construct_macro(source.state, grouped_near=True)
    )

    def poisoned_sector(*_args: object, **_kwargs: object) -> object:
        pytest.fail("terminal projection rescanned the large literal")

    monkeypatch.setattr(occurrence_module, "decimal_sector", poisoned_sector)
    assert prefix.terminal_exponent == source.exponent + prefix.width_delta
    assert prefix.terminal_c1_phase.suffix == prefix.terminal_low_suffix


def test_published_prefix_rejects_changed_macro_weight() -> None:
    source = BoundaryOccurrence(BoundaryState("N", 9, 5), 5)
    template = construct_macro(source.state, grouped_near=True)
    prefix = OccurrencePrefixReturn(source, template)
    object.__setattr__(template, "weight", AffineWeight(0, 0, 1))

    with pytest.raises(ValueError, match="snapshot"):
        _ = prefix.terminal_value


@pytest.mark.parametrize("mutate_before_publication", (False, True))
def test_prefix_rejects_equality_alias_in_macro_source(
    mutate_before_publication: bool,
) -> None:
    class EqualityTrap:
        calls = 0

        def __eq__(self, _other: object) -> bool:
            self.calls += 1
            raise AssertionError("untrusted boundary equality was evaluated")

    source = BoundaryOccurrence(BoundaryState("N", 9, 5), 5)
    template = construct_macro(source.state, grouped_near=True)
    prefix = None
    if not mutate_before_publication:
        prefix = OccurrencePrefixReturn(source, template)

    forged_source = BoundaryState("N", 9, 5)
    alias = EqualityTrap()
    object.__setattr__(forged_source, "kind", alias)
    object.__setattr__(template, "source", forged_source)

    with pytest.raises(ValueError, match="noncanonical scalar fields"):
        if prefix is None:
            OccurrencePrefixReturn(source, template)
        else:
            _ = prefix.terminal_value
    assert alias.calls == 0


def test_prefix_template_point_checks_only_the_selected_sealed_fragment() -> None:
    exponent = 934
    state = BoundaryState("N", 2, exponent % 924)
    source = BoundaryOccurrence(state, exponent)
    template = construct_macro(state)
    prefix = OccurrencePrefixReturn(source, template)
    selected = next(
        (
            (index, fragment)
            for index, fragment in enumerate(template.sector_fragments)
            if fragment.period and fragment.complete_cycles.evaluate(exponent) > 0
        ),
        None,
    )
    assert selected is not None
    index, fragment = selected
    transition_offset = (
        template.prefix_weights[index].evaluate(exponent) + fragment.period
    )
    object.__setattr__(fragment, "displacement", fragment.displacement + 1)

    # The cached terminal is independent of chart-component reads; point
    # selection validates its logarithmically selected component rows.
    assert prefix.terminal_value > 0
    with pytest.raises(ValueError, match="publication was altered"):
        prefix.template.point(exponent, transition_offset)


def test_child_occurrence_composition_uses_shared_exact_width_action() -> None:
    source = BoundaryOccurrence(BoundaryState("N", 9, 5), 5)
    prefix = OccurrencePrefixReturn(
        source, construct_macro(source.state, grouped_near=True)
    )
    first = prefix.child("Z")
    assert first.target.state == BoundaryState("Z", 3, 6)
    assert first.target.exponent == 6

    second_prefix = OccurrencePrefixReturn(
        first.target,
        construct_macro(first.target.state, grouped_near=True),
    )
    second = second_prefix.child("N")
    assert second.target.state == BoundaryState("N", 4, 9)
    assert second.target.exponent == 9

    composed = first.then(second)
    assert composed.exponent_delta == (
        first.weighted_action().exponent_delta + second.weighted_action().exponent_delta
    )
    assert composed.exponent_delta == 4
    assert second.target.exponent == source.exponent + composed.exponent_delta
    assert (
        second.target.high_prefix() - source.high_prefix()
        == first.c1_count() + second.c1_count()
    )


def test_same_semantic_boundary_at_different_physical_exponents_is_distinct() -> None:
    canonical = BoundaryOccurrence(BoundaryState("N", 6, 5), 5)
    transported = BoundaryOccurrence(BoundaryState("N", 6, 5), 929)
    assert canonical.state == transported.state
    assert canonical.exponent != transported.exponent
    assert canonical.value() != transported.value()
