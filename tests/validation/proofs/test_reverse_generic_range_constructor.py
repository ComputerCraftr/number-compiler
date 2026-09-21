"""Release acceptance: one generic constructor must own decimal powers.

These positive assertions deliberately fail until a complete return is
published. A specialized chamber or two-step consumer cannot discharge them.
"""

import importlib.util
from typing import Never

import pytest

from devtools.experiments.reverse_add import (
    chamber_exit,
    edge_interior_d4_regions,
    edge_interior_regions,
    uniform_projection_reference,
)
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.arithmetic.functions import residual
from number_compiler.hashlife.execution.continuations.higher_bimachine import (
    HigherBimachineRuntime,
)
from number_compiler.hashlife.execution.recursive_outputs import (
    RecursiveCoordinateMorphismArena,
)
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add import source_images
from number_compiler.sequences.reverse_add.cylinder_innovation import (
    PrimitiveSuccessorClause,
)
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts

pytestmark = pytest.mark.validation


def _forbidden(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("generic complete return used a retired or specialized path")


@pytest.fixture
def generic_only(monkeypatch: pytest.MonkeyPatch) -> None:
    assert importlib.util.find_spec("number_compiler.hashlife.actions.power") is None
    assert (
        importlib.util.find_spec("number_compiler.hashlife.execution.cascade_power")
        is None
    )
    assert (
        importlib.util.find_spec("number_compiler.hashlife.execution.cascade") is None
    )
    # Resolved pair-field shapes are output fixtures, never temporal states.
    # A source-bound cylinder must construct its innovation/predicates first.
    for name in (
        "uniform_successor",
        "uniform_no_growth_power",
        "edge_core_successors",
        "select_clause",
    ):
        monkeypatch.setattr(uniform_projection_reference, name, _forbidden)
    monkeypatch.setattr(
        uniform_projection_reference.ProjectionClause, "instantiate", _forbidden
    )
    monkeypatch.setattr(chamber_exit, "analyze_chamber_exit", _forbidden)
    # Hand-derived finite chamber rules are reference evidence, not the
    # generic source-bound constructor, even when their expressions are DAGs.
    monkeypatch.setattr(edge_interior_regions, "construct_edge_interior_d2", _forbidden)
    monkeypatch.setattr(
        edge_interior_d4_regions, "construct_edge_interior_d2", _forbidden
    )
    monkeypatch.setattr(
        edge_interior_d4_regions, "construct_edge_interior_d4", _forbidden
    )
    monkeypatch.setattr(ReverseAddCyclotomicInnovationBlock, "from_events", _forbidden)
    # A primitive whole-function identity does not authorize reconstructing
    # the next pair field point by point to discover a temporal clause.
    monkeypatch.setattr(
        PrimitiveSuccessorClause, "successor_pair_coefficient", _forbidden
    )
    # The production quotient must be admitted before temporal composition.
    # Compressing/minimizing a universal context machine after construction
    # cannot satisfy this gate, even if it eventually emits correct digits.
    monkeypatch.setattr(residual, "minimize_bimachine", _forbidden)
    for name in ("second_pair", "second_carry", "second_width"):
        monkeypatch.setattr(SourceCarryPorts, name, _forbidden)
    for name in ("validate_same_carry_chamber", "same_carry_digit"):
        monkeypatch.setattr(source_images, name, _forbidden)
    adapter = source_images.ReverseSourceImageWorkspace
    workspace = adapter(ResourceLedger(), 196, 0)
    adapter_type = type(workspace.adapter)
    workspace.dispose()
    for name in (
        "iter_second_digits",
        "iter_same_carry_digits",
        "iter_primitive_digits",
    ):
        monkeypatch.setattr(adapter_type, name, _forbidden)
    monkeypatch.setattr(CausalTileEngine, "_run", _forbidden)
    monkeypatch.setattr(HigherBimachineRuntime, "point", _forbidden)
    monkeypatch.setattr(RecursiveCoordinateMorphismArena, "temporal", _forbidden)


@pytest.mark.parametrize(
    ("seed", "steps", "expected"),
    (
        (196, 2, "1675"),
        (0, 4, "0"),
        (1, 4, "16"),
        (18, 4, "10890"),
        (196, 4, "13783"),
        (1593, 4, "109989"),
    ),
)
@pytest.mark.parametrize("point_first", (False, True))
def test_generic_return_serves_width_points_and_stream(
    seed: int,
    steps: int,
    expected: str,
    point_first: bool,
    generic_only: None,
) -> None:
    digits = tuple(int(digit) for digit in reversed(expected))
    term = ReverseAddPoweredTerm(seed, steps)
    if point_first:
        assert term.digit(0) == digits[0]
    assert term.width() == len(digits)
    assert tuple(term.digit(i) for i in range(len(digits))) == digits
    assert term.digits() == digits
