"""Adversarial admission checks for the generic runtime K/U carrier."""

from __future__ import annotations

from tests.support.assertions import assert_rejected_atomically

from dataclasses import replace
from typing import TYPE_CHECKING, cast

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.generic_higher import (
    generic_higher_runtime,
)
from number_compiler.resources.metric_collection import collect_ledger_metrics
from tests.support.diamond_query import build

if TYPE_CHECKING:
    from number_compiler.hashlife.observation.diamond_query import DiamondApplication


def _application(
    steps: int = 0,
) -> DiamondApplication:
    return build(BaseBlockEffect(3), (2, 4, 2), 8, steps)


@pytest.mark.parametrize("side", [True, 1.0, -1, 2])
def test_identity_schema_validates_side_before_shortcut(side: object) -> None:
    app = _application()
    schema = generic_higher_runtime(app.runtime).schema
    identity = schema.import_action(app.root)

    before = app.ledger.snapshot()
    with pytest.raises((TypeError, ValueError)):
        schema.state_count(identity, cast(int, side))
    with pytest.raises((TypeError, ValueError)):
        schema.initial(identity, cast(int, side))
    assert app.ledger.snapshot() == before


@pytest.mark.parametrize(
    ("method", "arguments"),
    [
        ("step", (0, True, 0)),
        ("step", (0, 0, True)),
        ("step", (0, 0, 6)),
        ("emit", (True, 0, 0)),
        ("emit", (0, 1.0, 0)),
        ("emit", (0, 6, 0)),
        ("emit", (0, 0, True)),
    ],
)
def test_identity_schema_validates_complete_primitive_port(
    method: str,
    arguments: tuple[object, ...],
) -> None:
    app = _application()
    schema = generic_higher_runtime(app.runtime).schema
    identity = schema.import_action(app.root)

    assert_rejected_atomically(
        app.ledger,
        lambda: getattr(schema, method)(identity, *arguments),
        (TypeError, ValueError),
    )


def test_width_rejects_foreign_second_action_before_importing_first() -> None:
    app = _application(2)
    foreign = _application(1)
    higher = generic_higher_runtime(app.runtime)
    before = app.ledger.snapshot(), len(higher.schema._nodes), len(higher.schema._keys)

    with pytest.raises(ValueError):
        higher.width(app.root, foreign.root, 8)

    assert (
        app.ledger.snapshot(),
        len(higher.schema._nodes),
        len(higher.schema._keys),
    ) == before


def test_schema_rejects_foreign_and_forged_identity_handles_before_lookup() -> None:
    app = _application()
    foreign = _application()
    schema = generic_higher_runtime(app.runtime).schema
    identity = schema.import_action(app.root)
    foreign_identity = generic_higher_runtime(foreign.runtime).schema.import_action(
        foreign.root
    )
    forged = object.__new__(FieldCellActionID)
    object.__setattr__(forged, "owner", identity.owner)
    object.__setattr__(forged, "kind", identity.kind)
    object.__setattr__(forged, "local_id", False)
    before = app.ledger.snapshot()

    for invalid in (foreign_identity, forged):
        with pytest.raises((TypeError, ValueError)):
            schema.initial(invalid, 0)
    assert app.ledger.snapshot() == before


def test_generic_action_audit_rejects_boolean_interner_index() -> None:
    app = _application(2)
    higher = generic_higher_runtime(app.runtime)
    higher.schema.import_action(app.root)
    assert collect_ledger_metrics(app.ledger).forbidden_future_payloads == 0

    original = next(iter(higher.schema._keys))
    higher.schema._keys[original] = True

    assert collect_ledger_metrics(app.ledger).forbidden_future_payloads > 0


def test_generic_action_audit_rejects_equal_forged_child_handle() -> None:
    app = _application(3)
    higher = generic_higher_runtime(app.runtime)
    parent = higher.schema.import_action(app.root)
    record = higher.schema._resolve(parent)
    assert record.children is not None
    child = record.children[0]
    forged = object.__new__(FieldCellActionID)
    object.__setattr__(forged, "owner", child.owner)
    object.__setattr__(forged, "kind", child.kind)
    object.__setattr__(forged, "local_id", True)
    assert forged == child

    nodes = object.__getattribute__(higher.schema._nodes, "_data")
    nodes[parent.local_id] = replace(record, children=(forged, record.children[1]))

    assert collect_ledger_metrics(app.ledger).forbidden_future_payloads > 0


def test_generic_action_audit_rejects_forged_original_handle() -> None:
    app = _application(1)
    higher = generic_higher_runtime(app.runtime)
    action = higher.schema.import_action(app.root)
    record = higher.schema._resolve(action)
    forged = object.__new__(ActionProgramID)
    object.__setattr__(forged, "owner", record.original.owner)
    object.__setattr__(forged, "kind", record.original.kind)
    object.__setattr__(forged, "local_id", float(record.original.local_id))

    nodes = object.__getattribute__(higher.schema._nodes, "_data")
    nodes[action.local_id] = replace(record, original=forged)

    assert collect_ledger_metrics(app.ledger).forbidden_future_payloads > 0
