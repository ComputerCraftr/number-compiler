"""Focused gates for the bounded reverse/add source-image adapter."""

from __future__ import annotations

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.source_images import (
    ReverseActionID,
    ReverseCylinderConstructionUnavailable,
    ReverseImagePayload,
    ReverseSourceImageWorkspace,
)


def _digits(value: int, base: int) -> tuple[int, ...]:
    result: list[int] = []
    while True:
        result.append(value % base)
        value //= base
        if not value:
            return tuple(result)


def _reverse_add(value: int, steps: int, base: int) -> int:
    for _ in range(steps):
        source = _digits(value, base)
        reverse = sum(
            digit * base**position for position, digit in enumerate(reversed(source))
        )
        value += reverse
    return value


@pytest.mark.parametrize(
    ("seed", "base"), ((0, 10), (196, 10), (999, 10), (11, 2), (41, 3))
)
def test_identity_and_one_primitive_are_exact(seed: int, base: int) -> None:
    source = _digits(seed, base)
    reverse = sum(value * base**position for position, value in enumerate(source[::-1]))
    for steps, expected in ((0, seed), (1, seed + reverse)):
        workspace = ReverseSourceImageWorkspace(
            ResourceLedger(), seed, steps, base=base
        )
        digits = tuple(workspace.iter_digits())
        assert digits == _digits(expected, base)
        assert workspace.width() == len(digits)
        assert tuple(workspace.digit(i) for i in range(len(digits))) == digits


def test_one_step_stream_is_linear_and_retains_no_endpoint_word() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 1)
    before = workspace.ledger.counters.get("reverse_source_carry_coordinates", 0)
    assert tuple(workspace.iter_digits()) == (7, 8, 8)
    work = workspace.ledger.counters["reverse_source_carry_coordinates"] - before
    assert work == 3
    image = workspace._image
    assert image is not None
    payload = workspace.scheduler._source_image_core().view(image).payload
    assert not hasattr(payload, "digits")


@pytest.mark.parametrize(
    ("seed", "base"), ((0, 10), (5, 10), (11, 10), (196, 10), (99, 10), (41, 3))
)
def test_fused_second_step_matches_reference_without_midpoint(
    seed: int, base: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, 2, base=base)
    adapter_type = type(workspace.adapter)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("two-step pullback entered a one-step evaluator")

    monkeypatch.setattr(adapter_type, "apply_primitive", forbidden)
    monkeypatch.setattr(adapter_type, "iter_primitive_digits", forbidden)
    monkeypatch.setattr(adapter_type, "_carry_and_digit", forbidden, raising=False)
    monkeypatch.setattr(adapter_type, "_width", forbidden)
    expected = _digits(_reverse_add(seed, 2, base), base)
    assert tuple(workspace.iter_digits()) == expected
    assert workspace.width() == len(expected)
    assert tuple(workspace.digit(i) for i in range(len(expected))) == expected
    assert workspace.ledger.counters.get("source_image_primitive_applications", 0) == 0
    assert (
        workspace.ledger.counters["reverse_source_two_step_pullback_publications"] == 1
    )


@pytest.mark.parametrize(
    "seed",
    (
        int("4" * 512 + "5" * 512),
        int("9" + "4" * 511 + "5" * 511 + "9"),
    ),
)
def test_fused_second_step_full_output_has_linear_source_work(seed: int) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, 2)
    assert tuple(workspace.iter_digits()) == _digits(_reverse_add(seed, 2, 10), 10)
    width = len(_digits(seed, 10))
    assert workspace.ledger.counters["reverse_source_pullback_pair_reads"] <= 8 * width


def test_undemanded_second_step_publishes_one_fused_image() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 2)
    image = workspace.scheduler.source_image(
        workspace.adapter, workspace.source, workspace.root_action
    )
    payload = workspace.scheduler._source_image_core().view(image).payload
    assert isinstance(payload, ReverseImagePayload)
    assert workspace.actions.node(payload.action).steps == 2
    assert workspace.ledger.counters.get("source_image_primitive_applications", 0) == 0


@pytest.mark.parametrize(
    ("seed", "steps", "expected"),
    ((1, 3, 8), (10, 4, 88), (11, 3, 88), (1001, 3, 8008)),
)
def test_powered_same_carry_chamber_is_exact(
    seed: int, steps: int, expected: int
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, steps)
    digits = _digits(expected, 10)
    assert workspace.width() == len(digits)
    assert tuple(workspace.iter_digits()) == digits
    assert tuple(workspace.digit(i) for i in range(len(digits))) == digits
    assert workspace.ledger.counters["reverse_source_same_carry_publications"] == 1
    assert workspace.ledger.counters.get("source_image_primitive_applications", 0) == 0


@pytest.mark.parametrize("seed,steps", ((1, 4), (196, 3), (111589511, 3)))
def test_powered_chamber_rejects_growth_or_changed_carries_before_output(
    seed: int, steps: int
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, steps)
    output = iter(workspace.iter_digits())
    with pytest.raises(
        ReverseCylinderConstructionUnavailable, match="same-carry no-growth"
    ):
        next(output)
    assert workspace.ledger.counters.get("source_image_primitive_applications", 0) == 0
    assert workspace.ledger.counters["reverse_source_chamber_rejections"] >= 1
    assert workspace._image is None


def test_zero_source_admits_huge_power_without_constructing_the_power() -> None:
    steps = 10**26
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 0, steps)
    assert workspace.width() == 1
    assert tuple(workspace.iter_digits()) == (0,)
    assert workspace.digit(0) == 0
    assert workspace.operator_nodes <= 2 * steps.bit_length()
    assert workspace.ledger.counters["reverse_source_chamber_admissions"] >= 1


@pytest.mark.parametrize("base", [2, 3, 10])
def test_two_step_small_sources_against_independent_arithmetic(base: int) -> None:
    for seed in range(512):
        workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, 2, base=base)
        assert tuple(workspace.iter_digits()) == _digits(
            _reverse_add(seed, 2, base), base
        )
        workspace.dispose()
        assert workspace.ledger.nodes == workspace.ledger.entries == 0


def test_composite_demand_refuses_before_primitive_and_retry_does_not_leak(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 20)
    adapter_type = type(workspace.adapter)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("composite demand descended to a primitive")

    monkeypatch.setattr(adapter_type, "apply_primitive", forbidden)
    with pytest.raises(ReverseCylinderConstructionUnavailable, match="20 temporal"):
        workspace.width()
    retained = workspace.ledger.entries, workspace.ledger.nodes
    with pytest.raises(ReverseCylinderConstructionUnavailable, match="20 temporal"):
        workspace.digit(0)
    assert (workspace.ledger.entries, workspace.ledger.nodes) == retained
    assert workspace.ledger.counters.get("source_image_primitive_applications", 0) == 0


def test_undemanded_scheduler_entry_cannot_bypass_composite_gate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 8)
    adapter_type = type(workspace.adapter)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("undemanded image descended to a primitive")

    monkeypatch.setattr(adapter_type, "apply_primitive", forbidden)
    with pytest.raises(ReverseCylinderConstructionUnavailable, match="8 temporal"):
        workspace.scheduler.source_image(
            workspace.adapter, workspace.source, workspace.root_action
        )
    retained = workspace.ledger.entries, workspace.ledger.nodes
    with pytest.raises(ReverseCylinderConstructionUnavailable, match="8 temporal"):
        workspace.scheduler.source_image(
            workspace.adapter, workspace.source, workspace.root_action
        )
    assert (workspace.ledger.entries, workspace.ledger.nodes) == retained
    assert workspace.ledger.counters.get("source_image_primitive_applications", 0) == 0


def test_descriptor_is_lazy_logarithmic_and_handles_are_scoped() -> None:
    left = ReverseSourceImageWorkspace(ResourceLedger(), 196, 1 << 40)
    right = ReverseSourceImageWorkspace(ResourceLedger(), 196, 1)
    assert left.operator_nodes <= 42
    assert left.compose_operations <= 40
    assert left.syntax_depth_bound <= 41
    foreign = ReverseActionID(
        right.root_action.owner,
        right.root_action.kind,
        right.root_action.local_id,
    )
    with pytest.raises(ValueError, match="different arena"):
        left.actions.node(foreign)
    left.dispose()
    with pytest.raises(ValueError, match="disposed"):
        left.actions.node(left.root_action)


def test_dispose_releases_retained_images_and_actions() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 1)
    assert workspace.digit(0) == 7
    workspace.dispose()
    assert workspace.ledger.entries == 0
    assert workspace.ledger.nodes == 0
    with pytest.raises(ValueError, match="disposed"):
        workspace.width()


def test_workspace_rejects_mutated_public_bindings() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 1)
    workspace.steps = 0
    with pytest.raises(ValueError, match="binding was altered"):
        workspace.digit(0)
    workspace.dispose()

    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 1)
    foreign = ReverseSourceImageWorkspace(ResourceLedger(), 196, 1)
    workspace.source = foreign.source
    with pytest.raises(ValueError, match="binding was altered"):
        workspace.width()
    workspace.dispose()
    foreign.dispose()


@pytest.mark.parametrize(
    "ledger", (ResourceLedger(max_nodes=1), ResourceLedger(max_cache_entries=5))
)
def test_failed_workspace_construction_releases_every_reservation(
    ledger: ResourceLedger,
) -> None:
    with pytest.raises(RuntimeError):
        ReverseSourceImageWorkspace(ledger, 196, 1)
    assert ledger.entries == 0
    assert ledger.nodes == 0
