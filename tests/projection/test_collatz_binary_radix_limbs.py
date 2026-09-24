"""Scalar power-of-two radix points preserve blank versus zero padding."""

from dataclasses import replace
from typing import Never

import pytest

from number_compiler.api.number_api import PoweredCollatzTermPayload
from number_compiler.hashlife.execution.dyadic_return_images import DyadicReturnImageID
from number_compiler.hashlife.execution.source_bound_images import SourceImageDemand
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


@pytest.mark.parametrize(
    "seed,steps",
    ((1, 0), (2, 0), (63, 0), (64, 0), (82, 0), (1, 1), (2, 1), (27, 3), (16, 4)),
)
@pytest.mark.parametrize("radix", (4, 64, 1 << 63))
def test_partial_limb_and_exterior_without_width_or_materialization(
    seed: int, steps: int, radix: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    expected = seed
    for _ in range(steps):
        expected = 3 * expected + 1 if expected & 1 else expected // 2

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("scalar limb observed the complete endpoint")

    for name in ("width", "digits", "iter_digits", "materialize"):
        monkeypatch.setattr(PoweredCollatzTerm, name, forbidden)
    term = PoweredCollatzTerm(seed, steps)
    payload = PoweredCollatzTermPayload(term, radix)
    remaining, index = expected, 0
    while remaining:
        remaining, digit = divmod(remaining, radix)
        assert payload.digit(index) == digit
        index += 1
    with pytest.raises(IndexError) as exterior:
        payload.digit(index)
    assert exterior.value.args == (index,)
    with pytest.raises(IndexError):
        term.digit(expected.bit_length())
    assert term.digit(expected.bit_length() - 1) == 1


def test_limb_does_not_swallow_an_internal_point_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def broken(_term: PoweredCollatzTerm, _radix: int, _position: int) -> int:
        raise IndexError("internal point failure")

    monkeypatch.setattr(PoweredCollatzTerm, "_admitted_radix_digit", broken)
    with pytest.raises(IndexError, match="internal point failure"):
        PoweredCollatzTerm(27, 3).radix_digit(2, 0)
    with pytest.raises(IndexError, match="internal point failure"):
        PoweredCollatzTerm(27, 3).digit(0)
    with pytest.raises(IndexError, match="internal point failure"):
        PoweredCollatzTermPayload(PoweredCollatzTerm(27, 3), 64).digit(0)


def test_limb_rejects_an_invalid_kernel_symbol(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        PoweredCollatzTerm,
        "_admitted_radix_digit",
        lambda _self, _radix, _position: 64,
    )
    with pytest.raises(AssertionError):
        PoweredCollatzTermPayload(PoweredCollatzTerm(27, 3), 64).digit(0)


def test_whole_limb_uses_one_guarded_demand_and_reuses_its_cache(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed, steps, radix = (1 << 512) + 27, 129, 1 << 63
    expected = seed
    for _ in range(steps):
        expected = 3 * expected + 1 if expected & 1 else expected // 2

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("limb query expanded into binary point queries")

    monkeypatch.setattr(PoweredCollatzTerm, "_point_symbol", forbidden)
    term = PoweredCollatzTerm(seed, steps)
    payload = PoweredCollatzTermPayload(term, radix)
    assert payload.digit(0) == expected % radix
    assert term._ledger.counters["collatz_image_radix_demands"] == 1
    projection_work = term._ledger.counters["collatz_image_projection_operand_bits"]
    entries = term._ledger.entries
    assert payload.digit(0) == expected % radix
    assert (
        term._ledger.counters["collatz_image_projection_operand_bits"]
        == projection_work
    )
    assert term._ledger.entries == entries


@pytest.mark.parametrize("radix", (2, 64))
def test_warm_point_rejects_disposed_source_image(radix: int) -> None:
    term = PoweredCollatzTerm(27, 16)
    payload = PoweredCollatzTermPayload(term, radix)
    payload.digit(0)
    term._source_image().dispose()
    with pytest.raises(ValueError, match="disposed"):
        payload.digit(0)


def test_warm_limb_rejects_valid_but_wrong_root_image() -> None:
    term = PoweredCollatzTerm(27, 16)
    payload = PoweredCollatzTermPayload(term, 64)
    expected = payload.digit(0)
    term.width()
    workspace = term._source_image()
    previous = workspace.root_payload
    identity = workspace.admit_source(workspace.root_source)
    object.__setattr__(workspace, "root_payload", identity.payload)
    try:
        with pytest.raises(ValueError, match="another source/action"):
            payload.digit(0)
        with pytest.raises(ValueError, match="another source/action"):
            term.radix_digit(64, 0)
        with pytest.raises(ValueError, match="another source/action"):
            term.width()
    finally:
        object.__setattr__(workspace, "root_payload", previous)
    assert payload.digit(0) == expected


def test_cached_width_rejects_disposed_image() -> None:
    term = PoweredCollatzTerm(27, 16)
    assert term.width() > 0
    term._source_image().dispose()
    with pytest.raises(ValueError, match="disposed"):
        term.width()


def test_width_bound_cannot_change_original_source_extent() -> None:
    term = PoweredCollatzTerm(27, 0)
    term._width_bound = (27, 0, 1)
    with pytest.raises(ValueError, match="another source/action"):
        term.digit(0)


def test_warm_limb_rejects_coherent_replacement_root_handles() -> None:
    term = PoweredCollatzTerm(27, 16)
    payload = PoweredCollatzTermPayload(term, 64)
    expected = payload.digit(0)
    workspace = term._source_image()
    original = (workspace.root_source, workspace.root_action, workspace.root_payload)
    other_source = workspace._append_source(
        replace(workspace.source_node(workspace.root_source), residue=28)
    )
    other_image = workspace.scheduler.source_image_demanded(
        workspace,
        other_source,
        workspace.root_action,
        SourceImageDemand("physical-summary"),
    )
    other_payload = workspace.scheduler.source_projection(
        workspace, other_image, SourceImageDemand("physical-summary")
    ).value
    assert isinstance(other_payload, DyadicReturnImageID)
    assert workspace.image_node(other_payload).summary.width == term.steps
    workspace.root_source = other_source
    workspace.root_payload = other_payload
    try:
        with pytest.raises(ValueError, match="another source/action"):
            payload.digit(0)
    finally:
        workspace.root_source, workspace.root_action, workspace.root_payload = original
    assert payload.digit(0) == expected


def test_original_source_points_reuse_charged_width_bound() -> None:
    seed = (1 << 2048) + 27
    term = PoweredCollatzTerm(seed, 0)
    before = dict(term._ledger.counters)
    assert tuple(term.digit(i) for i in range(seed.bit_length())) == tuple(
        (seed >> i) & 1 for i in range(seed.bit_length())
    )
    assert term._ledger.counters["collatz_width_bound_constructions"] == 1
    assert (
        term._ledger.counters["collatz_width_bound_operand_bits"]
        == before["collatz_width_bound_operand_bits"]
    )
    term.steps = 1
    with pytest.raises(ValueError, match="another source/action"):
        term.digit(0)


@pytest.mark.parametrize("field", ("source", "image", "action"))
def test_warm_limb_revalidates_source_image_and_action(field: str) -> None:
    term = PoweredCollatzTerm(27, 16)
    payload = PoweredCollatzTermPayload(term, 64)
    expected = payload.digit(0)
    workspace = term._source_image()
    node: object
    if field == "source":
        source = workspace.source_node(workspace.root_source)
        node = source
        previous = source.residue
        object.__setattr__(node, "residue", previous + 1)
        attribute = "residue"
    elif field == "action":
        action = workspace.action_node(workspace.root_action)
        node = action
        previous = action.width
        object.__setattr__(node, "width", previous + 1)
        attribute = "width"
    else:
        summary = workspace.summary()
        node = summary
        previous = summary.odd_steps
        object.__setattr__(node, "odd_steps", previous + 1)
        attribute = "odd_steps"
    try:
        with pytest.raises(ValueError, match="altered"):
            payload.digit(0)
    finally:
        object.__setattr__(node, attribute, previous)
    assert payload.digit(0) == expected
