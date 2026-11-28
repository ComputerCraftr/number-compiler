"""Source-issued three-tick edge guard and its open-ring consumer."""

from __future__ import annotations

import json
from collections.abc import Callable
from typing import cast

import pytest

from number_compiler.api import cli
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add import q19_border_control
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from tests.support.private_attributes import private_test_attribute


def _literal_growth(value: int) -> tuple[int, ...]:
    growth: list[int] = []
    for _ in range(3):
        successor = value + int(str(value)[::-1])
        growth.append(int(len(str(successor)) > len(str(value))))
        value = successor
    return tuple(growth)


def test_source_guard_101_matches_literal_and_existing_border_relation() -> None:
    for value in range(100, 1000):
        digits = digits_lsd(value, 10)
        if not 14 <= digits[0] + digits[-1] <= 17:
            continue
        ledger = ResourceLedger()
        owner = ReversePairQ19OutputOwner(ledger, digits, base=10)
        try:
            with ledger.reservation(owner.scratch_owner, nodes=400):
                certify = cast(
                    Callable[..., q19_border_control.CertifiedBorderGrowth],
                    private_test_attribute(q19_border_control, "_certify_reserved"),
                )
                generic = certify(
                    owner, owner.initial, steps=3, window_digits=1, max_states=100
                )
            # A second owner keeps the generic issued root out of the new path's cache.
            other_ledger = ResourceLedger()
            other = ReversePairQ19OutputOwner(other_ledger, digits, base=10)
            try:
                certificate = other.certify_border_growth(
                    other.initial, steps=3, window_digits=1, max_states=100
                )
                assert certificate.growth_word == _literal_growth(value) == (1, 0, 1)
                assert certificate.outer_pairs == generic.outer_pairs
                assert certificate.window_tiles == generic.window_tiles
                assert certificate.max_visited_states == generic.max_visited_states
                assert certificate.source_pair_inspections == 0
            finally:
                other.dispose()
                assert other_ledger.nodes == other_ledger.entries == 0
        finally:
            owner.dispose()
            assert ledger.nodes == ledger.entries == 0


def test_source_guard_101_cli_uses_no_border_frontier(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("the admitted source opened the border frontier")

    monkeypatch.setattr(q19_border_control, "_certify_reserved", forbidden)
    assert (
        cli.main(
            [
                "reverse-add",
                "--seed",
                "599",
                "--nth",
                "3",
                "--no-value",
                "--info",
                "temporal.open-ring",
                "--spatial-bank-morphism-count",
                "1",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    ring = packet["info"]["temporal.open-ring"]
    assert ring["status"] == "available"
    assert ring["widths"] == [3, 4, 4, 5]


@pytest.mark.parametrize(("seed", "max_states"), [(59, 100), (599, 1), (500999, 2)])
def test_source_guard_keeps_state_budget_refusal(seed: int, max_states: int) -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
    try:
        with pytest.raises(q19_border_control.BoundaryControlNotAuthorized):
            owner.certify_border_growth(
                owner.initial, steps=3, window_digits=1, max_states=max_states
            )
    finally:
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0
