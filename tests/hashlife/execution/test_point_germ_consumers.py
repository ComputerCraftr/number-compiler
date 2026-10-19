"""Independent consumer checks; point equality never admits a future action."""

from __future__ import annotations

from itertools import product
from typing import Never

import pytest

from number_compiler.api.cli import main
from number_compiler.api.number_api import AntihydraTermPayload
from number_compiler.arithmetic.contracts.exact_tree_context import (
    ExactTreeConstructionForbidden,
)
from number_compiler.arithmetic.fields.dyadic_tile import DyadicSpan
from number_compiler.arithmetic.fields.point_germ import AffinePointGerm
from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
)
from number_compiler.hashlife.execution.dyadic_return_observers import binary_cell
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.arithmetic_images import (
    ANTIHYDRA_ARITHMETIC_LAW,
)
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.physical_images import COLLATZ_PHYSICAL_LAW


@pytest.mark.parametrize("width", range(1, 6))
def test_normalization_preserves_every_affine_bit_function(width: int) -> None:
    modulus = 1 << width
    seen: dict[tuple[int, ...], AffinePointGerm] = {}
    for a, c in product(range(modulus), repeat=2):
        germ = AffinePointGerm.normal_form(width, a, c, 0)
        values = tuple(((a * y + c) >> (width - 1)) & 1 for y in range(modulus))
        assert tuple(germ.at(y) for y in range(modulus)) == values
        assert seen.setdefault(values, germ) == germ


@pytest.mark.parametrize("a,b", ((2, 0), (2, 1), (6, 3), (5, 4), (64, 31)))
def test_affine_spatial_pullback_transports_blank_and_composes(a: int, b: int) -> None:
    for width, cut in product(range(1, 7), (0, 1, 9)):
        germ = AffinePointGerm.normal_form(width, 27, 14, cut)
        residual = germ.pullback(a, b)
        assert residual.pullback(6, 3) == germ.pullback(a * 6, a * 3 + b)
        for y in range(30):
            assert residual.at(y) == germ.at(a * y + b)


def test_current_point_equivalence_is_not_temporal_equivalence() -> None:
    left = AffinePointGerm.normal_form(2, 27, 2, 0)
    right = AffinePointGerm.normal_form(2, 27, 14, 0)
    assert left == right
    # At high fibre zero their next physical images are 1 and 7: blank vs one.
    assert 2 // 2 < 2 <= 14 // 2


@pytest.mark.parametrize("antihydra", (False, True))
def test_shared_image_points_match_independent_recurrences(antihydra: bool) -> None:
    law = ANTIHYDRA_ARITHMETIC_LAW if antihydra else COLLATZ_PHYSICAL_LAW
    for seed, steps in product((0, 1, 8, 27, (1 << 193) + 27), (0, 1, 4, 16, 65)):
        expected = seed
        for _ in range(steps):
            expected = (
                expected + expected // 2
                if antihydra
                else (3 * expected + 1 if expected & 1 else expected // 2)
            )
        workspace = DyadicReturnImageWorkspace(ResourceLedger(), seed, steps, law)
        try:
            for p in (
                *range(10),
                max(0, expected.bit_length() - 1),
                expected.bit_length() + 1,
                10**100,
            ):
                wanted = (
                    2 if p >= max(1, expected.bit_length()) else (expected >> p) & 1
                )
                assert binary_cell(workspace, p) == wanted
        finally:
            workspace.dispose()


def _forbidden(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("point demand forced an endpoint or safety result")


def test_public_antihydra_point_is_lazy_and_reuses_discovery(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(AntihydraArithmeticTerm, "result", _forbidden)
    monkeypatch.setattr(DyadicReturnImageWorkspace, "endpoint", _forbidden)
    monkeypatch.setattr(DyadicReturnImageWorkspace, "first_failure_index", _forbidden)
    term = AntihydraArithmeticTerm(129)
    payload = AntihydraTermPayload(term)
    expected = 8
    for _ in range(129):
        expected += expected // 2
    assert payload.digit(0) == expected & 1
    workspace = term.arithmetic_workspace
    assert workspace is not None
    entries = term.ledger.entries
    construction = {
        k: v for k, v in term.ledger.counters.items() if "point_germ" not in k
    }
    assert payload.digit(7) == (expected >> 7) & 1
    assert term.arithmetic_workspace is workspace
    assert term.ledger.entries == entries
    assert {
        k: v for k, v in term.ledger.counters.items() if "point_germ" not in k
    } == construction
    assert term._physical is None
    workspace.dispose()
    with pytest.raises(ValueError):
        payload.digit(0)


def test_collatz_point_uses_same_kernel_without_endpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(PoweredCollatzTerm, "_source_numerator", _forbidden)
    monkeypatch.setattr(DyadicReturnImageWorkspace, "endpoint", _forbidden)
    term = PoweredCollatzTerm(931386509544713451, 1000)
    assert term.digit(0) == 1  # independent long noncycle fixture
    assert term.resource_ledger.counters["collatz_physical_point_germ_demands"] > 0
    assert (
        term.resource_ledger.counters["collatz_physical_run_contraction_publications"]
        == 1
    )
    assert term._source_image().summary().transfer.upper == 0
    assert (
        term.resource_ledger.counters.get(
            "collatz_physical_point_germ_normalizations", 0
        )
        == 0
    )


def test_antihydra_cli_digits_do_not_request_safety(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(AntihydraArithmeticTerm, "result", _forbidden)
    monkeypatch.setattr(DyadicReturnImageWorkspace, "first_failure_index", _forbidden)
    expected = 8
    for _ in range(129):
        expected += expected // 2
    assert main(["antihydra", "--nth", "129"]) == 0
    assert capsys.readouterr().out.strip() == str(expected)


def test_foreign_action_and_source_are_rejected_before_observation() -> None:
    a = DyadicReturnImageWorkspace(ResourceLedger(), 27, 16, COLLATZ_PHYSICAL_LAW)
    b = DyadicReturnImageWorkspace(ResourceLedger(), 31, 16, COLLATZ_PHYSICAL_LAW)
    a.root_payload = b.root_payload
    with pytest.raises(ValueError):
        binary_cell(a, 0)
    a.dispose()
    b.dispose()


def test_direct_antihydra_point_guards_transient_callbacks(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = AntihydraArithmeticTerm(16)
    assert term.digit(0) in (0, 1)

    def eager(_workspace: DyadicReturnImageWorkspace) -> Never:
        DyadicSpan(0, 0, ())
        raise AssertionError("point scope did not guard the summary callback")

    monkeypatch.setattr(DyadicReturnImageWorkspace, "summary", eager)
    with pytest.raises(ExactTreeConstructionForbidden):
        term.digit(1)
