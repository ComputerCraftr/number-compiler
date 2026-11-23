"""Source-bound transient effects and projected upper carry responses."""

from __future__ import annotations

import random

import pytest

from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
)
from number_compiler.hashlife.execution.dyadic_upper_band import (
    certified_lower_upper_action,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.arithmetic_images import (
    AntihydraArithmeticImageWorkspace,
)
from number_compiler.sequences.antihydra.mahler_transient_carry_sheet import (
    eight_step_carry_sheet,
)


def _literal(source: int, width: int) -> tuple[int, int, int, int]:
    delta = minimum = odd = 0
    for _ in range(width):
        parity = source & 1
        source = (3 * source) // 2
        delta += 2 - 3 * parity
        minimum = min(minimum, delta)
        odd += parity
    return source, delta, minimum, odd


def _assert_cylinder_lifts(
    workspace: AntihydraArithmeticImageWorkspace,
    width: int,
    residue: int,
    lifts: tuple[int, ...],
) -> None:
    effect = workspace.transient_leaf_effect(width, residue)
    assert effect is not None
    for lift in lifts:
        source = residue + (lift << width)
        endpoint, delta, minimum, odd = _literal(source, width)
        assert (
            effect.transfer.upper * source + effect.transfer.offset
            == endpoint * effect.transfer.lower
        )
        assert (effect.delta, effect.minimum, effect.odd_steps) == (
            delta,
            minimum,
            odd,
        )


def test_sheet_and_wider_cylinders_agree_with_literal_high_lifts() -> None:
    sheet = eight_step_carry_sheet()
    assert len(sheet) == 256
    for source, (correction, delta, minimum, odd) in enumerate(sheet):
        for lift in (0, 1, 3):
            endpoint, wanted_delta, wanted_minimum, wanted_odd = _literal(
                source + 256 * lift, 8
            )
            assert (3**8 * (source + 256 * lift) - correction) // 256 == endpoint
            assert (delta, minimum, odd) == (wanted_delta, wanted_minimum, wanted_odd)
    workspace = AntihydraArithmeticImageWorkspace(
        ResourceLedger(), 0, shared_cache=False
    )
    try:
        assert (
            DyadicReturnImageWorkspace.MAX_LEAF_STEPS == workspace.MAX_LEAF_STEPS == 64
        )
        assert workspace.MAX_TRANSIENT_FOLD_STEPS == 128
        rng = random.Random(20261120)
        for width in (8, 12, 64, 65, 96, 128):
            for residue in (0, 1, 8, (1 << width) - 1, rng.getrandbits(width)):
                _assert_cylinder_lifts(workspace, width, residue, (0, 1, 3))
        with pytest.raises(ValueError):
            workspace.transient_leaf_effect(129, 8)
    finally:
        workspace.dispose()


def test_upper_projection_preserves_phase_safety_and_composition() -> None:
    workspace = AntihydraArithmeticImageWorkspace(
        ResourceLedger(), 0, shared_cache=False
    )
    try:
        rng = random.Random(42192026)
        for _ in range(500):
            a, b = rng.randrange(1, 9), rng.randrange(1, 9)
            cut = a + b + rng.randrange(7)
            source = rng.getrandbits(cut + 9)
            left = workspace.transient_leaf_effect(a, source & ((1 << a) - 1))
            assert left is not None
            first = certified_lower_upper_action(
                left, source & ((1 << cut) - 1), cut=cut, demand_width=9
            )
            mid, delta, minimum, odd = _literal(source, a)
            right = workspace.transient_leaf_effect(b, mid & ((1 << b) - 1))
            assert right is not None
            second = certified_lower_upper_action(
                right, mid & ((1 << (cut - a)) - 1), cut=cut - a, demand_width=9
            )
            whole = workspace.transient_leaf_effect(
                a + b, source & ((1 << (a + b)) - 1)
            )
            assert whole is not None
            direct = certified_lower_upper_action(
                whole, source & ((1 << cut) - 1), cut=cut, demand_width=9
            )
            end, whole_delta, whole_minimum, whole_odd = _literal(source, a + b)
            assert first.then(second) == direct
            assert direct.apply(source >> cut) == (end >> (cut - a - b)) & 511
            assert (whole_delta, whole_minimum, whole_odd) == (
                delta + right.delta,
                min(minimum, delta + right.minimum),
                odd + right.odd_steps,
            )
        mismatched = workspace.transient_leaf_effect(3, 5)
        assert mismatched is not None
        with pytest.raises(ValueError, match="aligned lower cylinder"):
            certified_lower_upper_action(mismatched, 4, cut=3, demand_width=9)
    finally:
        workspace.dispose()


def test_repeat_prefilter_matches_literal_low_cylinders() -> None:
    workspace = AntihydraArithmeticImageWorkspace(
        ResourceLedger(), 0, shared_cache=False
    )
    try:
        rng = random.Random(20261121)
        for width in (12, 24, 32, 64, 128):
            sources = (0, 1, 8, (1 << width) - 1) + tuple(
                rng.getrandbits(width) for _ in range(80)
            )
            for source in sources:
                _assert_cylinder_lifts(workspace, width, source, (0,))
    finally:
        workspace.dispose()


@pytest.mark.parametrize(
    "source,delta,minimum,odd", ((0, 256, 0, 0), (1, -128, -128, 128))
)
def test_transient_uniform_cylinder_does_not_construct_carry_sheet(
    monkeypatch: pytest.MonkeyPatch,
    source: int,
    delta: int,
    minimum: int,
    odd: int,
) -> None:
    import number_compiler.sequences.antihydra.mahler_transient_carry_sheet as carry_sheet

    def forbid_sheet() -> tuple[tuple[int, int, int, int], ...]:
        raise AssertionError("fixed point reconstructed the carry sheet")

    monkeypatch.setattr(carry_sheet, "eight_step_carry_sheet", forbid_sheet)
    workspace = AntihydraArithmeticImageWorkspace(
        ResourceLedger(), 0, shared_cache=False
    )
    try:
        effect = workspace.transient_leaf_effect(128, source)
        assert effect is not None
        assert effect.transfer.upper * source + effect.transfer.offset == (
            effect.transfer.lower * source
        )
        assert (effect.delta, effect.minimum, effect.odd_steps) == (delta, minimum, odd)
    finally:
        workspace.dispose()


def test_upper_seam_failure_releases_balanced_scratch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.execution import dyadic_return_transport

    workspace = AntihydraArithmeticImageWorkspace(
        ResourceLedger(), 0, shared_cache=False
    )
    try:

        def interrupted(*_args: object, **_kwargs: object) -> None:
            raise ArithmeticError("upper seam cancelled")

        monkeypatch.setattr(
            dyadic_return_transport, "certified_lower_upper_action", interrupted
        )
        with pytest.raises(ArithmeticError, match="upper seam cancelled"):
            dyadic_return_transport.balanced_residue_effect(
                workspace, 256, (1 << 200) + 31
            )
        assert len(workspace.balanced_stack) == 0
        assert workspace.ledger.account_usage(workspace.balanced_stack_owner) == (0, 0)
    finally:
        workspace.dispose()
