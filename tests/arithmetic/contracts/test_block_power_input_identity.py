from __future__ import annotations

from dataclasses import replace
from typing import cast

import pytest

from devtools.verification.block_power import apply_block_power, power_block_effect
from tests.support.dataclass_records import replace_record


@pytest.mark.parametrize("base", (True, 10.0, "10"))
def test_power_block_effect_rejects_nonexact_base_before_work(base: object) -> None:
    with pytest.raises(TypeError, match="exact integers"):
        power_block_effect(base=cast(int, base), exponent=0)


@pytest.mark.parametrize("exponent", (True, 1.0, "1"))
def test_power_block_effect_rejects_nonexact_exponent_before_work(
    exponent: object,
) -> None:
    with pytest.raises(TypeError, match="exact integers"):
        power_block_effect(base=10, exponent=cast(int, exponent))


@pytest.mark.parametrize("limit", (True, 1.0, "1"))
def test_power_block_effect_rejects_nonexact_limits(limit: object) -> None:
    with pytest.raises(TypeError, match="exact integer or None"):
        power_block_effect(
            base=10, exponent=0, max_cache_entries=cast(int | None, limit)
        )


@pytest.mark.parametrize("symbol", (True, 7.0, "7"))
def test_apply_block_power_rejects_symbol_coercions(symbol: object) -> None:
    power = power_block_effect(base=10, exponent=0)
    with pytest.raises(TypeError, match="source symbols must be exact integers"):
        apply_block_power(power, [cast(int, symbol)])


def test_apply_block_power_rejects_forged_numeric_metadata() -> None:
    power = power_block_effect(base=10, exponent=0)
    for forged in (
        replace(power, base=True),
        replace_record(power, {"exponent": 0.0}),
    ):
        with pytest.raises(TypeError, match="metadata must contain exact integers"):
            apply_block_power(forged, [7])


@pytest.mark.parametrize("source", ("7", (value for value in (7,))))
def test_apply_block_power_requires_an_explicit_sequence(source: object) -> None:
    power = power_block_effect(base=10, exponent=0)
    with pytest.raises(TypeError, match="tuple or list"):
        apply_block_power(power, cast(tuple[int, ...], source))


@pytest.mark.parametrize("base", (True, 2.0, "2"))
def test_primitive_kernel_rejects_numeric_base_aliases(base: object) -> None:
    from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect

    with pytest.raises(TypeError, match="exact integer"):
        BaseBlockEffect(cast(int, base))


@pytest.mark.parametrize("base", (2, 3, 5, 10, 12))
def test_all_reverse_bases_bypass_proof_execution(
    base: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    from devtools.verification.block_composed import ComposedBlockEffect
    from tests.support.reverse_pair_oracle import reference_successor

    power = power_block_effect(base=base, exponent=4)
    source = (base, base)
    expected: tuple[int, ...] = source
    for _ in range(4):
        expected = reference_successor(expected, base)

    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("compatibility projection reached the proof executor")

    monkeypatch.setattr(ComposedBlockEffect, "advance", forbidden)
    monkeypatch.setattr(ComposedBlockEffect, "emit", forbidden)
    assert apply_block_power(power, source).values == expected


def test_block_projection_rejects_mismatched_operator_metadata() -> None:
    power = power_block_effect(base=3, exponent=2)
    for forged in (
        replace(power, exponent=3),
        replace(power, base=4),
        replace(power, exponent=0),
        replace(power, root=None),
    ):
        with pytest.raises(ValueError):
            apply_block_power(forged, (2, 2))


def test_custom_identity_program_keeps_its_semantics_and_budget() -> None:
    from array import array

    from number_compiler import BlockContextBudget, BlockContextBudgetExceeded
    from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
    from number_compiler.arithmetic.contracts.block_power_types import BlockPower

    identity = FiniteBlockEffect(
        base=10,
        exponent=1,
        left_count=1,
        right_count=1,
        alphabet_size=20,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", [0] * 20),
        right_transitions=array("I", [0] * 20),
        outputs=bytes(range(20)),
        kernel_name="identity",
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
    )
    power = BlockPower(10, 1, identity, 1, 0, 1, BlockContextBudget())
    result = apply_block_power(power, (2,))
    assert result.values == (2,)
    assert result.runtime_stats["retained_nodes"] > 0
    assert result.runtime_stats["retained_cache_entries"] > 0
    assert result.runtime_stats["peak_nodes"] >= result.runtime_stats["retained_nodes"]
    assert (
        result.runtime_stats["peak_cache_entries"]
        >= result.runtime_stats["retained_cache_entries"]
    )
    # The compatibility operator owns its construction, not an already lowered
    # application's private runtime. Repeated applications get fresh budgets.
    assert power.budget.created_nodes == power.budget.cache_entries == 0
    tight = replace(
        power,
        budget=BlockContextBudget(
            # The budget covers live construction workspace as well as the
            # final retained graph. Calibrate from actual same-run peaks.
            max_nodes=result.runtime_stats["peak_nodes"],
            max_cache_entries=result.runtime_stats["peak_cache_entries"],
        ),
    )
    assert apply_block_power(tight, (2,)).values == (2,)
    assert apply_block_power(tight, (2,)).values == (2,)
    assert tight.budget.created_nodes == tight.budget.cache_entries == 0
    rejected = replace(power, budget=BlockContextBudget(max_cache_entries=0))
    with pytest.raises(BlockContextBudgetExceeded):
        apply_block_power(rejected, (2,))
    assert rejected.budget.created_nodes == rejected.budget.cache_entries == 0


@pytest.mark.parametrize("root", (True, 1, 1.0, "operator", object()))
def test_block_projection_rejects_unadmitted_root_before_dispatch(root: object) -> None:
    power = power_block_effect(base=3, exponent=1)
    forged = replace_record(power, {"root": root})
    before = (power.budget.created_nodes, power.budget.cache_entries)
    with pytest.raises(TypeError, match="complete operator interface"):
        apply_block_power(forged, (2, 2))
    assert (power.budget.created_nodes, power.budget.cache_entries) == before
