from __future__ import annotations

import gc
import random
import weakref
from array import array

import pytest

from devtools.proofs.block_power import compose_block_effects
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudget,
    BlockContextBudgetExceeded,
    BlockEffect,
    _effect_key,
)
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
)
from number_compiler.arithmetic.fields.dyadic_tile import join, leaf, tile_arena_metrics
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def finite(
    outputs: bytes | None = None,
    name: str = "same-name",
    left: array[int] | None = None,
) -> FiniteBlockEffect:
    return FiniteBlockEffect(
        base=10,
        exponent=1,
        left_count=1,
        right_count=1,
        alphabet_size=20,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", [0] * 20) if left is None else left,
        right_transitions=array("I", [0] * 20),
        outputs=bytes(range(20)) if outputs is None else outputs,
        kernel_name=name,
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
    )


def test_generic_identity_then_normalization_is_two_without_family_inference() -> None:
    effect = compose_block_effects(
        finite(), DigitNormalizeBlockEffect(10), budget=BlockContextBudget()
    )
    reverse = compose_block_effects(
        BaseBlockEffect(10), DigitNormalizeBlockEffect(10), budget=BlockContextBudget()
    )
    index = HashLifeBlockIndex(effect, (2,), logical_length=3)
    assert isinstance(index._lazy_application, LazyProjection)
    assert index._bounded_application is None
    assert index.direct_powered_point(0) == 2
    assert index.direct_active_width() == 1
    assert _effect_key(effect) != _effect_key(reverse)
    metrics = index.metrics()
    assert metrics.resource_audit_complete == 1
    assert metrics.forbidden_future_payloads == 0
    assert metrics.sequential_generation_advances == 0
    assert metrics.bimachine_composition_certified == 1


def test_finite_kernel_identity_covers_frozen_behavior_and_ignores_names() -> None:
    transitions = array("I", [0] * 20)
    first = finite(left=transitions)
    equivalent = finite(name="renamed")
    other = finite(outputs=bytes([0] * 19 + [19]))
    assert first.canonical_key == equivalent.canonical_key
    assert first.canonical_key != other.canonical_key
    transitions[0] = 100
    assert first.left_transitions[0] == 0
    with pytest.raises(AttributeError):
        first.outputs = bytes([0] * 20)


def test_generic_compositions_never_lower_midpoint_fields(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.fields.dyadic_tile as tiles

    rng = random.Random(553)
    for base in range(2, 6):
        for steps in range(1, 4):
            digits = [rng.randrange(base) for _ in range(4)]
            digits[-1] = 1
            pair = tuple(digits[i] + digits[-1 - i] for i in range(4))
            expected = pair
            effect: BlockEffect = BaseBlockEffect(base)
            for _ in range(steps - 1):
                effect = compose_block_effects(
                    effect, BaseBlockEffect(base), budget=BlockContextBudget()
                )
            effect = compose_block_effects(
                effect, DigitNormalizeBlockEffect(base), budget=BlockContextBudget()
            )
            index = HashLifeBlockIndex(
                effect, pair, logical_length=len(pair) + steps + 2
            )
            for _ in range(steps):
                expected, _ = pair_step(expected, base)
            out, carry = [], 0
            for symbol in expected:
                carry, digit = divmod(symbol + carry, base)
                out.append(digit)
            if carry:
                out.append(carry)
            before = tile_arena_metrics()["intern_misses"]
            with monkeypatch.context() as patch:
                patch.setattr(
                    tiles,
                    "source_span",
                    lambda *a, **k: pytest.fail("future exact tape"),
                )
                assert tuple(
                    index.direct_powered_point(i) for i in range(len(out))
                ) == tuple(out)
                assert index.direct_active_width() == len(out)
            assert tile_arena_metrics()["intern_misses"] == before
            m = index.metrics()
            assert m.resource_audit_complete == 1
            assert m.forbidden_future_payloads == m.resource_accounting_mismatch == 0


def test_zero_budget_rejects_before_source_geometry_or_branch_work() -> None:
    ledger = ResourceLedger(max_cache_entries=0)
    before = tile_arena_metrics()["intern_misses"]
    with pytest.raises(BlockContextBudgetExceeded):
        HashLifeBlockIndex(finite(), (2,), logical_length=3, ledger=ledger)
    assert ledger.entries == ledger.nodes == 0
    assert ledger.counters == {}
    assert tile_arena_metrics()["intern_misses"] == before
    for cls in (ReverseAddPoweredTerm, PoweredCollatzTerm):
        with pytest.raises(BlockContextBudgetExceeded):
            cls(27, 64, max_cache_entries=0)


def test_shared_immutable_source_interning_is_weak_and_ids_are_not_recycled() -> None:
    node = join(leaf(398991), leaf(398992))
    identity = node.node_id
    reference = weakref.ref(node)
    del node
    gc.collect()
    assert reference() is None
    assert join(leaf(398991), leaf(398992)).node_id > identity


@pytest.mark.validation  # Cross-family deep-query isolation workload.
def test_unrelated_index_work_cannot_change_an_existing_index_metrics() -> None:
    first = ReverseAddPoweredTerm(196, 32)
    first.digit(0)
    before = first.metrics()
    second = PoweredCollatzTerm(27, 64)
    second.digit(3)
    after = first.metrics()
    for name in (
        "resource_ledger_entries",
        "resource_ledger_nodes",
        "composition_requests",
        "spacetime_primitive_field_steps",
        "symbolic_port_queries",
    ):
        assert getattr(before, name) == getattr(after, name)


def test_uncertified_huge_blank_geometry_never_expands_to_a_future_word() -> None:
    effect = compose_block_effects(
        finite(), DigitNormalizeBlockEffect(10), budget=BlockContextBudget()
    )
    index = HashLifeBlockIndex(effect, (2,), logical_length=1 << 100)
    assert index.direct_powered_point((1 << 100) - 1) == 19
    assert index.direct_active_width() == 1
    assert index.direct_powered_point(0) == 2
    metrics = index.metrics()
    assert metrics.forbidden_future_payloads == 0
    assert metrics.retained_unbounded_future_integers == 0
    assert metrics.resource_audit_complete == 1
    assert metrics.maximum_arithmetic_bits <= 64


def test_explicit_block_application_preserves_compiled_program_output_type() -> None:
    from devtools.proofs.block_power import apply_block_power

    term = ReverseAddPoweredTerm(196, 4)
    expected = term.seed_pair
    for _ in range(3):
        expected, _ = pair_step(expected, 10)
    assert term.pair_power is not None
    result = apply_block_power(term.pair_power, term.seed_pair)
    assert result.values == expected
    assert isinstance(result.values, tuple)
    assert result.intermediate_pair_words == 0
    assert result.runtime_stats["explicitly_materialized_endpoints"] == 1


def test_custom_atom_cannot_alias_a_warm_supported_kernel_key() -> None:
    from number_compiler.hashlife.actions.lazy_compiler import (
        LazyCompiler,
        UnsupportedInterfaceError,
    )

    compiler = LazyCompiler(ResourceLedger())
    compiler.atom(BaseBlockEffect(10))

    class Impostor(BaseBlockEffect):
        def emit(self, left: object, symbol: object, right: object) -> int:
            return 0

    before = compiler.ledger.snapshot()
    with pytest.raises(UnsupportedInterfaceError):
        compiler.atom(Impostor(10))
    assert compiler.ledger.entries == before.entries
    assert compiler.ledger.nodes == before.nodes
