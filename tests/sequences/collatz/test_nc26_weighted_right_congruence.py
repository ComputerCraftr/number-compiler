"""Independent weighted Myhill-Nerode unary classes and production binding."""

from __future__ import annotations

import json
import random
from collections.abc import Callable
from contextlib import redirect_stdout
from io import StringIO

import pytest

from number_compiler.api.cli import main
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.source_closed_port_action import SourceCongruence
from number_compiler.sequences.collatz.weighted_right_congruence import (
    WeightedRightBinding,
    WeightedRightClass,
    WeightedRightTransition,
    bind_weighted_right_class,
    exact_double_weight,
    transport_weighted_right_binding,
)
from tests.support.collatz_finite_trace import normalized_trace


def _physical(source: int, steps: int) -> tuple[int, int, int, int]:
    x, a, b, phase = source, 0, 0, 0
    for _ in range(steps):
        if x & 1:
            a += 2 * x + 1
            x = 3 * x + 1
            phase = 1
        else:
            x //= 2
            b += x
            phase = 0
    return x, a, b, phase


def test_exact_double_weight_handles_ordered_distinct_odd_even_actions() -> None:
    rng = random.Random(20261026)
    for _ in range(420):
        source = rng.randrange(1, 1 << 18)
        horizon = rng.randrange(0, 48)
        starts, current = normalized_trace(source, horizon)
        word = DyadicTerminalFieldAction.identity()
        for current_start in starts:
            bit = current_start & 1
            word = word.then(
                DyadicTerminalFieldAction.one_run(1)
                if bit
                else DyadicTerminalFieldAction.zero_run(1)
            )
        weight = exact_double_weight(word, source)
        # Independent normalized-step scalar accumulators.
        x, credit, debit = source, 0, 0
        for _ in range(horizon):
            if x & 1:
                credit += 2 * x + 1
                x = (3 * x + 1) // 2
                debit += x
            else:
                x //= 2
                debit += x
        assert (weight.added, weight.subtracted, weight.normalized_endpoint) == (
            credit,
            debit,
            x,
        )
        if current & 1:
            pending = exact_double_weight(word, source, phase=1)
            assert pending.added == credit + 2 * current + 1
            assert pending.subtracted == debit
            assert pending.physical_endpoint == 3 * current + 1


def test_source_independent_future_class_and_distinct_historical_weights() -> None:
    word = DyadicTerminalFieldAction.one_run(1)
    a = bind_weighted_right_class(word, 7, preflight=lambda _bits: None)
    b = bind_weighted_right_class(word, 23, preflight=lambda _bits: None)
    assert a.future is not b.future
    assert a.future == b.future
    assert a.future.key == b.future.key
    assert a.guard == b.guard == SourceCongruence(7, 16)
    ta = a.power(2, preflight=lambda _bits: None)
    tb = b.power(2, preflight=lambda _bits: None)
    assert ta.origin == tb.origin and ta.target == tb.target
    wa, wb = ta.evaluate(7), tb.evaluate(23)
    assert wa.added != wb.added
    assert wa.subtracted != wb.subtracted
    assert 7 + wa.added - wa.subtracted == wa.physical_endpoint
    assert 23 + wb.added - wb.subtracted == wb.physical_endpoint


def test_exit_guard_and_successor_class_transport() -> None:
    rng = random.Random(606)
    for _ in range(320):
        source = rng.randrange(1, 1 << 17)
        starts, _endpoint = normalized_trace(source, rng.randrange(1, 7))
        parity = tuple(value & 1 for value in starts)
        word = DyadicTerminalFieldAction.identity()
        for bit in parity:
            word = word.then(
                DyadicTerminalFieldAction.one_run(1)
                if bit
                else DyadicTerminalFieldAction.zero_run(1)
            )
        bound = bind_weighted_right_class(word, source, preflight=lambda _bits: None)
        n = bound.future.remaining
        if n is None:
            for q in (0, 1, 4):
                assert (
                    bound.power(q, preflight=lambda _bits: None)
                    .evaluate(source)
                    .normalized_endpoint
                    == source
                )
            with pytest.raises(ValueError, match="original-source guard"):
                bound.power(1, preflight=lambda _bits: None).evaluate(
                    source + 2 * word.source_modulus
                )
            continue
        assert n >= 1
        q = rng.randrange(n + 1)
        transition = bound.power(q, preflight=lambda _bits: None)
        weight = transition.evaluate(source)
        current_starts, current = normalized_trace(source, q * len(parity))
        assert tuple(value & 1 for value in current_starts) == parity * q
        assert current == weight.normalized_endpoint
        assert transition.target.remaining == n - q
        assert transition.target_guard.admits(current)
        with pytest.raises(ValueError, match="repetition exceeds"):
            bound.power(n + 1, preflight=lambda _bits: None)
        with pytest.raises(ValueError, match="original-source guard"):
            transition.evaluate(source + bound.guard.modulus // 2)


def test_foreign_port_punctures_cannot_transplant_future_class() -> None:
    word = DyadicTerminalFieldAction.one_run(1)
    valid = bind_weighted_right_class(
        word, 7, port_guard=SourceCongruence(7, 40), preflight=lambda _bits: None
    )
    assert valid.guard.admits(7)
    with pytest.raises(ValueError, match="conflicts"):
        bind_weighted_right_class(
            word, 7, port_guard=SourceCongruence(3, 16), preflight=lambda _bits: None
        )
    with pytest.raises(ValueError, match="original-source guard"):
        valid.power(1, preflight=lambda _bits: None).evaluate(23)


def test_public_binding_cannot_forge_a_longer_future_or_target() -> None:
    binding = bind_weighted_right_class(
        DyadicTerminalFieldAction.one_run(1),
        7,
        preflight=lambda _bits: None,
    )
    object.__setattr__(
        binding, "future", WeightedRightClass(binding.future.word, None, None)
    )
    with pytest.raises(ValueError, match="changed after source admission"):
        binding.power(1, preflight=lambda _bits: None)

    binding = bind_weighted_right_class(
        DyadicTerminalFieldAction.one_run(1),
        7,
        preflight=lambda _bits: None,
    )
    transition = binding.power(1, preflight=lambda _bits: None)
    object.__setattr__(
        transition,
        "target",
        WeightedRightClass(transition.target.word, 0, 0),
    )
    with pytest.raises(ValueError, match="changed after source issuance"):
        transition.evaluate(7)


def test_source_word_validation_is_not_replayed_for_validated_powers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    binding = bind_weighted_right_class(
        DyadicTerminalFieldAction.one_run(1),
        7,
        preflight=lambda _bits: None,
    )

    def forbidden_replay(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("validated source word was replayed during powering")

    monkeypatch.setattr(DyadicTerminalFieldAction, "one_run", forbidden_replay)
    first = binding.power(2, preflight=lambda _bits: None)
    endpoint = first.evaluate(7).normalized_endpoint
    successor = transport_weighted_right_binding(first, endpoint)
    second = successor.power(1, preflight=lambda _bits: None)
    assert second.evaluate(endpoint).normalized_endpoint == 26


def test_fixed_point_future_remains_pointed_to_its_issued_source() -> None:
    word = DyadicTerminalFieldAction.one_run(1).then(
        DyadicTerminalFieldAction.zero_run(1)
    )
    binding = bind_weighted_right_class(word, 1, preflight=lambda _bits: None)
    assert binding.future.remaining is None
    assert binding.pointed_source == binding.source_witness == 1
    with pytest.raises(TypeError, match="authenticated binding"):
        WeightedRightTransition.issue_weighted_right_transition(
            None,
            1,
            preflight=lambda _bits: None,
        )
    with pytest.raises(ValueError, match="repetition count"):
        WeightedRightTransition.issue_weighted_right_transition(
            binding,
            True,
            preflight=lambda _bits: None,
        )


def test_89_transition_reuses_the_issued_boundary_action(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz.boundary_macros import (
        admit_routed_boundary_macro_plan,
        select_admitted_boundary_macro,
    )

    source = 327679  # source + 1 is divisible by 2^16 and source ends in 9
    plan = admit_routed_boundary_macro_plan(source, 300)
    assert plan is not None and plan.repetitions == 16
    macro = select_admitted_boundary_macro(plan)
    binding = bind_weighted_right_class(
        DyadicTerminalFieldAction.one_run(1),
        source,
        preflight=lambda _bits: None,
    )

    def forbidden_power(
        _action: DyadicTerminalFieldAction,
        _count: int,
        **_kwargs: object,
    ) -> DyadicTerminalFieldAction:
        raise AssertionError("weighted transition rebuilt the issued 89 action")

    monkeypatch.setattr(DyadicTerminalFieldAction, "power", forbidden_power)
    transition = binding.power(
        plan.repetitions,
        action_authority=macro,
        preflight=lambda _bits: None,
    )
    weight = transition.evaluate(source)
    assert transition.action is macro.fields
    assert weight.normalized_endpoint == weight.physical_endpoint == macro.endpoint


def test_restored_affine_action_cannot_forge_weighted_output_sums() -> None:
    canonical = DyadicTerminalFieldAction.one_run(1)
    coefficients = list(canonical.coefficient_snapshot()[1:])
    coefficients[2] += 2
    forged = DyadicTerminalFieldAction.restore_untrusted_cache_payload(
        1, tuple(coefficients)
    )
    assert not forged.producer_issued and forged.certifies(7)
    assert (forged.gain * 7 + forged.offset) // (1 << forged.steps) == (
        canonical.endpoint(7)
    )
    with pytest.raises(ValueError, match="untrusted field coefficients"):
        forged.endpoint(7)

    with pytest.raises(TypeError, match="authenticated field action"):
        exact_double_weight(forged, 7)
    with pytest.raises(TypeError, match="issued normalized word"):
        bind_weighted_right_class(forged, 7, preflight=lambda _bits: None)


@pytest.mark.parametrize(
    "source,ticks",
    (
        (7, 0),
        (7, 8),
        (27, 3),
        (16, 16),
        (10 * (1 << 32) - 1, 64),
        (95 * (1 << 80) - 1, 160),
        (10 * (1 << 64) - 1, 220),
    ),
)
def test_production_cli_publishes_both_exact_accumulators(
    source: int, ticks: int
) -> None:
    endpoint, a, b, pending = _physical(source, ticks)
    output = StringIO()
    with redirect_stdout(output):
        assert (
            main(
                [
                    "collatz",
                    "--seed",
                    str(source),
                    "--nth",
                    str(ticks),
                    "--info",
                    "temporal.double-accumulator",
                    "--format",
                    "json",
                ],
                shared_cache=False,
            )
            == 0
        )
    packet = json.loads(output.getvalue())
    info = packet["info"]["temporal.double-accumulator"]
    assert int(packet["value"]) == endpoint
    assert info["added"] == a
    assert info["subtracted"] == b
    assert info["phase"] == pending
    assert info["source"] == source
    assert info["physical_endpoint"] == endpoint
    assert source + a - b == endpoint


def test_production_scheduler_really_consumes_long_weighted_power(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.collatz import (
        temporal_weighted_right_execution as route,
    )
    from number_compiler.sequences.collatz.temporal_run_quotient import (
        compile_collatz_temporal_run_quotient,
    )

    calls: list[
        tuple[tuple[str, tuple[int, int, int], int | None, int | None], int]
    ] = []
    original = route.bind_weighted_right_class

    def traced(
        word: DyadicTerminalFieldAction,
        source: int,
        *,
        port_guard: SourceCongruence | None = None,
        preflight: Callable[[int], None],
    ) -> WeightedRightBinding:
        binding = original(word, source, port_guard=port_guard, preflight=preflight)
        calls.append((binding.future.key, source))
        return binding

    monkeypatch.setattr(route, "bind_weighted_right_class", traced)
    seed = 95 * (1 << 80) - 1
    result = compile_collatz_temporal_run_quotient(
        seed, 1050, ledger=ResourceLedger(), include_joint_cocycle=True
    )
    assert calls, "default CLI did not consume the weighted future class"
    assert calls[0][1] == seed
    x, added, subtracted, _ = _physical(seed, 1050)
    assert result.endpoint == x
    assert result.joint_action is not None
    w = result.joint_action.double_accumulators()
    assert (w.added, w.subtracted) == (added, subtracted)
    calls.clear()
    # A short root query already has a faster certified complete-macro route.
    result = compile_collatz_temporal_run_quotient(seed, 160, ledger=ResourceLedger())
    assert result.endpoint == _physical(seed, 160)[0]
    assert not calls
