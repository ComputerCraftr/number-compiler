from __future__ import annotations

import random
from typing import Never

import pytest

from number_compiler.arithmetic.fields.digit_formula import closed_digit_at
from number_compiler.arithmetic.formula.derived import successor
from number_compiler.arithmetic.formula.formula import FormulaArena, root_from_values
from number_compiler.arithmetic.formula.types import RadixSpec
from number_compiler.hashlife.actions.native_power import (
    compile_native_two_step,
    native_two_step,
    native_two_step_digits,
    native_two_step_reset_sets,
    native_two_step_value_sets,
)
from number_compiler.hashlife.execution.evaluator import materialize_values


def reference_successor(full: tuple[int, ...], base: int) -> tuple[int, ...]:
    d = len(full)
    L = [0] * (d + 1)
    for i, s in enumerate(full):
        L[i + 1] = int(s + L[i] >= base)
    R = [L[d - i] for i in range(d + 1)]
    growth = L[d]
    if not growth:
        out = [
            2 * full[i] + L[i] + R[i + 1] - base * (L[i + 1] + R[i]) for i in range(d)
        ]
    else:
        out = [0] * (d + 1)
        out[0] = full[0] + 1 - base * L[1]
        out[d] = out[0]
        for i in range(1, d):
            out[i] = full[i] + full[i - 1] + L[i] + R[i] - base * (L[i + 1] + R[i - 1])
    assert out == out[::-1]
    return tuple(out)


def normalize_pair_digits(full: tuple[int, ...], base: int) -> tuple[int, ...]:
    carry = 0
    out = []
    for s in full:
        z = s + carry
        out.append(z % base)
        carry = z // base
    if carry:
        out.append(carry)
    return tuple(out)


def symmetric_word(rng: random.Random, base: int, width: int) -> tuple[int, ...]:
    half = [rng.randrange(2 * base - 1) for _ in range((width + 1) // 2)]
    if half[0] == 0:
        half[0] = 1
    return tuple(half + (half[-2::-1] if width & 1 else half[::-1]))


def test_native_two_step_matches_two_successors_random_bases() -> None:
    rng = random.Random(0x1962)
    for base in range(2, 18):
        spec = RadixSpec(base)
        for _ in range(40):
            values = symmetric_word(rng, base, rng.randint(1, 18))
            expected1 = reference_successor(values, base)
            expected2 = reference_successor(expected1, base)
            arena = FormulaArena()
            source = root_from_values(values, arena, spec)
            compiled = compile_native_two_step(arena, source, spec)
            assert materialize_values(compiled.pair) == expected2
            assert compiled.first_growth == len(expected1) - len(values)
            assert compiled.second_growth == len(expected2) - len(expected1)
            assert compiled.pair.width == len(expected2)


def test_native_two_step_exact_digit_projector() -> None:
    rng = random.Random(0xA2196)
    for base in (2, 3, 5, 7, 10, 16):
        spec = RadixSpec(base)
        for _ in range(30):
            values = symmetric_word(rng, base, rng.randint(1, 16))
            tau = reference_successor(values, base)
            expected_digits = normalize_pair_digits(tau, base)
            arena = FormulaArena()
            source = root_from_values(values, arena, spec)
            digits = native_two_step_digits(arena, source, spec)
            actual = tuple(
                closed_digit_at(arena, digits, i) for i in range(digits.width)
            )
            assert actual == expected_digits


def test_native_second_reset_sets_are_fully_substituted_tau_classes() -> None:
    rng = random.Random(0x2CA77)
    for base in (2, 3, 7, 10, 16):
        spec = RadixSpec(base)
        for _ in range(20):
            values = symmetric_word(rng, base, rng.randint(1, 14))
            tau = reference_successor(values, base)
            arena = FormulaArena()
            source = root_from_values(values, arena, spec)
            less, equal, greater = native_two_step_reset_sets(arena, source, spec)
            for i, coeff in enumerate(tau):
                got = (
                    arena.eval_closed_bit(less, i),
                    arena.eval_closed_bit(equal, i),
                    arena.eval_closed_bit(greater, i),
                )
                expected = (coeff < base - 1, coeff == base - 1, coeff > base - 1)
                assert got == tuple(map(int, expected))


def test_native_two_step_value_sets_are_exact_and_disjoint() -> None:
    spec = RadixSpec(10)
    values = (7, 18, 7)
    arena = FormulaArena()
    source = root_from_values(values, arena, spec)
    pair = native_two_step(arena, source, spec)
    expected = materialize_values(pair)
    zsets = native_two_step_value_sets(arena, source, spec)
    for i, value in enumerate(expected):
        hits = [w for w, mask in enumerate(zsets) if arena.eval_closed_bit(mask, i)]
        assert hits == [value]


def test_native_two_step_does_not_construct_or_cache_first_successor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A hard regression check for the distinction this primitive exists to make:
    # successor() must not be reachable from native T^2.
    import number_compiler.arithmetic.formula.derived as derived

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("native T^2 called successor()")

    monkeypatch.setattr(derived, "successor", forbidden)
    spec = RadixSpec(10)
    arena = FormulaArena()
    source = root_from_values((7, 18, 7), arena, spec)
    compiled = compile_native_two_step(arena, source, spec)
    assert materialize_values(compiled.pair) == reference_successor(
        reference_successor((7, 18, 7), 10), 10
    )
    # The only native-T2 metadata entry retains the completed result, not tau/K.
    native_keys = [
        key for key in arena._metadata if key and key[0] == "native-two-step"
    ]
    assert len(native_keys) == 1
    assert arena._metadata[native_keys[0]] is compiled
    assert not any(key and str(key[0]).startswith("tau") for key in arena._metadata)
    assert arena._derived == {}  # no source/tau carry identity is installed


def test_native_two_step_and_composed_reference_are_extensionally_identical() -> None:
    spec = RadixSpec(10)
    values = (7, 18, 7)

    native_arena = FormulaArena()
    native_source = root_from_values(values, native_arena, spec)
    native = native_two_step(native_arena, native_source, spec)

    composed_arena = FormulaArena()
    composed_source = root_from_values(values, composed_arena, spec)
    composed = successor(
        composed_arena, successor(composed_arena, composed_source, spec), spec
    )

    assert materialize_values(native) == materialize_values(composed)
    # Native construction deliberately avoids the non-semantic intermediate/final
    # BlockSummary work done by successor replay, so its arena footprint is no larger.
    assert native_arena.unique_nodes <= composed_arena.unique_nodes


def test_native_four_step_matches_four_successors_random_bases() -> None:
    from number_compiler.hashlife.actions.native_power import compile_native_four_step

    rng = random.Random(0x41964)
    for base in range(2, 14):
        spec = RadixSpec(base)
        for _ in range(25):
            values = symmetric_word(rng, base, rng.randint(1, 16))
            expected = values
            widths = [len(values)]
            growths = []
            for _step in range(4):
                nxt = reference_successor(expected, base)
                growths.append(len(nxt) - len(expected))
                widths.append(len(nxt))
                expected = nxt
            arena = FormulaArena()
            source = root_from_values(values, arena, spec)
            compiled = compile_native_four_step(arena, source, spec)
            assert materialize_values(compiled.pair) == expected
            assert compiled.growths == tuple(growths)
            assert compiled.widths == tuple(widths)


def test_native_four_step_is_not_composed_from_native_t2_or_successor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.formula.derived as derived
    import number_compiler.hashlife.actions.native_power as native_power

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("native T4 used a semantic temporal step")

    monkeypatch.setattr(derived, "successor", forbidden)
    monkeypatch.setattr(native_power, "native_two_step", forbidden)
    monkeypatch.setattr(native_power, "compile_native_two_step", forbidden)

    spec = RadixSpec(10)
    arena = FormulaArena()
    source = root_from_values((7, 18, 7), arena, spec)
    actual = native_power.native_four_step(arena, source, spec)
    expected: tuple[int, ...] = (7, 18, 7)
    for _ in range(4):
        expected = reference_successor(expected, 10)
    assert materialize_values(actual) == expected
    native_keys = [
        key for key in arena._metadata if key and key[0] == "native-four-step"
    ]
    assert len(native_keys) == 1
    assert not any(key and key[0] == "native-two-step" for key in arena._metadata)
    assert arena._derived == {}


def test_native_four_step_matches_t2_squared_but_uses_no_intermediate_root_cache() -> (
    None
):
    from number_compiler.arithmetic.formula.formula import formula_metrics
    from number_compiler.hashlife.actions.native_power import native_four_step

    spec = RadixSpec(10)
    values = (7, 18, 7)

    direct_arena = FormulaArena()
    direct_source = root_from_values(values, direct_arena, spec)
    direct = native_four_step(direct_arena, direct_source, spec)

    square_arena = FormulaArena()
    square_source = root_from_values(values, square_arena, spec)
    squared = native_two_step(
        square_arena, native_two_step(square_arena, square_source, spec), spec
    )

    assert materialize_values(direct) == materialize_values(squared)
    assert formula_metrics(direct) == formula_metrics(squared)
    direct_keys = [
        k for k in direct_arena._metadata if k and k[0] == "native-four-step"
    ]
    square_keys = [k for k in square_arena._metadata if k and k[0] == "native-two-step"]
    assert len(direct_keys) == 1
    assert len(square_keys) == 2


def test_native_four_step_digit_projector() -> None:
    from number_compiler.hashlife.actions.native_power import native_four_step_digits

    rng = random.Random(0xD4196)
    for base in (2, 3, 5, 10, 16):
        spec = RadixSpec(base)
        for _ in range(15):
            values = symmetric_word(rng, base, rng.randint(1, 14))
            s = values
            for _step in range(3):
                s = reference_successor(s, base)
            expected_digits = normalize_pair_digits(s, base)
            arena = FormulaArena()
            source = root_from_values(values, arena, spec)
            digits = native_four_step_digits(arena, source, spec)
            actual = tuple(
                closed_digit_at(arena, digits, i) for i in range(digits.width)
            )
            assert actual == expected_digits


def test_general_native_power_matches_reference_without_semantic_intermediate_roots(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.formula.derived as derived
    import number_compiler.hashlife.actions.native_power as native_module
    from number_compiler.hashlife.actions.native_power import compile_native_power

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("general native power used a semantic temporal primitive")

    monkeypatch.setattr(derived, "successor", forbidden)
    monkeypatch.setattr(native_module, "native_two_step", forbidden)
    monkeypatch.setattr(native_module, "compile_native_two_step", forbidden)
    monkeypatch.setattr(native_module, "native_four_step", forbidden)
    monkeypatch.setattr(native_module, "compile_native_four_step", forbidden)

    rng = random.Random(0x196B17)
    for base in (2, 3, 5, 10, 16):
        spec = RadixSpec(base)
        for steps in range(0, 10):
            values = symmetric_word(rng, base, rng.randint(1, 12))
            expected = values
            widths = [len(values)]
            growths = []
            for _ in range(steps):
                nxt = reference_successor(expected, base)
                growths.append(len(nxt) - len(expected))
                widths.append(len(nxt))
                expected = nxt
            arena = FormulaArena()
            source = root_from_values(values, arena, spec)
            compiled = compile_native_power(arena, source, steps, spec)
            assert materialize_values(compiled.pair) == expected
            assert compiled.growths == tuple(growths)
            assert compiled.widths == tuple(widths)
            if steps:
                keys = [k for k in arena._metadata if k and k[0] == "native-power"]
                assert len(keys) == 1
                assert not any(
                    k and k[0] in {"native-two-step", "native-four-step"}
                    for k in arena._metadata
                )
                assert arena._derived == {}


def test_general_native_power_digit_projector() -> None:
    from number_compiler.hashlife.actions.native_power import native_power_digits

    rng = random.Random(0x196D1617)
    for base in (2, 3, 7, 10, 16):
        spec = RadixSpec(base)
        for steps in range(1, 8):
            values = symmetric_word(rng, base, rng.randint(1, 10))
            pair = values
            expected_digits = None
            for _ in range(steps):
                expected_digits = normalize_pair_digits(pair, base)
                pair = reference_successor(pair, base)
            assert expected_digits is not None
            arena = FormulaArena()
            source = root_from_values(values, arena, spec)
            digits = native_power_digits(arena, source, steps, spec)
            actual = tuple(
                closed_digit_at(arena, digits, i) for i in range(digits.width)
            )
            assert actual == expected_digits


def test_general_native_power_is_guard_ineligible_until_growth_is_symbolic() -> None:
    from number_compiler.arithmetic.automata.guard import (
        JumpAudit,
        JumpGuardViolation,
        powered_jump_scope,
    )
    from number_compiler.hashlife.actions.native_power import (
        native_power as native_power_root,
    )

    arena = FormulaArena()
    spec = RadixSpec(10)
    source = root_from_values((7, 18, 7), arena, spec)
    with pytest.raises(JumpGuardViolation):
        with powered_jump_scope(JumpAudit()):
            native_power_root(arena, source, 3, spec)
