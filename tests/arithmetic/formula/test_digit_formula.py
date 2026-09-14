from __future__ import annotations

from typing import Never

import pytest

from number_compiler.arithmetic.fields.digit_formula import (
    DigitSpec,
    digit_root_from_int,
    divide_formula,
    multiply_add_formula,
    root_to_int,
)
from number_compiler.arithmetic.formula.formula import FormulaArena
from number_compiler.arithmetic.formula.types import RadixSpec
from number_compiler.projection.collatz_orbits.binary import collatz_values
from number_compiler.resources.instrumentation import formula_radix_residue
from number_compiler.sequences.collatz.orbit import collatz_monoid_metrics
from number_compiler.sequences.reverse_add.digits import reverse_add_orbit_formulas


def _reverse_base(n: int, base: int) -> int:
    digits = []
    if n == 0:
        digits = [0]
    while n:
        n, d = divmod(n, base)
        digits.append(d)
    out = 0
    for d in digits:
        out = out * base + d
    return out


def test_generic_multiply_divide_monoid_formulas() -> None:
    for base in (2, 3, 5, 10, 16):
        spec = DigitSpec(base)
        for n in range(24):
            A = FormulaArena()
            r = digit_root_from_int(n, A, spec)
            out, _ = multiply_add_formula(A, r, spec, 3, 1)
            assert root_to_int(A, out, spec) == 3 * n + 1
            A = FormulaArena()
            r = digit_root_from_int(6 * n, A, spec)
            out, _ = divide_formula(A, r, spec, 6)
            assert root_to_int(A, out, spec) == n


def test_reverse_add_exact_digits_all_bases() -> None:
    for base in (2, 3, 5, 10, 16):
        for seed in (1, 7, 22, 196):
            A, digits, _pairs = reverse_add_orbit_formulas(seed, 8, base=base)
            spec = DigitSpec(base)
            n = seed
            assert root_to_int(A, digits[0], spec) == n
            for root in digits[1:]:
                n += _reverse_base(n, base)
                assert root_to_int(A, root, spec) == n


def test_collatz_exact_formula_orbits() -> None:
    expected_27 = (27, 82, 41, 124, 62, 31, 94, 47, 142, 71, 214)
    got = collatz_values(27, 10)
    assert got == expected_27
    vals = collatz_values(196, 100)
    assert vals[-1] == 1
    assert len(vals) - 1 == 26


def test_collatz_monoids_and_residue_instrumentation() -> None:
    metrics = collatz_monoid_metrics()
    assert metrics["multiply_3_add_1"]["states"] == 3
    assert metrics["multiply_3_add_1"]["transition_monoid"] == 8
    assert metrics["divide_2"]["states"] == 2
    assert metrics["divide_2"]["transition_monoid"] == 3

    A = FormulaArena()
    spec = DigitSpec(2)
    root = digit_root_from_int(27, A, spec)
    for m in (3, 4, 5, 7, 8, 9, 11, 16, 25, 27):
        assert formula_radix_residue(A, root, spec, 2, m) == 27 % m


def test_smb_formula_view_is_derived_not_duplicate_state() -> None:
    from number_compiler.arithmetic.fields.digit_formula import closed_digit_at
    from number_compiler.arithmetic.formula.smb_formula import smb_formula_view
    from number_compiler.sequences.reverse_add.digits import pair_root_from_integer

    A = FormulaArena()
    spec = RadixSpec(10)
    pair = pair_root_from_integer(196, A, spec)
    view = smb_formula_view(A, pair, spec)
    # pair(196) = (7,18,7); M = (<9, >9, <9) -> (0,2,0)
    assert tuple(closed_digit_at(A, view.domain, i) for i in range(3)) == (0, 2, 0)
    # Direct carry sequence 0 -> 1 -> 0 gives B=(0,1,1).
    assert tuple(closed_digit_at(A, view.border, i) for i in range(3)) == (0, 1, 1)


def test_transducer_state_renaming_canonicalizes_before_monoid_cache() -> None:
    from number_compiler.arithmetic.fields.digit_formula import (
        DigitTransducer,
        canonical_transducer_key,
        synthesize_function_monoid,
    )

    # Same two-state Mealy machine with unrelated external labels/order.
    t1 = DigitTransducer(
        2,
        (10, 20),
        10,
        {
            (10, 0): (10, 0),
            (10, 1): (20, 1),
            (20, 0): (10, 1),
            (20, 1): (20, 0),
        },
    )
    t2 = DigitTransducer(
        2,
        (7, 3),
        7,
        {
            (7, 0): (7, 0),
            (7, 1): (3, 1),
            (3, 0): (7, 1),
            (3, 1): (3, 0),
        },
    )
    assert canonical_transducer_key(t1) == canonical_transducer_key(t2)
    assert synthesize_function_monoid(t1) is synthesize_function_monoid(t2)


def test_smb_and_digit_compilation_cache_by_canonical_roots() -> None:
    from number_compiler.arithmetic.fields.digit_formula import (
        DigitSpec,
        compile_digit_transducer,
        digit_root_from_int,
        synthesize_multiply_add,
    )
    from number_compiler.arithmetic.formula.formula import FormulaArena
    from number_compiler.arithmetic.formula.smb_formula import smb_formula_view
    from number_compiler.arithmetic.formula.types import RadixSpec
    from number_compiler.sequences.reverse_add.digits import pair_root_from_integer

    A = FormulaArena()
    pair = pair_root_from_integer(196, A, RadixSpec(10))
    v1 = smb_formula_view(A, pair, RadixSpec(10))
    v2 = smb_formula_view(A, pair, RadixSpec(10))
    assert v1 is v2
    d = digit_root_from_int(27, A, DigitSpec(2))
    t = synthesize_multiply_add(2, 3, 1)
    c1 = compile_digit_transducer(A, d, DigitSpec(2), t)
    c2 = compile_digit_transducer(A, d, DigitSpec(2), t)
    assert c1 is c2


def test_canonical_output_relation_never_repopulates_tuple_cache() -> None:
    from number_compiler.arithmetic.automata.transducer import build_pair_step_bimachine
    from number_compiler.arithmetic.functions.residual import minimize_bimachine

    q = minimize_bimachine(build_pair_step_bimachine(10), cache_outputs=True).machine
    assert q.has_canonical_output and q.cached_outputs == 0
    for left_index in q.left.states[:4]:
        for r in q.right.states[:4]:
            for a in q.alphabet[:4]:
                q.emit(left_index, a, r)
    assert q.cached_outputs == 0


def test_next_reverse_add_digits_get_growth_from_summary_not_terminal_carry_evaluation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.reverse_add.digits import (
        next_digit_formula,
        pair_root_from_integer,
    )

    arena = FormulaArena()
    spec = RadixSpec(10)
    pair = pair_root_from_integer(196, arena, spec)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("terminal carry evaluation re-entered digit generation")

    monkeypatch.setattr(FormulaArena, "eval_closed_bit", forbidden)
    root = next_digit_formula(arena, pair, spec)
    # Building the symbolic next-digit formula succeeds without asking the
    # terminal carry bit; concrete evaluation is intentionally not attempted.
    assert root.width == 3


def test_growth_bit_compatibility_api_does_not_build_carry_scan(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.formula import derived
    from number_compiler.sequences.reverse_add.digits import pair_root_from_integer

    arena = FormulaArena()
    spec = RadixSpec(10)
    pair = pair_root_from_integer(196, arena, spec)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("carry_out entered growth-only query")

    monkeypatch.setattr(derived, "carry_out", forbidden)
    assert derived.growth_bit(arena, pair, spec) == 0
