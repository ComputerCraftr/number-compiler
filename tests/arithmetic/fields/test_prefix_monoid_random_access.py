from __future__ import annotations

from math import ceil, log2
from typing import Never

import pytest

from number_compiler.api.number_api import NumberCompiler
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.fields.digit_formula import (
    DigitSpec,
    compile_digit_transducer,
    digit_root_from_int,
    synthesize_multiply_add,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.formula.formula import (
    FormulaArena,
    FormulaRoot,
    RadixSpec,
)
from number_compiler.hashlife.execution.evaluator import materialize_values
from number_compiler.sequences.reverse_add.digits import reverse_add_orbit_formulas
from number_compiler.sequences.reverse_add.domain import ReverseAddSpatialIndex


def test_reverse_add_domain_index_matches_exact_pair_and_digit_orbit() -> None:
    arena, digit_roots, pair_roots = reverse_add_orbit_formulas(196, 18, base=10)
    spec = RadixSpec(10)
    for step, pair in enumerate(pair_roots[:-1]):
        index = ReverseAddSpatialIndex.build(arena, pair, spec)
        source = materialize_values(pair)
        target, growth = pair_step(source, 10)
        assert index.growth == growth
        assert index.target_width == len(target)
        assert index.prefix_stages == ceil(log2(len(source))) if len(source) > 1 else 0
        assert tuple(index.source_value_at(i) for i in range(len(source))) == source
        assert tuple(index.next_value_at(i) for i in range(len(target))) == target
        assert tuple(
            index.next_digit_at(i) for i in range(digit_roots[step + 1].width)
        ) == materialize_values(digit_roots[step + 1])
        assert tuple(
            index.next_symbol_at(i).relation for i in range(len(target))
        ) == tuple(-1 if v < 9 else 1 if v > 9 else 0 for v in target)


def test_reverse_add_random_digit_api_does_not_build_final_digit_formula(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.reverse_add.digits as reverse_digits

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("final complete digit formula was constructed")

    monkeypatch.setattr(reverse_digits, "next_digit_formula", forbidden)
    compiler = NumberCompiler()
    expected = digits_lsd(52514, 10)
    for i, digit in enumerate(expected):
        assert compiler.project_digit("196", 5, i) == digit


def test_collatz_digit_transducer_uses_shared_prefix_random_access() -> None:
    spec = DigitSpec(2)
    arena = FormulaArena()
    root = digit_root_from_int((1 << 127) + (1 << 73) + 27, arena, spec)
    transducer = synthesize_multiply_add(2, 3, 1)
    compiled = compile_digit_transducer(arena, root, spec, transducer)
    assert compiled.prefix_projection.stages == ceil(log2(root.width))

    # Random-access outputs and state projections agree with the full exact word.
    values = materialize_values(compiled.output)
    for i in (0, 1, 7, 31, 63, 95, root.width - 1):
        assert compiled.output_digit_at(arena, i) == values[i]
        assert compiled.incoming_state_at(arena, i) in transducer.states
        assert compiled.outgoing_state_at(arena, i) in transducer.states


def test_prefix_stage_count_is_logarithmic_not_spatial_width() -> None:
    spec = RadixSpec(10)
    for width in (2, 3, 8, 17, 65, 257):
        # Symmetric coefficient word with a mix of LT/EQ/GT domains.
        half = [7 + (i % 5) for i in range((width + 1) // 2)]
        values = tuple((half + half[-2::-1]) if width % 2 else (half + half[::-1]))
        values = values[:width]
        arena = FormulaArena()
        from number_compiler.arithmetic.formula.formula import root_from_values

        pair = root_from_values(values, arena, spec)
        index = ReverseAddSpatialIndex.build(arena, pair, spec)
        assert index.prefix_stages == (width - 1).bit_length()
        # Querying the far edge returns the same terminal carry as a scalar scan.
        carry = 0
        for value in values:
            carry = int(value + carry >= 10)
        assert index.carry_boundary(width) == carry


def test_collatz_explicit_parity_prefix_uses_cached_block_monoid() -> None:
    from number_compiler.sequences.collatz.parity import (
        CollatzParityCursor,
        advance_collatz_parity,
        collatz_parity_prefix_index,
        collatz_parity_word,
    )

    width = 4096
    word = collatz_parity_word(27, width)
    first = collatz_parity_prefix_index(word, width)
    second = collatz_parity_prefix_index(word, width)
    assert first is second
    assert first.block_count == 64
    result = advance_collatz_parity(CollatzParityCursor(word, width), 4096)
    assert result.rank_bits_scanned <= 64
    assert result.rank_queries <= 2 * width.bit_length()


def test_prefix_predicate_selects_first_failure_without_linear_point_scan() -> None:
    from number_compiler.arithmetic.carry.prefix_monoid import (
        compile_formula_prefix_predicate,
    )
    from number_compiler.arithmetic.fields.digit_formula import (
        digit_root_from_values,
        digit_value_masks,
    )

    spec = DigitSpec(4)
    arena = FormulaArena()
    # radix-4 Collatz sentinel is 1; place the first hole far into the word.
    values = (1,) * 256 + (3, 2, 0)
    root = digit_root_from_values(values, arena, spec)
    predicate = digit_value_masks(arena, root, spec)[1]
    projection = compile_formula_prefix_predicate(arena, predicate)
    before = arena.metadata_counter("prefix_predicate_select_probes")
    assert projection.first_false(arena) == 256
    probes = arena.metadata_counter("prefix_predicate_select_probes") - before
    assert projection.stages == (len(values) - 1).bit_length()
    # Binary selection probes only O(log width) prefix coordinates; no scan of
    # the preceding 256 sentinel digits occurs.
    assert probes <= (len(values) - 1).bit_length() + 1


def test_collatz_sentinel_formula_endpoint_uses_prefix_select_not_sentinel_scan(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields import digit_formula
    from number_compiler.arithmetic.fields.digit_formula import digit_root_from_values
    from number_compiler.sequences.collatz.raw_field import (
        accelerated_collatz_sentinel_formula_step,
    )

    spec = DigitSpec(4)
    arena = FormulaArena()
    root = digit_root_from_values((1,) * 256 + (3, 2), arena, spec)
    original = digit_formula.closed_digit_at
    calls = 0

    def counted(arena: FormulaArena, root: FormulaRoot, position: int) -> int:
        nonlocal calls
        calls += 1
        return original(arena, root, position)

    monkeypatch.setattr(digit_formula, "closed_digit_at", counted)
    _out, valuation, stripped, local = accelerated_collatz_sentinel_formula_step(
        arena, root, base=4
    )
    assert stripped == 256
    assert valuation == 2 * 256 + local
    # Endpoint discovery itself does not scan q digits.  The constant extra
    # queries belong to the bounded local divide/remainder path after the hole.
    assert calls <= 3
