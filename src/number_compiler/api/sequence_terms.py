"""Shared compact term/projection constructors used by sequence families."""

from __future__ import annotations

from math import gcd
from typing import TYPE_CHECKING

from number_compiler.api.sequence_types import FactoredRadixProjection, RadixTermMetrics
from number_compiler.arithmetic.automata.program_word import (
    CanonicalWord,
    from_runs,
    word_metrics,
)
from number_compiler.arithmetic.fields.digit_formula import DigitSpec
from number_compiler.arithmetic.fields.radix import digits_lsd, symbol_runs
from number_compiler.arithmetic.fields.symbolic_extent import (
    Extent,
    extent_description_bits,
)
from number_compiler.arithmetic.formula.formula import (
    FormulaArena,
    FormulaRoot,
    formula_metrics,
)
from number_compiler.arithmetic.polynomials.primary_jet import (
    PrimaryJetBlock,
    primary_jet_from_runs,
    primary_jet_from_word,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.fields.congruence_automaton import (
        FactoredPrimeAutomaton,
    )


def factored_word_projection(
    word: CanonicalWord, radix: int, automaton: FactoredPrimeAutomaton
) -> FactoredRadixProjection:
    # Keep packed prime machinery off the ordinary symbolic-word import path.
    # The factor projection is an explicitly requested theorem/diagnostic view.
    from number_compiler.arithmetic.fields.congruence_automaton import (
        compile_word_morphism,
    )

    morphism = compile_word_morphism(automaton.moduli, word, radix=int(radix))
    state = morphism.apply(automaton.zero())
    calls = len(automaton.moduli)
    noncoprime = 0
    witness = None
    from number_compiler.sequences.prime.set import smallest_factor

    for residue, modulus in zip(state.residues, automaton.moduli):
        common = gcd(int(residue), int(modulus))
        if common <= 1:
            continue
        noncoprime += 1
        if witness is None:
            proper = smallest_factor(common)
            witness = int(common if proper is None else proper)
    return FactoredRadixProjection(
        automaton.wheel.limit,
        automaton.wheel.group_count,
        automaton.wheel.total_group_bits,
        state.residues,
        morphism.compositions,
        morphism.description_bits,
        calls,
        noncoprime,
        witness,
    )


def radix_term(
    index: int, value: int, radix: int, *, formula_root: FormulaRoot | None = None
) -> RadixTermMetrics:
    digits = digits_lsd(value, radix)
    runs = symbol_runs(digits)
    word = from_runs(runs)
    wm = word_metrics(word)
    if formula_root is None:
        fnodes = fbits = 0
    else:
        fm = formula_metrics(formula_root)
        fnodes = int(fm["nodes"])
        fbits = int(fm["description_bits"])
    jet = primary_jet_from_runs(runs, degree=4, modulus=32)
    return RadixTermMetrics(
        int(index),
        int(radix),
        len(digits),
        int(wm["runs"]),
        int(wm["nodes"]),
        int(wm["description_bits"]),
        fnodes,
        fbits,
        int(value),
        jet,
    )


def formula_term(
    index: int,
    radix: int,
    formula_root: FormulaRoot,
    *,
    arena: FormulaArena,
    digit_spec: DigitSpec,
    diagnostics: bool,
) -> RadixTermMetrics:
    if diagnostics:
        from number_compiler.arithmetic.fields.digit_formula import root_to_int

        return radix_term(
            int(index),
            root_to_int(arena, formula_root, digit_spec),
            int(radix),
            formula_root=formula_root,
        )
    fm = formula_metrics(formula_root)
    return RadixTermMetrics(
        int(index),
        int(radix),
        int(formula_root.width),
        0,
        0,
        0,
        int(fm["nodes"]),
        int(fm["description_bits"]),
        None,
        None,
        None,
    )


def symbolic_word_term(
    index: int,
    radix: int,
    word: CanonicalWord,
    *,
    factored_automaton: FactoredPrimeAutomaton | None = None,
    diagnostics: bool = False,
) -> RadixTermMetrics:
    wm = word_metrics(word)
    jet = primary_jet_from_word(word, degree=4, modulus=32) if diagnostics else None
    projection = (
        None
        if factored_automaton is None
        else factored_word_projection(word, radix, factored_automaton)
    )
    return RadixTermMetrics(
        int(index),
        int(radix),
        int(word.length),
        int(wm["runs"]),
        int(wm["nodes"]),
        int(wm["description_bits"]),
        0,
        0,
        None,
        jet,
        projection,
    )


def symbolic_sparse_term(
    index: int,
    radix: int,
    width: Extent,
    *,
    runs: int,
    extent_parameters: tuple[Extent, ...],
    diagnostics_jet: PrimaryJetBlock | None = None,
) -> RadixTermMetrics:
    """Build a sparse exact radix source without lowering symbolic extents.

    ``extent_parameters`` are the algebraic run/boundary parameters retained by
    the source program.  Their descriptor charge is based on the symbolic
    parameter, not the represented integer width.
    """
    run_count = int(runs)
    if run_count <= 0:
        raise ValueError(run_count)
    param_bits = sum(extent_description_bits(v) for v in extent_parameters)
    # Charge symbols, radix, run tags and references conservatively.  The exact
    # constant is unimportant; dependence on every retained algebraic parameter
    # is explicit and O(description size).
    description = (
        param_bits
        + max(1, int(radix).bit_length())
        + run_count * (max(1, int(radix - 1).bit_length()) + 2)
        + max(1, run_count.bit_length()) * max(0, run_count - 1)
    )
    return RadixTermMetrics(
        int(index),
        int(radix),
        width,
        run_count,
        max(1, 2 * run_count - 1),
        int(description),
        0,
        0,
        None,
        diagnostics_jet,
        None,
    )


__all__ = [
    "factored_word_projection",
    "formula_term",
    "radix_term",
    "symbolic_sparse_term",
    "symbolic_word_term",
]
