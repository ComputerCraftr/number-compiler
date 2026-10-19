"""Store-free collatz compilation operations."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.api.sequence_terms import (
    formula_term,
)
from number_compiler.api.sequence_types import (
    CollatzCompilation,
    CollatzRawFieldQuotient,
    CollatzSequenceSpec,
)
from number_compiler.arithmetic.fields.digit_formula import DigitSpec
from number_compiler.arithmetic.fields.radix import symbol_runs
from number_compiler.projection.collatz_orbits.binary import collatz_orbit_formulas
from number_compiler.sequences.collatz.pair import (
    CollatzValuationState,
)
from number_compiler.sequences.collatz.radix import (
    collatz_orbit_formulas_local_composite_radix,
    collatz_orbit_formulas_ternary,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.frame import CollatzFutureValuationRoot


def compile_collatz(
    spec: CollatzSequenceSpec, *, diagnostics: bool
) -> CollatzCompilation:
    if spec.radix == 2:
        arena, rows = collatz_orbit_formulas(
            spec.seed,
            max_steps=spec.max_steps,
            stop_at_one=True,
            materialize_values=diagnostics,
        )
    elif spec.radix == 3:
        arena, rows = collatz_orbit_formulas_ternary(
            spec.seed,
            max_steps=spec.max_steps,
            stop_at_one=True,
            materialize_values=diagnostics,
        )
    else:
        arena, rows = collatz_orbit_formulas_local_composite_radix(
            spec.seed,
            radix=spec.radix,
            max_steps=spec.max_steps,
            stop_at_one=True,
            materialize_values=diagnostics,
        )
    terms = tuple(
        formula_term(
            row.index,
            spec.radix,
            row.root,
            arena=arena,
            digit_spec=DigitSpec(spec.radix),
            diagnostics=diagnostics,
        )
        for row in rows
    )

    # Auxiliary Collatz theorem channels are diagnostic views, not parallel
    # production traversals.  When requested, the radix-4 sentinel orbit is
    # the single accelerated traversal: its valuations feed both the exact
    # valuation slab and the normalized parity sensitivity.
    radial = None
    raw_quotient = None
    valuation_projection = None
    valuation_state_classes = valuation_state_max_bits = 0
    future_valuation_roots: tuple[CollatzFutureValuationRoot, ...] = ()
    if diagnostics:
        from number_compiler.sequences.collatz.frame import (
            CollatzFutureValuationRoot,
        )
        from number_compiler.sequences.collatz.pair import (
            valuation_projection_from_runs,
        )
        from number_compiler.sequences.collatz.parity import (
            collatz_parity_slab,
            collatz_parity_word_from_valuations,
            collatz_slab_padic3,
        )
        from number_compiler.sequences.collatz.raw_field import (
            collatz_sentinel_orbit,
        )

        raw_steps = collatz_sentinel_orbit(
            spec.seed, base=4, max_odd_steps=spec.max_steps
        )
        valuations = tuple(int(step.valuation) for step in raw_steps)
        raw_quotient = CollatzRawFieldQuotient(
            4,
            1,
            len(raw_steps),
            sum(valuations),
            sum(step.increases for step in raw_steps),
            sum(step.nonincreasing for step in raw_steps),
            sum(step.valuation_digit_checks for step in raw_steps),
            sum(step.source_width for step in raw_steps),
            sum(step.stripped_digits for step in raw_steps),
            sum(step.source_width - step.stripped_digits for step in raw_steps),
            max((step.scalar_carry_peak for step in raw_steps), default=0),
        )
        valuation_projection = valuation_projection_from_runs(symbol_runs(valuations))
        future_valuation_roots = (
            CollatzFutureValuationRoot(0),
            CollatzFutureValuationRoot(1),
        )
        valuation_states = tuple(CollatzValuationState(k) for k in valuations)
        valuation_state_classes = len(
            {state.canonical_key for state in valuation_states}
        )
        valuation_state_max_bits = max(
            (state.description_bits for state in valuation_states), default=0
        )
        initial_even_steps = 0
        initial_value = int(spec.seed)
        while initial_value > 1 and not (initial_value & 1):
            initial_value >>= 1
            initial_even_steps += 1
        # The accelerated valuation word covers exactly the normalized-H
        # orbit through the first arrival at 1.  The old compiler instead
        # extended Q past that terminal point into the artificial 1<->2
        # cycle merely because the physical E/O orbit had more rows.
        normalized_steps = min(
            int(spec.max_steps), initial_even_steps + sum(valuations)
        )
        if normalized_steps:
            parity = collatz_parity_word_from_valuations(
                spec.seed, valuations, normalized_steps
            )
            radial = collatz_slab_padic3(
                collatz_parity_slab(parity, normalized_steps), precision=8
            ).radial_quotient
    return CollatzCompilation(
        spec,
        terms,
        (tuple(row.branch for row in rows) if diagnostics else ()),
        radial,
        raw_quotient,
        valuation_projection,
        valuation_state_classes,
        valuation_state_max_bits,
        future_valuation_roots,
    )
