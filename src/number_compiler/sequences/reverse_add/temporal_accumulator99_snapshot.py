"""Authenticated snapshots for the reverse/add accumulator99 cache."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.input_validation import require_integer

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.temporal_accumulator99 import (
        PoweredAccumulator99,
    )


def accumulator99_snapshot(result: PoweredAccumulator99) -> tuple[object, ...]:
    """Reject malformed or foreign accumulator packets before cache reuse."""

    from .temporal_accumulator99 import (
        AccumulatorMooreState99,
        PoweredAccumulator99,
        RankOneAccumulatorAction99,
    )

    if type(result) is not PoweredAccumulator99:
        raise TypeError("mod-99 cache result has a foreign type")
    state = result.state
    if type(state) is not AccumulatorMooreState99:
        raise TypeError("mod-99 cache state has a foreign type")
    phase = require_integer(state.phase, "accumulator phase", 0, 1)
    state_a = require_integer(state.a, "first accumulator residue", 0, 98)
    state_b = require_integer(state.b, "second accumulator residue", 0, 98)
    AccumulatorMooreState99.__post_init__(state)

    action = result.action
    if type(action) is not RankOneAccumulatorAction99:
        raise TypeError("mod-99 cache action has a foreign type")
    multiplier = require_integer(action.multiplier, "rank-one multiplier", 0, 98)
    coupling = require_integer(action.coupling, "rank-one coupling", 0, 98)
    RankOneAccumulatorAction99.__post_init__(action)

    source_reverse = result.source_reverse_mod99
    if source_reverse is not None:
        source_reverse = require_integer(
            source_reverse, "source reverse residue", 0, 98
        )
    source_certified = result.source_certified
    if type(source_certified) is not bool or not source_certified:
        raise ValueError("mod-99 cache result lost source certification")
    absorbed = result.absorbed_mod11
    if type(absorbed) is not bool:
        raise TypeError("mod-99 absorbed flag must be Boolean")
    complete_integer_certified = result.complete_integer_certified
    if type(complete_integer_certified) is not bool:
        raise TypeError("mod-99 integer certificate flag must be Boolean")

    return (
        require_integer(result.generation, "accumulator generation", 0),
        require_integer(result.bootstrap_generation, "bootstrap generation", 0),
        phase,
        state_a,
        state_b,
        require_integer(result.integer_mod99, "integer residue", 0, 98),
        require_integer(result.reverse_mod99, "reverse residue", 0, 98),
        absorbed,
        require_integer(result.even_blocks_powered, "powered even blocks", 0),
        multiplier,
        coupling,
        require_integer(result.source_mod99, "source residue", 0, 98),
        require_integer(result.generation_mod99, "generation residue", 0, 98),
        source_certified,
        complete_integer_certified,
        source_reverse,
    )
