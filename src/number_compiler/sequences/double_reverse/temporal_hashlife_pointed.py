"""Bounded source-authenticated point queries over 2rev10 Hashlife."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    double_reverse as _double_reverse_keys,
)
from number_compiler.sequences.double_reverse.stencil_moore import (
    DIGIT_STENCIL_MOORE,
)
from number_compiler.sequences.double_reverse.temporal_alternating_carry import (
    normalized_t_squared_suffix,
)
from number_compiler.sequences.double_reverse.temporal_defect_quotient import (
    FourSymbolDefect,
    defect_and_successor_from_normalized_suffix,
    defect_from_normalized_suffix,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_borders import (
    growth_ports,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
    DoubleReverseSLPID,
    PointedDigitStencil,
)


class PointedHashlifeEngine(Protocol):
    """Public bounded source operations required by pointed observations."""

    arena: LedgerSLPArena
    ledger: ResourceLedger
    max_steps: int
    scratch_owner: int

    def part(self, root: int, begin: int, end: int) -> int: ...

    def certify(self, root: int) -> int | None: ...

    def scoped_handle(self, root: int) -> DoubleReverseSLPID: ...

    def cone_step_for_pointed_window(self, root: int, steps: int) -> int: ...


@dataclass(frozen=True, slots=True)
class CertifiedDefectTape:
    """Source-guarded local emissions and their bounded halo work summary."""

    emissions: tuple[FourSymbolDefect, ...]
    halo_segments: int
    locally_advanced_f_steps: int


def pointed_source_window(
    engine: PointedHashlifeEngine, root: int, origin: int, radius: int
) -> int:
    """Build the exact zero-extended causal interval around one source cell."""
    width = engine.arena.nodes[root].length
    length = 2 * radius + 1
    begin = origin - radius
    end = begin + length
    left_zeros = min(length, max(0, -begin))
    right_zeros = min(length - left_zeros, max(0, end - width))
    middle = length - left_zeros - right_zeros
    with engine.ledger.reservation(engine.scratch_owner, entries=8, nodes=8):
        fragments: list[int] = []
        zero = engine.arena.terminal(0)
        if left_zeros:
            fragments.append(engine.arena.repeat(zero, left_zeros))
        if middle:
            first = max(0, begin)
            fragments.append(engine.part(root, first, first + middle))
        if right_zeros:
            fragments.append(engine.arena.repeat(zero, right_zeros))
        window = engine.arena.concat_many(fragments)
    if engine.arena.nodes[window].length != length:
        raise AssertionError("pointed stencil window omitted its causal halo")
    return window


def _advance_pointed_window(
    engine: PointedHashlifeEngine, window: int, steps: int
) -> int:
    """Apply one dyadic F chunk and retain only its exact future cone."""
    width = engine.arena.nodes[window].length
    if steps < 1 or steps & (steps - 1) or width <= 2 * steps:
        raise ValueError("pointed stencil needs a complete dyadic causal halo")
    output_width = width - 2 * steps
    span = 2 * steps
    count = (output_width + span - 1) // span
    # This is the private, source-authenticated causal-window path.  The
    # public pointed_window API retains its separate 18-cell bound. An
    # internally wider window avoids rebuilding each dyadic source cone
    # for three adjacent chunks of the same contiguous carry suffix.
    if count > 128:
        raise ValueError("private pointed halo exceeds 128 causal tiles")
    reservations = 8 + 4 * max(0, count - 2)
    with engine.ledger.reservation(
        engine.scratch_owner, entries=reservations, nodes=reservations
    ):
        zero_pad = engine.arena.repeat(engine.arena.terminal(0), 2 * steps)
        padded = engine.arena.concat(window, zero_pad)
        tile_roots: list[int] = []
        for tile_index in range(count):
            block = engine.part(
                padded, tile_index * span, tile_index * span + 4 * steps
            )
            tile_roots.append(engine.cone_step_for_pointed_window(block, steps))
            engine.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_POINTED_STENCIL_TILES
            )
        joined = engine.arena.concat_many(tile_roots)
        result = engine.part(joined, 0, output_width)
    if engine.arena.nodes[result].length != output_width:
        raise AssertionError("pointed stencil lost requested coordinates")
    return result


def _pointed_causal_window(
    engine: PointedHashlifeEngine,
    root: int,
    steps: int,
    phase: int,
    msd_start: int,
    count: int,
) -> tuple[int, ...]:
    """Share one complete source cone across a bounded output interval."""
    left, right = growth_ports(phase, steps)
    width = engine.arena.nodes[root].length + left + right
    if msd_start < 0 or msd_start + count > width:
        raise IndexError("pointed temporal row outside the normalized output")
    if steps == 0:
        values = tuple(
            symbol_at(engine.arena, root, msd_start + i) for i in range(count)
        )
    else:
        # The centered input cone for an even row contains one surplus
        # cell on its left. Crop that cell after the causal evolution.
        left_padding = int(count % 2 == 0)
        center = msd_start - left + (count - 1) // 2
        radius = steps + count // 2
        window = pointed_source_window(engine, root, center, radius)
        for bit in range(steps.bit_length() - 1, -1, -1):
            chunk = 1 << bit
            if steps & chunk:
                window = _advance_pointed_window(engine, window, chunk)
                engine.ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_POWERED_T2_STEPS,
                    chunk,
                )
                engine.ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_POWER_CHUNKS
                )
        if engine.arena.nodes[window].length != count + left_padding:
            raise AssertionError("pointed causal cone lost its complete row")
        values = tuple(
            symbol_at(engine.arena, window, left_padding + i) for i in range(count)
        )
    engine.ledger.bump(
        _double_reverse_keys.DOUBLE_REVERSE_POINTED_STENCIL_PUBLICATIONS,
        count,
    )
    return values


def pointed_window(
    engine: PointedHashlifeEngine,
    root: int,
    steps: int,
    phase: int,
    msd_start: int,
    count: int,
) -> tuple[int, ...]:
    """Read a short exact row through one shared source-root causal cone."""
    if (
        type(root) is not int
        or not 0 <= root < len(engine.arena.nodes)
        or type(steps) is not int
        or not 0 <= steps <= engine.max_steps // 2
        or type(phase) is not int
        or phase not in (0, 1, 2, 3)
        or type(msd_start) is not int
        or type(count) is not int
        or not 1 <= count <= 18
        or engine.certify(root) != phase
    ):
        raise ValueError("pointed temporal row needs a certified bounded source")
    return _pointed_causal_window(engine, root, steps, phase, msd_start, count)


def _pointed_carry_suffix(
    engine: PointedHashlifeEngine,
    root: int,
    steps: int,
    phase: int,
    length: int,
) -> tuple[int, ...]:
    """Read a certified suffix in at most 192-cell contiguous cones.

    The 192-cell cap implies at most 96 causal tiles at the final dyadic
    step. Public pointed_window remains limited to 18 digits; this
    internal path accounts for every intermediate tile and scratch node.
    """
    if (
        type(root) is not int
        or not 0 <= root < len(engine.arena.nodes)
        or type(steps) is not int
        or not 0 <= steps <= engine.max_steps // 2
        or type(phase) is not int
        or phase not in (0, 1, 2, 3)
        or engine.certify(root) != phase
        or type(length) is not int
        or length < 1
    ):
        raise ValueError("invalid authenticated carry-suffix source")
    width = engine.arena.nodes[root].length + sum(growth_ports(phase, steps))
    begin = width - min(width, length)
    suffix: list[int] = []
    while begin < width:
        count = min(192, width - begin)
        suffix.extend(_pointed_causal_window(engine, root, steps, phase, begin, count))
        begin += count
    return (0,) * (length - len(suffix)) + tuple(suffix)


def pointed_combined_defect(
    engine: PointedHashlifeEngine,
    root: int,
    steps: int,
    phase: int,
    digits: int,
) -> FourSymbolDefect:
    """One source-bound squared two-direction carry emission."""
    if (
        type(root) is not int
        or not 0 <= root < len(engine.arena.nodes)
        or type(steps) is not int
        or not 0 <= steps <= engine.max_steps // 2
        or type(phase) is not int
        or phase not in (0, 1, 2, 3)
        or type(digits) is not int
        or not 1 <= digits <= 96
        or engine.certify(root) != phase
    ):
        raise ValueError("pointed combined defect needs a certified source cone")
    return defect_from_normalized_suffix(
        _pointed_carry_suffix(engine, root, steps, phase, digits + 4), digits
    )


def pointed_combined_defect_tape(
    engine: PointedHashlifeEngine,
    root: int,
    start_steps: int,
    phase: int,
    digits: int,
    samples: int,
    stride: int = 1,
) -> CertifiedDefectTape:
    """Compile exact sampled carry actions from bounded shared halos.

    Plan the canonical source-coordinate segments BEFORE constructing any
    cone. Each segment retains the entire causal left halo for its own
    consecutive exact samples; a long observation tape needs a few
    certified segments, never one cone per occurrence after a 1024-cell
    cutoff. The temporal innovations themselves are not assumed periodic.
    """
    if (
        type(root) is not int
        or not 0 <= root < len(engine.arena.nodes)
        or type(start_steps) is not int
        or not 0 <= start_steps <= engine.max_steps // 2
        or type(phase) is not int
        or phase not in (0, 1, 2, 3)
        or type(digits) is not int
        or not 1 <= digits <= 96
        or type(samples) is not int
        or not 1 <= samples <= 128
        or type(stride) is not int
        or not 1 <= stride <= 4096
        or engine.certify(root) != phase
    ):
        raise ValueError("invalid source-bound combined defect tape")
    last = start_steps + 2 * stride * (samples - 1) + 2
    if last > engine.max_steps // 2:
        raise ValueError("defect tape exceeds the source temporal horizon")
    # The two F transitions of a macro require a 2-cell temporal halo,
    # plus four carry/normalization cells. A fixed 1024-cell guard makes
    # every private source cone bounded regardless of samples or stride.
    maximum_halo = 1024
    max_segment_samples = max(1, 1 + (maximum_halo - digits - 6) // (2 * stride))
    actions: list[FourSymbolDefect] = []
    segment_count = 0
    local_steps = 0
    for offset in range(0, samples, max_segment_samples):
        batch = min(max_segment_samples, samples - offset)
        begin_steps = start_steps + 2 * stride * offset
        required = digits + 4 + 2 * (stride * (batch - 1) + 1)
        if required > maximum_halo:
            raise AssertionError("carry halo plan exceeds its finite budget")
        current = _pointed_carry_suffix(engine, root, begin_steps, phase, required)
        segment_count += 1
        for i in range(batch):
            if len(current) < digits + 4:
                raise AssertionError("causal carry suffix exhausted its left halo")
            action, after_two_steps = defect_and_successor_from_normalized_suffix(
                current, digits
            )
            actions.append(action)
            if i + 1 == batch:
                break
            # The same normalized two-step successor is re-used for the
            # next state, then only the unobserved stride gap is advanced.
            current = after_two_steps
            local_steps += 2
            for _ in range(2 * stride - 2):
                current, _growth = normalized_t_squared_suffix(current)
                local_steps += 1
    return CertifiedDefectTape(tuple(actions), segment_count, local_steps)


def pointed_stencil(
    engine: PointedHashlifeEngine,
    root: int,
    steps: int,
    phase: int,
    msd_index: int,
) -> PointedDigitStencil:
    """Return one exact output cell without producing its full endpoint."""
    if (
        type(root) is not int
        or not 0 <= root < len(engine.arena.nodes)
        or type(steps) is not int
        or not 1 <= steps <= engine.max_steps // 2
        or type(phase) is not int
        or phase not in (0, 1, 2, 3)
        or type(msd_index) is not int
        or engine.certify(root) != phase
    ):
        raise ValueError("pointed stencil requires a certified source cylinder")
    digit = _pointed_causal_window(engine, root, steps, phase, msd_index, 1)[0]
    width = engine.arena.nodes[root].length + sum(growth_ports(phase, steps))
    return PointedDigitStencil(
        engine.scoped_handle(root),
        steps,
        phase,
        (phase + 2 * steps) % 4,
        width,
        msd_index,
        digit,
        int(digit >= 5),
        digit % 5,
        DIGIT_STENCIL_MOORE["joint"].classes[digit],
    )


__all__ = [
    "CertifiedDefectTape",
    "PointedHashlifeEngine",
    "_advance_pointed_window",
    "_pointed_carry_suffix",
    "_pointed_causal_window",
    "pointed_combined_defect",
    "pointed_combined_defect_tape",
    "pointed_source_window",
    "pointed_stencil",
    "pointed_window",
]
