"""Exact source replay and positional return rows for 2rev10 diagnostics."""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from typing import Literal

from number_compiler.sequences.double_reverse.temporal_birth_ring import (
    BirthRingPorts,
    BirthRingState,
)
from number_compiler.sequences.double_reverse.temporal_diagonal_induction import (
    ClosedBorderPairReturn,
    SeamGate,
    seam_gate,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_borders import (
    edge_phase,
)

MAX_GENERATION = 40_000
MAX_DECIMAL_WIDTH = 50_000
MAX_ANCHORS = 8
MAX_WINDOW = 2_048
MAX_DEPTH = 1_024
MAX_MULTIPLIER = 8
MAX_SAMPLED_ROWS = 16_384
MAX_RETAINED_ROW_BYTES = 256 * 1024 * 1024


class SourceEvidenceRefused(ValueError):
    """A finite source evidence request exceeded or failed its authority."""


@dataclass(frozen=True, slots=True)
class SpatialBorrowFold:
    """Exact two-sided subtraction ports for one source-to-successor seam."""

    upper_borrow: str
    lower_borrow: str
    upper_transfer: str
    lower_transfer: str
    edge_digit_updates: int
    lower_suffix_operand_width: int


@dataclass(frozen=True, slots=True)
class SpatialReturnRow:
    """Retained positional outputs from one exact physical source transition."""

    generation: int
    source_width: int
    target_width: int
    phase: int
    left: str
    right: str
    carry_left: str
    carry_right: str
    borrow_left: str
    borrow_right: str
    borrow_transfer_left: str
    borrow_transfer_right: str
    borrow_fold: SpatialBorrowFold

    @property
    def growth(self) -> int:
        return self.target_width - self.source_width


@dataclass(frozen=True, slots=True)
class SourceReplayWork:
    """Bounded diagnostic counters, not production work-saved claims."""

    physical_generations_replayed: int
    successor_evaluations: int
    source_rows_retained: int
    maximum_decimal_width: int
    retained_row_bytes_upper_bound: int
    borrow_edge_digit_updates: int
    lower_suffix_operand_width: int


@dataclass(frozen=True, slots=True)
class ReturnWitness:
    generation: int
    shifted_generation: int
    first_unverified_depth: int
    channel: str
    source_phase: int
    source_width: int
    shifted_width: int


@dataclass(frozen=True, slots=True)
class FiniteWindowReturn:
    anchor: int
    lag_physical_generations: int
    maximum_joint_depth: int
    checked_source_rows: int
    first_failure: ReturnWitness | None


@dataclass(frozen=True, slots=True)
class FinitePeriodLift:
    first_depth: int
    least_tested_multiplier: int | None
    finite_period_physical_generations: int | None
    passing_multipliers: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class OuterPairObservation:
    anchor: int
    status: Literal["source_closed_outer_pair", "outside_closed_component"]
    return_steps_unit: Literal["physical T transitions"]
    certificate: ClosedBorderPairReturn | None


def _valid_decimal_word(word: str) -> bool:
    return (
        bool(word)
        and word.isascii()
        and word.isdigit()
        and (len(word) == 1 or word[0] != "0")
    )


def reverse_double_word(word: str) -> str:
    """Exact decimal ``2 * reverse(word)`` without large integer casts."""
    if not _valid_decimal_word(word):
        raise ValueError("2rev10 source must be a canonical positive decimal word")
    carry = 0
    least_significant_first: list[str] = []
    for character in word:
        product = 2 * (ord(character) - ord("0")) + carry
        least_significant_first.append(chr(ord("0") + product % 10))
        carry = product // 10
    if carry:
        least_significant_first.append(chr(ord("0") + carry))
    result = "".join(reversed(least_significant_first)).lstrip("0")
    return result or "0"


def _transfer(source: str, target: str) -> str:
    return "1" if target < source else "0" if target > source else "I"


def _fold_borrow_strip(
    source_digits: Iterable[str], target_digits: Iterable[str], initial_borrow: int
) -> tuple[str, str]:
    borrows: list[str] = []
    transfers: list[str] = []
    borrow = initial_borrow
    for source_digit, target_digit in zip(source_digits, target_digits, strict=True):
        transfer = _transfer(source_digit, target_digit)
        borrow = int(transfer == "1" or (transfer == "I" and borrow == 1))
        borrows.append(str(borrow))
        transfers.append(transfer)
    return "".join(borrows), "".join(transfers)


def spatial_borrow_fold(source: str, target: str, depth: int) -> SpatialBorrowFold:
    """Fold edge strips and compare the intervening suffix for upper borrow."""
    if (
        not _valid_decimal_word(source)
        or not _valid_decimal_word(target)
        or type(depth) is not int
        or depth < 1
    ):
        raise ValueError("invalid spatial borrow-fold input")
    width = max(len(source), len(target))
    span = depth + 1
    if width < 2 * span:
        raise ValueError("source width is too small for disjoint edge strips")
    left = source.zfill(width)
    right = target.zfill(width)
    upper_borrows_lsd, upper_transfers_lsd = _fold_borrow_strip(
        reversed(left[:span]),
        reversed(right[:span]),
        int(right[span:] < left[span:]),
    )
    lower_borrows, lower_transfers = _fold_borrow_strip(
        reversed(left[-span:]), reversed(right[-span:]), 0
    )
    return SpatialBorrowFold(
        upper_borrows_lsd[::-1],
        lower_borrows,
        upper_transfers_lsd[::-1],
        lower_transfers,
        2 * span,
        len(left[span:]),
    )


def spatial_return_row(
    generation: int, source: str, target: str, depth: int
) -> SpatialReturnRow:
    """Create one exact positional row using the optimized borrow fold."""
    if type(generation) is not int or generation < 0 or type(depth) is not int:
        raise ValueError("invalid source-row coordinates")
    if depth < 2 or len(source) < 2 * (depth + 1):
        raise ValueError("source word is too narrow for the requested bank")
    phase = edge_phase(
        (int(source[0]), int(source[1])),
        (int(source[-2]), int(source[-1])),
    )
    if phase is None:
        raise SourceEvidenceRefused(
            f"generation {generation} is outside the certified 2rev10 border cylinder"
        )
    span = depth + 1
    fold = spatial_borrow_fold(source, target, depth)
    return SpatialReturnRow(
        generation,
        len(source),
        len(target),
        phase,
        source[: span + 1],
        source[-(span + 1) :],
        "".join("1" if digit >= "5" else "0" for digit in source[:span]),
        "".join("1" if digit >= "5" else "0" for digit in source[-span:]),
        fold.upper_borrow,
        fold.lower_borrow,
        fold.upper_transfer,
        fold.lower_transfer,
        fold,
    )


def effective_gate(row: SpatialReturnRow, depth: int) -> SeamGate:
    """Recover the exact F=T² bank gate using the existing Moore owner."""
    if type(depth) is not int or not 1 <= depth <= len(row.left) - 1:
        raise ValueError("effective gate depth exceeds retained source strips")
    state = BirthRingState(
        tuple(int(digit) for digit in row.left[:depth]),
        tuple(int(digit) for digit in row.right[-depth:]),
        row.phase,
    )
    ports = BirthRingPorts(int(row.left[depth]), int(row.right[-depth - 1]))
    return seam_gate(state, ports)


def _common_prefix(left: str, right: str) -> int:
    for index, (a, b) in enumerate(zip(left, right, strict=False)):
        if a != b:
            return index
    return min(len(left), len(right))


def _port_channels(row: SpatialReturnRow) -> tuple[tuple[str, str], ...]:
    return (
        ("source_left", row.left),
        ("source_right", row.right[::-1]),
        ("carry_left", row.carry_left),
        ("carry_right", row.carry_right[::-1]),
        ("propagated_borrow_left", row.borrow_left),
        ("propagated_borrow_right", row.borrow_right),
        ("borrow_transfer_left", row.borrow_transfer_left),
        ("borrow_transfer_right", row.borrow_transfer_right),
    )


def return_capacity(
    first: SpatialReturnRow, shifted: SpatialReturnRow, max_depth: int
) -> tuple[int, str]:
    if first.phase != shifted.phase:
        return 0, "phase"
    if first.growth != shifted.growth:
        return 0, "growth"
    limits = tuple(
        (name, _common_prefix(left, right))
        for (name, left), (_, right) in zip(
            _port_channels(first), _port_channels(shifted), strict=True
        )
    )
    capacity = min(max_depth, *(limit for _, limit in limits))
    failure_channel = next(
        (name for name, limit in limits if limit == capacity), "window_limit"
    )
    # A source-edge match of length c fixes every gate through depth c - 1:
    # depth d reads only edge-inward positions 0..d on each side. The candidate
    # depth c alone can see the first differing inlet, so check that boundary
    # once after the prefix-derived interior has been established.
    if capacity >= 1 and effective_gate(first, capacity) != effective_gate(
        shifted, capacity
    ):
        return capacity - 1, "effective_f5_gate"
    return capacity, failure_channel


def replay_source_rows(
    seed: int,
    checkpoint_generation: int,
    checkpoint: str,
    crosscheck_generation: int,
    crosscheck: str,
    generations: frozenset[int],
    *,
    depth: int,
) -> tuple[dict[int, SpatialReturnRow], SourceReplayWork]:
    """Replay bounded string recurrence and authenticate both checkpoints."""
    if type(seed) is not int or seed <= 0 or seed.bit_length() > 13_000:
        raise ValueError("seed exceeds the exact input budget")
    if not _valid_decimal_word(checkpoint) or not _valid_decimal_word(crosscheck):
        raise ValueError("checkpoint words must be canonical positive decimals")
    if (
        type(checkpoint_generation) is not int
        or type(crosscheck_generation) is not int
        or checkpoint_generation < 0
        or crosscheck_generation <= checkpoint_generation
        or type(depth) is not int
        or not 2 <= depth <= MAX_DEPTH
    ):
        raise ValueError("checkpoint generations must be strictly increasing")
    if not generations or min(generations) < crosscheck_generation:
        raise ValueError("all sampled anchors must follow the independent crosscheck")
    target_generation = max(max(generations), crosscheck_generation)
    if target_generation > MAX_GENERATION or checkpoint_generation > target_generation:
        raise SourceEvidenceRefused("source replay exceeds the generation budget")
    if any(type(generation) is not int or generation < 0 for generation in generations):
        raise ValueError("sample generations must be nonnegative exact integers")
    estimate = len(generations) * (1_024 + 16 * (depth + 2))
    if len(generations) > MAX_SAMPLED_ROWS or estimate > MAX_RETAINED_ROW_BYTES:
        raise SourceEvidenceRefused("sampled positional rows exceed the memory budget")
    word = str(seed)
    if len(word) > MAX_DECIMAL_WIDTH:
        raise SourceEvidenceRefused("seed exceeds the decimal-width budget")
    rows: dict[int, SpatialReturnRow] = {}
    max_width = len(word)
    edge_updates = 0
    suffix_operand_width = 0
    for generation in range(target_generation + 1):
        if generation == checkpoint_generation and word != checkpoint:
            raise SourceEvidenceRefused("checkpoint does not match exact seed replay")
        if generation == crosscheck_generation and word != crosscheck:
            raise SourceEvidenceRefused("crosscheck does not match exact seed replay")
        target = reverse_double_word(word)
        if len(target) > MAX_DECIMAL_WIDTH:
            raise SourceEvidenceRefused("replayed source exceeds decimal-width budget")
        max_width = max(max_width, len(target))
        if generation in generations:
            row = spatial_return_row(generation, word, target, depth)
            rows[generation] = row
            edge_updates += row.borrow_fold.edge_digit_updates
            suffix_operand_width += row.borrow_fold.lower_suffix_operand_width
        if generation < target_generation:
            word = target
    return rows, SourceReplayWork(
        target_generation,
        target_generation + 1,
        len(rows),
        max_width,
        estimate,
        edge_updates,
        suffix_operand_width,
    )


def sample_generations(
    anchors: tuple[int, ...],
    lags: tuple[int, ...],
    window: int,
    *,
    action_period: int | None,
) -> frozenset[int]:
    """Return exact rows required for finite comparisons and optional action."""
    generations = {
        anchor + lag + offset
        for anchor in anchors
        for lag in (0, *lags)
        for offset in range(window)
    }
    if action_period is not None:
        anchor = anchors[0]
        motif_fsteps = action_period // 2
        generations.update(anchor + 2 * step for step in range(motif_fsteps + 1))
        check_fsteps = (window + 1) // 2
        generations.update(
            anchor + action_period + 2 * step for step in range(check_fsteps + 1)
        )
    return frozenset(generations)


def finite_capacity_report(
    rows: dict[int, SpatialReturnRow],
    anchors: tuple[int, ...],
    lags: tuple[int, ...],
    *,
    window: int,
    max_depth: int,
    first_depth: int,
) -> tuple[tuple[FiniteWindowReturn, ...], tuple[FinitePeriodLift, ...]]:
    """Compare all requested source rows and extract only finite return lifts."""
    returns: list[FiniteWindowReturn] = []
    capacities: dict[int, int] = {}
    for multiplier, lag in enumerate(lags, start=1):
        joint = max_depth
        for anchor in anchors:
            best: int | None = None
            witness: ReturnWitness | None = None
            for offset in range(window):
                first = rows[anchor + offset]
                shifted = rows[anchor + lag + offset]
                capacity, channel = return_capacity(first, shifted, max_depth)
                if shifted.source_width - first.source_width != lag // 2:
                    capacity, channel = 0, "width_displacement"
                if best is None or capacity < best:
                    best = capacity
                    witness = ReturnWitness(
                        first.generation,
                        shifted.generation,
                        capacity + 1,
                        channel,
                        first.phase,
                        first.source_width,
                        shifted.source_width,
                    )
            if best is None:
                raise AssertionError("finite return window inspected no source row")
            returns.append(FiniteWindowReturn(anchor, lag, best, window, witness))
            joint = min(joint, best)
        capacities[multiplier] = joint
    lifts: list[FinitePeriodLift] = []
    prior: int | None = None
    first_layer = True
    for depth in range(first_depth, max_depth + 1):
        passing = tuple(
            multiplier
            for multiplier, capacity in capacities.items()
            if depth <= capacity
        )
        least = passing[0] if passing else None
        if first_layer or least != prior:
            lifts.append(
                FinitePeriodLift(
                    depth, least, None if least is None else lags[least - 1], passing
                )
            )
            prior = least
            first_layer = False
    return tuple(returns), tuple(lifts)
