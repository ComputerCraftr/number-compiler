"""Bounded 2rev10 source-return evidence, separate from production nth."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import TypeVar

from devtools.verification.double_reverse_period_action import (
    MAX_ACTION_STATES,
    ConditionalActionBudgetExceeded,
    ConditionalActionRefusalReport,
    ConditionalActionRefused,
    ConditionalActionReport,
    conditional_action,
)
from devtools.verification.double_reverse_period_source import (
    MAX_ANCHORS,
    MAX_DECIMAL_WIDTH,
    MAX_DEPTH,
    MAX_GENERATION,
    MAX_MULTIPLIER,
    MAX_RETAINED_ROW_BYTES,
    MAX_SAMPLED_ROWS,
    MAX_WINDOW,
    FinitePeriodLift,
    FiniteWindowReturn,
    OuterPairObservation,
    SourceEvidenceRefused,
    SourceReplayWork,
    finite_capacity_report,
    replay_source_rows,
    sample_generations,
)
from number_compiler.sequences.double_reverse.temporal_diagonal_induction import (
    certified_closed_outer_pair_return,
)


@dataclass(frozen=True, slots=True)
class PeriodReturnReport:
    source_seed: int
    checkpoint_generation: int
    crosscheck_generation: int
    anchors: tuple[int, ...]
    window_physical_generations: int
    finite_returns: tuple[FiniteWindowReturn, ...]
    finite_period_lifts: tuple[FinitePeriodLift, ...]
    source_closed_outer_pair: tuple[OuterPairObservation, ...]
    conditional_action: ConditionalActionResult | None
    work: SourceReplayWork
    scope: str


ConditionalActionResult = ConditionalActionReport | ConditionalActionRefusalReport
_T = TypeVar("_T")


def _required(value: _T | None, name: str) -> _T:
    if value is None:
        raise ValueError(f"missing required command-line option --{name}")
    return value


def analyze_source_returns(
    seed: int,
    checkpoint_generation: int,
    checkpoint: str,
    crosscheck_generation: int,
    crosscheck: str,
    *,
    anchors: tuple[int, ...],
    base_period: int,
    max_multiplier: int,
    first_depth: int,
    max_depth: int,
    window: int,
    action_depth: int | None = None,
    action_period: int | None = None,
    action_power_fsteps: int = 10**9,
    action_max_states: int = 4_096,
) -> PeriodReturnReport:
    """Replay exact source rows and report scoped finite/conditional results."""
    if (
        type(seed) is not int
        or seed <= 0
        or type(checkpoint_generation) is not int
        or type(crosscheck_generation) is not int
        or checkpoint_generation < 0
        or crosscheck_generation <= checkpoint_generation
        or not anchors
        or len(anchors) > MAX_ANCHORS
        or len(set(anchors)) != len(anchors)
        or any(
            type(anchor) is not int or anchor < crosscheck_generation or anchor % 4
            for anchor in anchors
        )
        or type(base_period) is not int
        or base_period < 4
        or base_period % 4
        or type(max_multiplier) is not int
        or not 1 <= max_multiplier <= MAX_MULTIPLIER
        or type(window) is not int
        or not 4 <= window <= MAX_WINDOW
        or type(first_depth) is not int
        or type(max_depth) is not int
        or not 2 <= first_depth <= max_depth <= MAX_DEPTH
        or (
            action_depth is not None
            and (type(action_depth) is not int or not 1 <= action_depth <= max_depth)
        )
        or (
            action_period is not None
            and (
                type(action_period) is not int
                or action_period <= 0
                or action_period % 4
            )
        )
        or type(action_power_fsteps) is not int
        or action_power_fsteps < 0
        or type(action_max_states) is not int
        or not 1 <= action_max_states <= MAX_ACTION_STATES
        or (action_depth is None) != (action_period is None)
    ):
        raise ValueError("invalid bounded source-return request")
    lags = tuple(
        base_period * multiplier for multiplier in range(1, max_multiplier + 1)
    )
    largest_sample = max(anchors) + lags[-1] + window - 1
    if action_period is not None:
        largest_sample = max(largest_sample, anchors[0] + action_period + window)
    if largest_sample > MAX_GENERATION:
        raise SourceEvidenceRefused("requested generation exceeds replay budget")
    conservative_rows = len(anchors) * (max_multiplier + 1) * window
    if action_period is not None:
        conservative_rows += action_period // 2 + (window + 1) // 2 + 2
    retained_row_bytes = conservative_rows * (1_024 + 16 * (max_depth + 2))
    if (
        conservative_rows > MAX_SAMPLED_ROWS
        or retained_row_bytes > MAX_RETAINED_ROW_BYTES
    ):
        raise SourceEvidenceRefused(
            "requested source windows exceed row or memory budget"
        )
    generations = sample_generations(anchors, lags, window, action_period=action_period)
    rows, replay_work = replay_source_rows(
        seed,
        checkpoint_generation,
        checkpoint,
        crosscheck_generation,
        crosscheck,
        generations,
        depth=max_depth,
    )
    finite_returns, lifts = finite_capacity_report(
        rows,
        anchors,
        lags,
        window=window,
        max_depth=max_depth,
        first_depth=first_depth,
    )
    outer: list[OuterPairObservation] = []
    for anchor in anchors:
        row = rows[anchor]
        edge = (
            int(row.left[0]),
            int(row.left[1]),
            int(row.right[-2]),
            int(row.right[-1]),
        )
        try:
            certificate = certified_closed_outer_pair_return(edge)
        except ValueError:
            outer.append(
                OuterPairObservation(
                    anchor, "outside_closed_component", "physical T transitions", None
                )
            )
        else:
            outer.append(
                OuterPairObservation(
                    anchor,
                    "source_closed_outer_pair",
                    "physical T transitions",
                    certificate,
                )
            )
    action: ConditionalActionResult | None = None
    if action_depth is not None and action_period is not None:
        try:
            action = conditional_action(
                rows,
                anchor=anchors[0],
                depth=action_depth,
                physical_period=action_period,
                window=window,
                power_fsteps=action_power_fsteps,
                max_states=action_max_states,
            )
        except ConditionalActionBudgetExceeded as error:
            action = ConditionalActionRefusalReport(
                "conditional_action_budget_exceeded",
                "conditional effective-seam action",
                str(error),
            )
        except ConditionalActionRefused as error:
            action = ConditionalActionRefusalReport(
                "conditional_action_refused",
                "conditional effective-seam action",
                str(error),
            )
        except SourceEvidenceRefused as error:
            action = ConditionalActionRefusalReport(
                "source_rows_incomplete",
                "conditional effective-seam source window",
                str(error),
            )
    return PeriodReturnReport(
        seed,
        checkpoint_generation,
        crosscheck_generation,
        anchors,
        window,
        finite_returns,
        lifts,
        tuple(outer),
        action,
        replay_work,
        "finite source-window observations plus separately scoped conditional actions",
    )


@dataclass(slots=True)
class _Arguments(argparse.Namespace):
    seed: int = 196
    checkpoint_generation: int | None = None
    checkpoint: Path | None = None
    crosscheck_generation: int | None = None
    crosscheck: Path | None = None
    anchors: list[int] | None = None
    window: int = 384
    base_period: int = 1_152
    max_multiplier: int = 6
    first_depth: int = 145
    max_depth: int = 650
    action_depth: int | None = None
    action_period: int | None = None
    action_power_fsteps: int = 10**9
    action_max_states: int = 4_096
    output: Path | None = None


def _checkpoint(path: Path) -> str:
    try:
        with path.open("r", encoding="ascii") as stream:
            checkpoint = stream.read(MAX_DECIMAL_WIDTH + 3)
            if len(checkpoint) > MAX_DECIMAL_WIDTH + 2:
                raise SourceEvidenceRefused(
                    "checkpoint file exceeds decimal-width budget"
                )
            if stream.read(1):
                raise SourceEvidenceRefused(
                    "checkpoint file exceeds decimal-width budget"
                )
    except (OSError, UnicodeError) as error:
        raise SourceEvidenceRefused(
            "checkpoint file cannot be read as ASCII"
        ) from error
    return checkpoint.strip()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--seed", type=int, default=196)
    parser.add_argument("--checkpoint-generation", type=int, required=True)
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--crosscheck-generation", type=int, required=True)
    parser.add_argument("--crosscheck", type=Path, required=True)
    parser.add_argument("--anchors", type=int, nargs="+", required=True)
    parser.add_argument("--window", type=int, default=384)
    parser.add_argument("--base-period", type=int, default=1_152)
    parser.add_argument("--max-multiplier", type=int, default=6)
    parser.add_argument("--first-depth", type=int, default=145)
    parser.add_argument("--max-depth", type=int, default=650)
    parser.add_argument("--action-depth", type=int)
    parser.add_argument("--action-period", type=int)
    parser.add_argument("--action-power-fsteps", type=int, default=10**9)
    parser.add_argument("--action-max-states", type=int, default=4_096)
    parser.add_argument("--output", type=Path, required=True)
    args = _Arguments()
    parser.parse_args(namespace=args)
    checkpoint_path = _required(args.checkpoint, "checkpoint")
    crosscheck_path = _required(args.crosscheck, "crosscheck")
    anchor_values = _required(args.anchors, "anchors")
    output_path = _required(args.output, "output")
    report = analyze_source_returns(
        args.seed,
        _required(args.checkpoint_generation, "checkpoint-generation"),
        _checkpoint(checkpoint_path),
        _required(args.crosscheck_generation, "crosscheck-generation"),
        _checkpoint(crosscheck_path),
        anchors=tuple(anchor_values),
        base_period=args.base_period,
        max_multiplier=args.max_multiplier,
        first_depth=args.first_depth,
        max_depth=args.max_depth,
        window=args.window,
        action_depth=args.action_depth,
        action_period=args.action_period,
        action_power_fsteps=args.action_power_fsteps,
        action_max_states=args.action_max_states,
    )
    output_path.parent.mkdir(parents=True, exist_ok=True)
    report_json = json.dumps(asdict(report), indent=2)
    output_path.write_text(report_json + "\n", encoding="utf-8")
    print(report_json, flush=True)
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
