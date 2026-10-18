"""Typed microbenchmark for finite Mahler joins and retained Collatz tapes.

The Mahler comparison separates two half-transfer builds, their final relation
composition, and direct issuance. Each half-build includes its own bounded
leaf issuance and internal joins. It is not an end-to-end term-query benchmark
or a speedup claim. The Collatz comparison reports normalized parity half-steps separately
from physical ticks (half-steps plus odd half-steps), and compares each retained
prefix with the literal word for that exact prefix.
"""

from __future__ import annotations

import json
from collections.abc import Callable
from dataclasses import asdict, dataclass
from statistics import median
from time import perf_counter_ns
from unittest.mock import patch

from devtools.benchmarks.reporting import write_markdown_json_report
from devtools.paths import report_directory, report_output
from devtools.runs import run_reported
from number_compiler.sequences.antihydra.mahler_center_depth_matrix import (
    MahlerCertifiedCenterDepthTransfer,
)
from number_compiler.sequences.antihydra.mahler_center_exterior_join import (
    MahlerCenterExteriorEvidence,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.named_border_carry_matrix import (
    UnitsCarryMatrix,
)
from number_compiler.sequences.collatz.parity_carry_tape import ParityCarryTape


@dataclass(frozen=True, slots=True)
class JoinProbeMetrics:
    source: int
    physical_steps: int
    split_steps: int
    direct_issue_median_ns: int
    preconstructed_halves_build_ns: int
    preconstructed_then_median_ns: int
    forbidden_exterior_reissue_calls: int
    pointed_paths_equal: bool
    full_source_relation_equal: bool


@dataclass(frozen=True, slots=True)
class TapeProbeMetrics:
    normalized_steps: int
    physical_ticks: int
    prefix_normalized_steps: int
    prefix_physical_ticks: int
    retained_prefix_median_ns: int
    literal_oracle_median_ns: int
    retained_letter_factory_calls: int
    literal_letter_factory_calls: int
    action_equal: bool
    weighted_units_equal: bool
    odd_count_equal: bool


def _time_repeated(call: Callable[[], object], repetitions: int = 5) -> tuple[int, ...]:
    samples: list[int] = []
    for _ in range(repetitions):
        started = perf_counter_ns()
        call()
        samples.append(perf_counter_ns() - started)
    return tuple(samples)


def _mahler_probe() -> JoinProbeMetrics:
    source = 100_007
    physical_steps = 4
    split_steps = 2

    started = perf_counter_ns()
    first = MahlerCertifiedCenterDepthTransfer.powered_from_source(
        source, split_steps, leaf_steps=1
    )
    second = MahlerCertifiedCenterDepthTransfer.powered_from_source(
        first.pointed_sources[-1], physical_steps - split_steps, leaf_steps=1
    )
    preconstructed_halves_build_ns = perf_counter_ns() - started

    direct_samples = _time_repeated(
        lambda: MahlerCertifiedCenterDepthTransfer.from_source(source, physical_steps)
    )
    direct = MahlerCertifiedCenterDepthTransfer.from_source(source, physical_steps)

    reissue_calls = 0
    original_from_source = MahlerCenterExteriorEvidence.from_source

    def counted_reissue(
        _cls: type[MahlerCenterExteriorEvidence],
        candidate: int,
        *,
        center_places: int = 2,
        center_start: int | None = None,
    ) -> MahlerCenterExteriorEvidence:
        nonlocal reissue_calls
        reissue_calls += 1
        return original_from_source(
            candidate,
            center_places=center_places,
            center_start=center_start,
        )

    def compose() -> MahlerCertifiedCenterDepthTransfer:
        return first.then(second)

    with patch.object(
        MahlerCenterExteriorEvidence,
        "from_source",
        classmethod(counted_reissue),
    ):
        join_samples = _time_repeated(compose)
        joined = compose()

    paths_equal = (
        joined.pointed_sources == direct.pointed_sources
        and joined.pointed_centers == direct.pointed_centers
        and joined.center_positions == direct.center_positions
        and joined.steps == direct.steps
    )
    relation_equal = joined.matrix.rows == direct.matrix.rows
    if not paths_equal:
        raise ArithmeticError("Mahler preconstructed join changed the pointed path")
    if not relation_equal:
        raise ArithmeticError(
            "Mahler preconstructed join changed the full source relation"
        )
    if reissue_calls:
        raise ArithmeticError("Mahler then reissued source exterior evidence")

    return JoinProbeMetrics(
        source=source,
        physical_steps=physical_steps,
        split_steps=split_steps,
        direct_issue_median_ns=int(median(direct_samples)),
        preconstructed_halves_build_ns=preconstructed_halves_build_ns,
        preconstructed_then_median_ns=int(median(join_samples)),
        forbidden_exterior_reissue_calls=reissue_calls,
        pointed_paths_equal=paths_equal,
        full_source_relation_equal=relation_equal,
    )


def _literal_action(bits: tuple[int, ...]) -> DyadicTerminalFieldAction:
    action = DyadicTerminalFieldAction.identity()
    for bit in bits:
        action = action.then(
            DyadicTerminalFieldAction.one_run(1)
            if bit
            else DyadicTerminalFieldAction.zero_run(1)
        )
    return action


def _tape_probe() -> TapeProbeMetrics:
    factors = (((1, 0, 0), 80), ((1, 0), 55), ((0,), 45))
    tape = ParityCarryTape.factors(factors)
    letters = tuple(
        bit for motif, count in factors for _ in range(count) for bit in motif
    )
    prefix_normalized_steps = tape.steps - 7
    prefix = letters[:prefix_normalized_steps]
    prefix_physical_ticks = prefix_normalized_steps + sum(prefix)

    factory_calls = 0
    original_letter = UnitsCarryMatrix.letter

    def counted_letter(cls: type[UnitsCarryMatrix], odd: int) -> UnitsCarryMatrix:
        nonlocal factory_calls
        factory_calls += 1
        return original_letter(odd)

    with patch.object(UnitsCarryMatrix, "letter", classmethod(counted_letter)):
        retained_samples = _time_repeated(
            lambda: tape.prefix_units(prefix_normalized_steps)
        )
        retained_units = tape.prefix_units(prefix_normalized_steps)
    retained_factory_calls = factory_calls

    literal_factory_calls = 0

    def counted_literal_letter(
        cls: type[UnitsCarryMatrix], odd: int
    ) -> UnitsCarryMatrix:
        nonlocal literal_factory_calls
        literal_factory_calls += 1
        return original_letter(odd)

    with patch.object(
        UnitsCarryMatrix,
        "letter",
        classmethod(counted_literal_letter),
    ):
        literal_samples = _time_repeated(lambda: UnitsCarryMatrix.word(prefix))
        literal_units = UnitsCarryMatrix.word(prefix)

    retained_action = tape.prefix_action(prefix_normalized_steps)
    literal_action = _literal_action(prefix)
    retained_odds = tape.prefix_odds(prefix_normalized_steps)
    literal_odds = sum(prefix)
    action_equal = retained_action == literal_action
    units_equal = retained_units == literal_units
    odds_equal = retained_odds == literal_odds
    if not (action_equal and units_equal and odds_equal):
        raise ArithmeticError("retained Collatz tape disagrees with literal prefix")

    return TapeProbeMetrics(
        normalized_steps=tape.steps,
        physical_ticks=tape.steps + tape.odds,
        prefix_normalized_steps=prefix_normalized_steps,
        prefix_physical_ticks=prefix_physical_ticks,
        retained_prefix_median_ns=int(median(retained_samples)),
        literal_oracle_median_ns=int(median(literal_samples)),
        retained_letter_factory_calls=retained_factory_calls,
        literal_letter_factory_calls=literal_factory_calls,
        action_equal=action_equal,
        weighted_units_equal=units_equal,
        odd_count_equal=odds_equal,
    )


def main() -> None:
    module = "devtools.benchmarks.mahler_family_join_probe"
    markdown_path = report_output(module, "MAHLER_FAMILY_JOIN_PROBE.md")
    metrics_path = report_directory(module) / "mahler_family_join_metrics.json"
    metrics = {
        "mahler_source_join": asdict(_mahler_probe()),
        "collatz_retained_tape": asdict(_tape_probe()),
        "claim_scope": (
            "bounded diagnostics only; no end-to-end production term-query "
            "speedup claim"
        ),
    }
    markdown = "\n".join(
        (
            "# Mahler and Collatz finite-join probe",
            "",
            "This report separates building two preconstructed Mahler half-transfers (including each half's leaf issuance and internal joins), composing those halves, and direct issuance. It compares pointed sources, centers, and center coordinates at the same source and horizon, and counts forbidden exterior-evidence reissues during the final composition. Collatz metrics report normalized parity half-steps and their derived physical tick count separately; each retained prefix is checked against the literal word for that prefix. These are bounded diagnostics, not an end-to-end production term-query speedup claim.",
            "",
            "```json",
            json.dumps(metrics, indent=2, sort_keys=True),
            "```",
            "",
        )
    )
    write_markdown_json_report(markdown_path, metrics_path, markdown, metrics)


if __name__ == "__main__":
    raise SystemExit(run_reported(main))
