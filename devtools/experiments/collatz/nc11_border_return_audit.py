"""Independent finite physical-trajectory audit for the NC11 6305R route."""

from __future__ import annotations

import json
import random
from collections import Counter
from pathlib import Path

from devtools.paths import report_output
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.border_identity import (
    BoundaryPathKind,
    GuardedBorderPath,
)
from number_compiler.sequences.collatz.border_return_grammar import BorderReturnMacro
from number_compiler.sequences.collatz.innovation_carry_cocycle import (
    exact_source_symbol,
)
from number_compiler.sequences.collatz.innovation_port_moore import SIGNED_SYMBOLS
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)


def audit(output: Path) -> dict[str, object]:
    rng = random.Random(63050011)
    sources = list(range(1, 601))
    sources.extend(10 * rng.randrange(1, 1 << 140) + 3 for _ in range(200))
    sources.extend(10 * rng.randrange(1, 1 << 140) + 5 for _ in range(100))
    sources.extend(20 * rng.randrange(1, 1 << 140) + 6 for _ in range(100))
    routes: Counter[str] = Counter()
    passed = 0
    composite = 0
    normalized_symbols = 0
    for index, source in enumerate(sources):
        ticks = 6 + index % 134
        ledger = ResourceLedger()
        result = compile_collatz_temporal_run_quotient(
            source,
            ticks,
            ledger=ledger,
            shared_cache=False,
            include_joint_cocycle=True,
            include_width_spine=True,
            include_f5=True,
            include_innovation_tape=True,
            innovation_modulus=49,
        )
        value = source
        widths = [value.bit_length()]
        normalized_sum = source
        normalized = 0
        odd = 0
        for _ in range(ticks):
            if value & 1:
                odd += 1
                value = 3 * value + 1
            else:
                normalized += 1
                value //= 2
                normalized_sum += value
            widths.append(value.bit_length())
        if (result.endpoint, result.odd_ticks, result.division_ticks) != (
            value,
            odd,
            normalized,
        ):
            raise AssertionError(("wrong endpoint/clock", source, ticks))
        if result.physical_f5 is None or result.physical_f5.apply(source) != value % 5:
            raise AssertionError(("wrong F5", source, ticks))
        if (
            result.joint_action is None
            or result.joint_action.accumulator_observation(
                1009
            ).normalized_accumulator_residue
            != normalized_sum % 1009
        ):
            raise AssertionError(("wrong accumulator", source, ticks))
        if result.tape_width_summary is None:
            raise AssertionError(("missing width summary", source, ticks))
        width = result.tape_width_summary.blank
        if (
            source.bit_length() + width.minimum,
            source.bit_length() + width.maximum,
        ) != (min(widths), max(widths)):
            raise AssertionError(("wrong width", source, ticks))
        if result.innovation_observation is None:
            raise AssertionError(("missing innovation tape", source, ticks))
        # The signed second innovation samples *normalized* sources, not
        # physical odd half-steps.  Derive that orbit independently.
        x = source
        normalized_sources = []
        for _ in range(normalized):
            normalized_sources.append(x)
            x = (3 * x + 1) // 2 if x & 1 else x // 2
        symbols = tuple(exact_source_symbol(x, 49) for x in normalized_sources)
        if tuple(result.innovation_observation.symbol_counts) != tuple(
            symbols.count(s) for s in SIGNED_SYMBOLS
        ):
            raise AssertionError(("wrong signed borrow/carry tape", source, ticks))
        macro = result.first_boundary_macro
        if (
            macro is not None
            and isinstance(macro.identity, GuardedBorderPath)
            and macro.identity.kind is BoundaryPathKind.THREE_BORDER_RETURN
        ):
            if type(macro) is not BorderReturnMacro:
                raise AssertionError(
                    ("6305R route has another macro type", source, ticks)
                )
            composite += 1
            routes[macro.exit_port.value] += 1
            if macro.fields.endpoint(macro.source) != macro.endpoint:
                raise AssertionError(("wrong composite", source, ticks))
            normalized_symbols += macro.normalized_symbols
        passed += 1
    # A separate complete digit-transition census confirms that no *interior*
    # 9 can arise without the source's last digit being 8.
    nine_transitions = 0
    for x in range(1, 10001):
        y = 3 * x + 1 if x & 1 else x // 2
        if y % 10 == 9:
            if x % 10 != 8 or x % 20 != 18:
                raise AssertionError(("unproven 8->9", x, y))
            nine_transitions += 1
    report = {
        "randomized_physical_trajectories_checked": passed,
        "complete_interior_nine_transition_checks": 10000,
        "nine_transitions_all_from_eight": nine_transitions,
        "composite_actions_observed": composite,
        "composite_normalized_symbols": normalized_symbols,
        "exit_ports": dict(sorted(routes.items())),
        "scope": "finite guarded physical prefixes, not Collatz convergence",
    }
    output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    return report


def main() -> None:
    output = report_output(
        "devtools.experiments.collatz.nc11_border_return_audit", "audit.json"
    )
    print(json.dumps(audit(output), sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
