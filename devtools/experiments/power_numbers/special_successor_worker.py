"""Fresh-interpreter worker for memory-isolated special-successor audit groups."""

from __future__ import annotations

import pickle
import sys
from collections.abc import Callable
from pathlib import Path

from devtools.paths import repository_root

ROOT = repository_root()


def main(argv: list[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    kinds = {"ordinary", "hensel", "temporal", "phase"}
    if len(args) != 2 or args[0] not in kinds:
        raise SystemExit(
            "usage: special_successor_worker.py {ordinary|hensel|temporal|phase} OUTPUT"
        )
    kind, output = args
    from devtools.experiments.power_numbers.special_successor_carry import (
        carry_hensel_cyclotomic_audits,
        carry_phase_refinement_audits,
        carry_temporal_automaton_audits,
    )
    from devtools.experiments.power_numbers.special_successor_generators import (
        _ordinary_special_successor_parts,
    )

    dispatch: dict[str, Callable[[], object]] = {
        "ordinary": _ordinary_special_successor_parts,
        "hensel": carry_hensel_cyclotomic_audits,
        "temporal": carry_temporal_automaton_audits,
        "phase": carry_phase_refinement_audits,
    }
    result = dispatch[kind]()
    Path(output).write_bytes(pickle.dumps(result, protocol=pickle.HIGHEST_PROTOCOL))
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
