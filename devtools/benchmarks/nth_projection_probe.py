"""Fail-closed nth-term projection work benchmark.

The charged metric is compiler/projection work *before* output materialization.
For geometric index doubling, a quadratic regression would approach a 4x work
ratio.  The release guard requires substantial headroom below that boundary.
"""

from __future__ import annotations

import json
from collections.abc import Callable
from typing import TypedDict

from devtools.paths import report_directory, repository_root
from devtools.runs import run_reported
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.query_types import (
    CollatzTermQuery,
    FermatTermQuery,
    MersenneTermQuery,
    PrimeTermQuery,
    ReverseAddTermQuery,
    TermQuery,
)
from number_compiler.arithmetic.fields.symbolic_extent import extent_json_value


class ProjectionRow(TypedDict):
    index: int
    projection_work: int
    descriptor_nodes: int
    width: object
    doubling_ratio: float


class SpecialRow(TypedDict):
    descriptor_bits: int
    raw_squarings: int
    projection_work: int


class ProjectionReport(TypedDict):
    status: str
    max_doubling_ratio: float
    quadratic_boundary: float
    guard: float
    series: dict[str, list[ProjectionRow]]
    special: dict[str, SpecialRow]


ROOT = repository_root()

INDICES = (8, 16, 32, 64)
MAX_DOUBLING_RATIO = 3.25


def _series(
    compiler: NumberCompiler, query: Callable[[int], TermQuery]
) -> list[ProjectionRow]:
    rows: list[ProjectionRow] = []
    previous = None
    for index in INDICES:
        term = compiler.project(query(index))
        work = int(term.metrics.projection_work)
        ratio = 0.0 if previous is None else work / previous
        rows.append(
            {
                "index": index,
                "projection_work": work,
                "descriptor_nodes": int(term.metrics.descriptor_nodes),
                "width": (
                    None
                    if term.metrics.width is None
                    else extent_json_value(term.metrics.width)
                ),
                "doubling_ratio": ratio,
            }
        )
        previous = max(1, work)
    return rows


def run_probe() -> ProjectionReport:
    compiler = NumberCompiler()
    data = {
        "reverse_add": _series(
            compiler, lambda index: ReverseAddTermQuery(index, seed=196)
        ),
        "collatz": _series(compiler, lambda index: CollatzTermQuery(index, seed=27)),
        "prime": _series(
            compiler, lambda index: PrimeTermQuery(index, start=1_000_000)
        ),
    }
    special = {
        "fermat": compiler.project(FermatTermQuery(30)).metrics,
        "mersenne": compiler.project(MersenneTermQuery(1_000_000)).metrics,
    }
    ratios = [
        float(row["doubling_ratio"]) for rows in data.values() for row in rows[1:]
    ]
    if max(ratios, default=0.0) >= MAX_DOUBLING_RATIO:
        raise AssertionError(("quadratic-projection-regression", max(ratios), data))
    if any(m.raw_squarings or m.projection_work for m in special.values()):
        raise AssertionError(("special-term-projection-replayed-squaring", special))
    return {
        "status": "PASS",
        "max_doubling_ratio": max(ratios, default=0.0),
        "quadratic_boundary": 4.0,
        "guard": MAX_DOUBLING_RATIO,
        "series": data,
        "special": {
            key: {
                "descriptor_bits": value.descriptor_bits,
                "raw_squarings": value.raw_squarings,
                "projection_work": value.projection_work,
            }
            for key, value in special.items()
        },
    }


def main() -> int:
    result = run_probe()
    out = (
        report_directory("devtools.benchmarks.nth_projection_probe")
        / "nth_projection_metrics.json"
    )
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(run_reported(main))
