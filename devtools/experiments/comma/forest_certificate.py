"""Generate exact finite-forest and first-fork evidence for the comma graph.

This is an independent development computation, not an admitted production
certificate. The source-to-infinite-path and executable checker refinements
must be built before its result can enable public A367620 terms.
"""

from __future__ import annotations

import json
from collections import deque
from dataclasses import dataclass
from hashlib import sha256

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.comma.arithmetic import phase_period

CERTIFICATE_ID = "a367620-root-forest-phase-v1"
FIRST_FORK_VALUE = 19_999_999_918
FIRST_FORK_CHILDREN = (19_999_999_999, 20_000_000_000)

# This list is checked again from the exact predecessor formula before it is
# admitted. It is included to pin the intended finite source partition.
ROOTS = (
    1,
    2,
    3,
    4,
    5,
    6,
    7,
    8,
    9,
    10,
    13,
    14,
    15,
    16,
    17,
    18,
    19,
    20,
    21,
    25,
    26,
    27,
    28,
    29,
    30,
    31,
    32,
    37,
    38,
    39,
    40,
    41,
    42,
    43,
    49,
    50,
    51,
    52,
    53,
    54,
    62,
    63,
    64,
    65,
    74,
    75,
    76,
    86,
    87,
    98,
)


@dataclass(frozen=True, slots=True)
class ForestEvidence:
    roots_exhausted: int
    sector_entries: int
    boundary_steps: int
    cycles_skipped: int
    maximum_decimal_digits: int
    trace_sha256: str


@dataclass(frozen=True, slots=True)
class PrefixEvidence:
    first_fork_index: int
    first_fork_value: int
    children: tuple[int, ...]
    cycles_skipped: int
    literal_steps: int


def _lead_and_scale(k: int) -> tuple[int, int]:
    scale = 10 ** (len(str(k)) - 1)
    return k // scale, scale


def _literal_children(k: int) -> tuple[int, ...]:
    d = k % 10
    return tuple(
        candidate for e in range(1, 10) if str(candidate := k + 10 * d + e)[0] == str(e)
    )


def _parent_if_any(n: int) -> int | None:
    f, _ = _lead_and_scale(n)
    d = (n - f) % 10
    parent = n - 10 * d - f
    return parent if parent > 0 else None


def _small_roots() -> tuple[int, ...]:
    roots = tuple(n for n in range(1, 100) if _parent_if_any(n) is None)
    if roots != ROOTS:
        raise ValueError("comma root classification does not match the child rule")
    return roots


def _interior_cycles(k: int, f: int, boundary: int) -> tuple[int, int]:
    """Skip only complete phase cycles whose every child stays in this sector."""
    length, displacement = phase_period(f, k % 10)
    cycles = max(0, (boundary - 100 - k) // displacement)
    return cycles * length, cycles * displacement


def _boundary_children(k: int, f: int, scale: int) -> tuple[int, ...]:
    """Classify the at-most-two children near a sector boundary exactly."""
    if k < 100:
        return _literal_children(k)
    d = k % 10
    x = k + 10 * d
    boundary = (f + 1) * scale if f < 9 else 10 * scale
    if f < 9:
        same = x + f
        next_sector = x + f + 1
        return ((same,) if same < boundary else ()) + (
            (next_sector,) if boundary <= next_sector < (f + 2) * scale else ()
        )
    same = x + 9
    next_scale = x + 1
    return ((same,) if same < boundary else ()) + (
        (next_scale,) if boundary <= next_scale < 20 * scale else ()
    )


lead_and_scale = _lead_and_scale
literal_children = _literal_children
interior_cycles = _interior_cycles
boundary_children = _boundary_children


def _charge(ledger: ResourceLedger, max_work: int, amount: int = 1) -> None:
    spent = ledger.counters.get("comma_work", 0) + ledger.counters.get(
        "comma_certificate_work", 0
    )
    if spent + amount > max_work:
        ledger.bump("comma_certificate_failed_work")
        raise BlockContextBudgetExceeded("comma certificate work budget exceeded")
    ledger.bump("comma_certificate_work", amount)


def check_excluded_roots(ledger: ResourceLedger, max_work: int) -> ForestEvidence:
    """Exhaust every root tree except 20 by exact guarded sector transitions."""
    _small_roots()
    _charge(ledger, max_work, 99)
    frontier = deque((root, root) for root in ROOTS if root != 20)
    trace = sha256()
    entries = boundary_steps = cycles_skipped = 0
    max_digits = 0
    while frontier:
        root, k = frontier.popleft()
        _charge(ledger, max_work)
        entries += 1
        f, scale = _lead_and_scale(k)
        max_digits = max(max_digits, len(str(k)))
        boundary = (f + 1) * scale if f < 9 else 10 * scale
        trace.update(f"{root}:{k}:".encode("ascii"))
        if k < 100:
            children = _literal_children(k)
            _charge(ledger, max_work)
            trace.update(f"small:{children};".encode("ascii"))
            frontier.extend((root, child) for child in children)
            continue
        while True:
            steps, gain = _interior_cycles(k, f, boundary)
            if steps:
                if k + gain > boundary - 100:
                    raise ValueError("unauthorized comma phase skip")
                k += gain
                cycles_skipped += steps
                _charge(ledger, max_work)
                trace.update(f"skip:{steps}:{gain};".encode("ascii"))
            children = _boundary_children(k, f, scale)
            _charge(ledger, max_work)
            boundary_steps += 1
            trace.update(f"{k}:{children};".encode("ascii"))
            same: int | None = None
            for child in children:
                if _parent_if_any(child) != k:
                    raise ValueError("comma child has a forged parent")
                if child < boundary:
                    if same is not None:
                        raise ValueError("two same-sector comma children")
                    same = child
                else:
                    frontier.append((root, child))
            if same is None:
                break
            k = same
    return ForestEvidence(
        roots_exhausted=len(ROOTS) - 1,
        sector_entries=entries,
        boundary_steps=boundary_steps,
        cycles_skipped=cycles_skipped,
        maximum_decimal_digits=max_digits,
        trace_sha256=trace.hexdigest(),
    )


def check_first_fork(ledger: ResourceLedger, max_work: int) -> PrefixEvidence:
    """Check the unique root-20 path through its first choice point."""
    k = 20
    index = 1
    cycles_skipped = literal_steps = 0
    while True:
        _charge(ledger, max_work)
        f, scale = _lead_and_scale(k)
        boundary = (f + 1) * scale if f < 9 else 10 * scale
        if k >= 100:
            steps, gain = _interior_cycles(k, f, boundary)
            if steps:
                if k + gain > boundary - 100:
                    raise ValueError("unauthorized comma prefix skip")
                k += gain
                index += steps
                cycles_skipped += steps
                _charge(ledger, max_work)
        children = _boundary_children(k, f, scale)
        literal_steps += 1
        if len(children) != 1:
            return PrefixEvidence(
                first_fork_index=index,
                first_fork_value=k,
                children=children,
                cycles_skipped=cycles_skipped,
                literal_steps=literal_steps,
            )
        k = children[0]
        index += 1


def evidence_summary(max_work: int = 1_000_000) -> dict[str, object]:
    """Recompute a reviewable summary with the independent exact checker."""
    ledger = ResourceLedger()
    forest = check_excluded_roots(ledger, max_work)
    prefix = check_first_fork(ledger, max_work)
    if (
        prefix.first_fork_value != FIRST_FORK_VALUE
        or prefix.children != FIRST_FORK_CHILDREN
    ):
        raise ValueError("source-20 first-fork witness differs from the computation")
    return {
        "certificate_id": CERTIFICATE_ID,
        "roots_exhausted": forest.roots_exhausted,
        "sector_entries": forest.sector_entries,
        "boundary_steps": forest.boundary_steps,
        "maximum_decimal_digits": forest.maximum_decimal_digits,
        "trace_sha256": forest.trace_sha256,
        "first_fork_index": prefix.first_fork_index,
        "first_fork_value": prefix.first_fork_value,
        "first_fork_children": list(prefix.children),
        "charged_work": ledger.counters["comma_certificate_work"],
        "formal_prefix_checked": False,
    }


def main() -> None:
    """Print a reproducible, reviewable finite-evidence record."""
    summary = evidence_summary()
    document = {
        "schema": "a367620-forest-evidence-v1",
        "root": 20,
        "excluded_roots_exhausted": summary["roots_exhausted"],
        "sector_entries": summary["sector_entries"],
        "boundary_steps": summary["boundary_steps"],
        "maximum_decimal_digits": summary["maximum_decimal_digits"],
        "trace_sha256": summary["trace_sha256"],
        "first_fork_index_one_based": summary["first_fork_index"],
        "first_fork_value": summary["first_fork_value"],
        "first_fork_children": summary["first_fork_children"],
        "charged_work": summary["charged_work"],
        "formal_prefix_checked": summary["formal_prefix_checked"],
    }
    print(json.dumps(document, indent=2))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
