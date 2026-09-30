"""Shared source-inspection inputs for temporal release probes."""

from __future__ import annotations

from collections.abc import Callable, Mapping, Sequence
from collections.abc import Set as AbstractSet
from pathlib import Path

from devtools.checks.dependency_graph import SourceSyntax, source_syntax


def shared_cutover_sources(
    root: Path,
) -> tuple[
    AbstractSet[str],
    AbstractSet[str],
    SourceSyntax,
    SourceSyntax,
    SourceSyntax,
    SourceSyntax,
    AbstractSet[str],
    bool,
]:
    """Inspect the common runtime/router surfaces used by temporal probes."""
    proof = root / "devtools" / "verification"
    runtime = source_syntax(proof / "block_runtime.py")
    spacetime = source_syntax(proof / "block_spacetime_runtime.py")
    boundary = source_syntax(proof / "spacetime_boundary.py")
    router = source_syntax(
        root / "src" / "number_compiler" / "sequences" / "runtime_router.py"
    )
    imports = router.imports | router.dynamic_imports
    return (
        runtime.identifiers | spacetime.identifiers,
        runtime.imports | spacetime.imports,
        runtime,
        spacetime,
        boundary,
        router,
        imports,
        router.unknown_dynamic_import
        or any(name.endswith("diamond_runtime") for name in imports),
    )


def common_temporal_blockers(
    projection: Sequence[Mapping[str, object]],
    rejection: object,
    metric_int: Callable[[object], int],
) -> list[str]:
    """Collect blocker checks shared by Collatz and reverse temporal probes."""
    blockers: list[str] = []
    if not projection:
        blockers.append("execution_measurements_missing")
    if rejection is not None:
        blockers.append("certified_execution_unavailable")
    if projection and not all(
        metric_int(row["whole_word_sweeps"]) == 0
        and metric_int(row["whole_word_symbol_visits"]) == 0
        and metric_int(row["proof_machine_applications"]) == 0
        for row in projection
    ):
        blockers.append("forbidden_execution_work_observed")
    return blockers
