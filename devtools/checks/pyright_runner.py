"""Run a full Pyright source sweep as serialized guarded batches."""

from __future__ import annotations

import json
from collections.abc import Mapping
from pathlib import Path
from typing import TYPE_CHECKING, Protocol

from devtools.checks.pyright_policy import (
    MAX_PYRIGHT_BATCH_FILES,
    PYRIGHT_OUTPUT_LIMIT_BYTES,
    diagnostics_are_clean,
    node_executable,
    pinned_pyright_version,
    pyright_batches,
    pyright_command,
    pyright_entrypoint,
    pyright_sources,
    validate_pyright_output,
)
from devtools.checks.validation_policy import PYTHON_COMMAND, ExecutionPolicy
from number_compiler.arithmetic.contracts.input_validation import (
    is_object_list,
    string_keyed_mapping,
)

if TYPE_CHECKING:
    from devtools.runs import EvidenceRun


class ExecuteCommand(Protocol):
    def __call__(
        self,
        run: EvidenceRun,
        name: str,
        command: tuple[str, ...],
        policy: ExecutionPolicy = PYTHON_COMMAND,
        *,
        acceptance: bool = False,
        record_fields: Mapping[str, object] | None = None,
        output_limit_bytes: int = 8 * 1024**2,
    ) -> bool: ...


def capture_batch_diagnostics(
    *,
    log_path: Path,
    diagnostics_path: Path,
    process_outcome: object,
) -> tuple[object | None, bool, str | None]:
    """Keep a batch incomplete whenever its process or JSON is incomplete."""
    if process_outcome == "output_limit":
        limit_megabytes = PYRIGHT_OUTPUT_LIMIT_BYTES // 1024**2
        return (
            None,
            False,
            f"Pyright output exceeded its {limit_megabytes} MiB retention limit",
        )
    if not isinstance(process_outcome, str) or process_outcome not in {
        "completed",
        "child_failed",
    }:
        return None, False, f"Pyright process ended as {process_outcome!r}"
    try:
        payload: object = json.loads(log_path.read_text(encoding="utf-8"))
        diagnostics_path.write_text(
            json.dumps(payload, indent=2) + "\n", encoding="utf-8"
        )
    except (OSError, json.JSONDecodeError) as error:
        return None, False, f"complete Pyright JSON output unavailable: {error}"
    return payload, True, None


def _write_report(run: EvidenceRun, report: Mapping[str, object]) -> None:
    (run.path / "pyright-diagnostics.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8"
    )


def run_pyright_quality(
    run: EvidenceRun,
    *,
    execute: ExecuteCommand,
    acceptance: bool = False,
) -> bool:
    """Check every discovered source in deterministic guarded batches."""
    root = run.root
    sources = pyright_sources(root)
    batches = pyright_batches(sources)
    node = node_executable()
    try:
        expected_version = pinned_pyright_version(root)
        entrypoint = pyright_entrypoint(root)
    except (OSError, RuntimeError, ValueError) as error:
        entrypoint = None
        expected_version = None
        detail = str(error)
    else:
        detail = ""
    reason = (
        detail or "Node was not found; set NUMBER_COMPILER_NODE or add Node to PATH"
    )
    if node is None or entrypoint is None:
        run.record(
            {
                "name": "pyright-availability",
                "outcome": "unavailable",
                "detail": reason,
                "source_count": len(sources),
                "batch_count": len(batches),
            }
        )
        _write_report(
            run,
            {
                "complete": False,
                "tool_version": None,
                "source_count": len(sources),
                "covered_source_count": 0,
                "batch_size_limit": MAX_PYRIGHT_BATCH_FILES,
                "batches": [],
                "error": reason,
            },
        )
        return False

    if not sources:
        run.record(
            {
                "name": "pyright-availability",
                "outcome": "incomplete",
                "detail": "source discovery returned no Python files",
            }
        )
        _write_report(
            run,
            {
                "complete": False,
                "tool_version": expected_version,
                "source_count": 0,
                "covered_source_count": 0,
                "batch_count": 0,
                "batch_size_limit": MAX_PYRIGHT_BATCH_FILES,
                "batches": [],
            },
        )
        return False

    batch_records: list[dict[str, object]] = []
    covered: list[str] = []
    passed = True
    for index, batch in enumerate(batches, start=1):
        name = f"pyright-{index:04d}"
        file_names = [path.relative_to(root).as_posix() for path in batch]
        covered.extend(file_names)
        command = pyright_command(root, batch, node=node)
        process_passed = execute(
            run,
            name,
            command,
            acceptance=acceptance,
            record_fields={
                "batch_index": index,
                "batch_count": len(batches),
                "source_count": len(batch),
                "source_files": file_names,
                "node_heap_megabytes": 2048,
            },
            output_limit_bytes=PYRIGHT_OUTPUT_LIMIT_BYTES,
        )
        log_path = run.path / f"{name}.log"
        execution_record_path = run.path / f"{name}.json"
        diagnostics_path = run.path / f"{name}.diagnostics.json"
        try:
            execution_record: object = json.loads(
                execution_record_path.read_text(encoding="utf-8")
            )
        except (OSError, json.JSONDecodeError):
            execution_record = None
        execution_data = string_keyed_mapping(execution_record)
        process_outcome = (
            execution_data.get("process_outcome")
            if execution_data is not None
            else None
        )
        output_limit_reached = process_outcome == "output_limit"
        payload, payload_parsed, parse_error = capture_batch_diagnostics(
            log_path=log_path,
            diagnostics_path=diagnostics_path,
            process_outcome=process_outcome,
        )
        summary, validation_error = (
            validate_pyright_output(
                payload,
                expected_version=expected_version,
                expected_root_count=len(batch),
            )
            if payload_parsed and expected_version is not None
            else (None, "Pyright output cannot be validated without a pinned version")
        )
        diagnostics_complete = payload_parsed and validation_error is None
        if parse_error is None and validation_error is not None:
            parse_error = validation_error
        diagnostic_data = string_keyed_mapping(payload)
        raw_diagnostics = (
            diagnostic_data.get("generalDiagnostics")
            if diagnostic_data is not None
            else None
        )
        has_findings = is_object_list(raw_diagnostics) and bool(raw_diagnostics)
        clean = diagnostics_complete and diagnostics_are_clean(payload)
        if not diagnostics_complete:
            batch_outcome = "incomplete"
        elif has_findings:
            batch_outcome = "findings"
        elif process_passed and clean:
            batch_outcome = "clean"
        else:
            batch_outcome = "incomplete"
        batch_records.append(
            {
                "batch_index": index,
                "source_files": file_names,
                "process_passed": process_passed,
                "outcome": batch_outcome,
                "diagnostics_clean": clean,
                "diagnostics_complete": diagnostics_complete,
                "output_limit_reached": output_limit_reached,
                "parse_error": parse_error,
                "diagnostics_file": diagnostics_path.name if payload_parsed else None,
                "diagnostic_summary": summary,
            }
        )
        run.record(
            {
                "name": f"{name}-diagnostics",
                "outcome": batch_outcome,
                "source_count": len(batch),
                "source_files": file_names,
                "complete_json": diagnostics_complete,
                "output_limit_reached": output_limit_reached,
                "parse_error": parse_error,
                "diagnostic_summary": summary,
                "diagnostics_file": diagnostics_path.name if payload_parsed else None,
            }
        )
        passed = process_passed and clean and passed
        _write_report(
            run,
            {
                "complete": False,
                "tool_version": expected_version,
                "node_executable": str(node),
                "source_count": len(sources),
                "covered_source_count": len(covered),
                "batch_count": len(batches),
                "batch_size_limit": MAX_PYRIGHT_BATCH_FILES,
                "batches": batch_records,
            },
        )

    expected = {path.relative_to(root).as_posix() for path in sources}
    files_assigned_complete = (
        len(covered) == len(sources)
        and len(set(covered)) == len(sources)
        and set(covered) == expected
    )
    diagnostics_complete = all(
        row["diagnostics_complete"] is True for row in batch_records
    )
    complete_coverage = files_assigned_complete and diagnostics_complete
    complete = complete_coverage and len(batch_records) == len(batches)
    _write_report(
        run,
        {
            "complete": complete,
            "tool_version": expected_version,
            "node_executable": str(node),
            "source_count": len(sources),
            "covered_source_count": len(covered),
            "batch_count": len(batches),
            "batch_size_limit": MAX_PYRIGHT_BATCH_FILES,
            "files_assigned_complete": files_assigned_complete,
            "diagnostics_complete": diagnostics_complete,
            "coverage_complete": complete_coverage,
            "batches": batch_records,
        },
    )
    run.record(
        {
            "name": "pyright-coverage",
            "outcome": "complete" if complete_coverage else "incomplete",
            "source_count": len(sources),
            "covered_source_count": len(covered),
            "batch_count": len(batches),
            "batch_size_limit": MAX_PYRIGHT_BATCH_FILES,
            "diagnostics_path": str(run.path / "pyright-diagnostics.json"),
        }
    )
    return passed and complete
