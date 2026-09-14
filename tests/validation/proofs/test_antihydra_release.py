"""Unweakened P0 gates: finite observations cannot substitute for these claims."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from number_compiler.api.cli import main
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.antihydra.observers import SpaceTimeProjection
from number_compiler.sequences.antihydra.runtime import run

pytestmark = pytest.mark.validation


def test_source7_has_installed_cli_nonhalting_certificate(
    capsys: pytest.CaptureFixture[str],
) -> None:
    root = Path(__file__).resolve().parents[3]
    certificate = root / "results" / "certificates" / "antihydra-source7.json"
    assert certificate.is_file(), "P0: no accepted source-7 non-halting certificate"
    assert main(["antihydra", "--verify-nonhalting", str(certificate)]) == 0
    result = json.loads(capsys.readouterr().out)
    assert result["nonhalting_certified"] is True


def test_spacetime_reads_retained_powered_support_without_macro_rediscovery() -> None:
    result = run(64)
    SpaceTimeProjection(result, 2, 2, -1, 1, 3, 100000).evaluate()
    assert result.ledger.counters.get("observer_macro_discovery_steps", 0) == 0, (
        "P0: demanded event support still rediscovers the macro section stream"
    )


def test_retained_cylinders_pass_shared_payload_admission() -> None:
    result = run(64)
    audit = audit_registered_payloads(result.ledger)
    assert (
        audit.forbidden_future_payloads,
        audit.unbounded_future_integers,
        audit.unknown_payloads,
    ) == (0, 0, 0), f"P0: Antihydra retained payload admission is incomplete: {audit}"
