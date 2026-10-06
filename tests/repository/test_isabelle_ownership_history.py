"""Ownership history is checked navigation data, never build acceptance."""

import json
from pathlib import Path

import pytest

from devtools.checks.isabelle_ownership_history import ownership_history
from devtools.checks.isabelle_source_analysis import analyze_isabelle_source
from devtools.checks.isabelle_syntax import Session


@pytest.mark.parametrize("defect", [None, "path", "declaration", "duplicate"])
def test_migration_history_checks_current_owners(
    tmp_path: Path, defect: str | None
) -> None:
    relative = "proofs/isabelle/shared/carry/core/Core.thy"
    source = tmp_path / relative
    analysis = analyze_isabelle_source(
        'theory Core imports Main begin\nlemma retained: "True" by simp\nend\n',
        source,
    )
    record = {
        "session": "Core",
        "new_session_path": "proofs/isabelle/shared/carry/core"
        if defect != "path"
        else "old",
    }
    history = {
        "schema_version": 1,
        "sessions_by_old_path": {"proofs/isabelle/old": record},
        "new_sessions": [record] if defect == "duplicate" else [],
        "declaration_extraction_claims": [
            {
                "destinations": [
                    {
                        "path": relative,
                        "declarations": [
                            "missing" if defect == "declaration" else "retained"
                        ],
                    }
                ],
            }
        ],
    }
    path = tmp_path / "devtools/checks/isabelle_ownership_history.json"
    path.parent.mkdir(parents=True)
    path.write_text(json.dumps(history))
    sessions = (Session("Core", Path("shared/carry/core"), "HOL", (), ("Core",)),)
    if defect:
        with pytest.raises(ValueError):
            ownership_history(tmp_path, sessions, {source: analysis}, {})
    else:
        assert ownership_history(tmp_path, sessions, {source: analysis}, {}) == history
