"""Installed physical-field controls for the bounded H moving cut."""

from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path
from typing import Any, cast

import pytest


def _field(
    seed: int, generation: int, places: int, expected_exit: int = 0
) -> dict[str, Any]:
    python = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if python is None:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to an installed wheel")
    environment = os.environ.copy()
    environment.pop("PYTHONPATH", None)
    environment.pop("PYTHONHOME", None)
    completed = subprocess.run(
        [
            str(Path(python).with_name("number-compiler")),
            "5rev10",
            "--seed",
            str(seed),
            "--nth",
            str(generation),
            "--no-value",
            "--info",
            "arithmetic.modular",
            "--arithmetic-modular-kind",
            "digit-field",
            "--arithmetic-modular-places",
            str(places),
            "--format",
            "json",
        ],
        check=False,
        capture_output=True,
        text=True,
        timeout=30,
        env=environment,
    )
    assert completed.returncode == expected_exit, completed.stderr
    packet = json.loads(completed.stdout)
    return cast(
        dict[str, Any], packet["info"]["arithmetic.modular"]["views"]["digit-field"]
    )


def test_installed_large_field_retains_bounded_refusal() -> None:
    two = _field(196, 9967, 2)
    assert two["status"] == "available"
    assert two["value"]["field_residue"] == 175
    assert two["value"]["source_occurrences_materialized"] is False
    three = _field(196, 9967, 3, expected_exit=3)
    assert three["status"] == "unavailable"
    assert three["value"]["reason"] == "physical low band exceeds the source budget"


def test_installed_third_place_distinguishes_equal_mod225() -> None:
    two, eleven = _field(2, 1, 3), _field(11, 1, 3)
    assert two["status"] == eleven["status"] == "available"
    assert two["value"]["field_residue225"] == eleven["value"]["field_residue225"] == 50
    assert (two["value"]["field_residue"], eleven["value"]["field_residue"]) == (
        50,
        275,
    )
