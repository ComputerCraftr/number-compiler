"""Scalar consumers use canonical admission and envelopes without observers."""

import subprocess
import sys
from dataclasses import replace
from typing import Never

import pytest

from number_compiler.api import cli, family_registry
from number_compiler.api.family_types import AdapterBinding
from number_compiler.api.number_api import NumberCompiler
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.family_identity import FamilyId


def test_cold_scalar_cli_does_not_import_projected_or_observation_owners() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-c",
            "import sys; from number_compiler.api.cli import main; "
            "assert main(['prime', '--nth', '20']) == 0; "
            "assert 'number_compiler.api.number_api' not in sys.modules; "
            "assert 'number_compiler.api.cli_context' not in sys.modules; "
            "assert 'number_compiler.api.observation_adapters' not in sys.modules",
        ],
        capture_output=True,
        text=True,
        check=True,
    )
    assert completed.stdout.strip() == "73"


@pytest.mark.parametrize(
    "arguments",
    (
        ["prime", "--nth", "20", "--format", "json"],
        ["prime", "--start", "100", "--nth", "0"],
        ["prime", "--nth", "40", "--max-prime-work", "1"],
        ["prime", "--nth", "20", "--max-output-bits", "1"],
    ),
)
def test_scalar_and_projected_cli_envelopes_agree(
    arguments: list[str],
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    fast_status = cli.main(arguments, shared_cache=False)
    fast_output = capsys.readouterr()
    specification = family_registry.CAPABILITIES[FamilyId.PRIME]
    monkeypatch.setattr(
        family_registry,
        "CAPABILITIES",
        dict(family_registry.CAPABILITIES)
        | {FamilyId.PRIME: replace(specification, scalar_value=None)},
    )
    assert cli.main(arguments, shared_cache=False) == fast_status
    assert capsys.readouterr() == fast_output


def test_scalar_value_avoids_projected_context(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("scalar value constructed an observation context")

    monkeypatch.setattr(NumberCompiler, "project", forbidden)
    assert cli.main(["prime", "--nth", "20"], shared_cache=False) == 0
    assert capsys.readouterr().out.strip() == "73"


@pytest.mark.parametrize(
    "error",
    (
        BlockContextBudgetExceeded("cache budget exceeded"),
        OverflowError("output is too large"),
    ),
)
def test_scalar_resource_failure_keeps_the_cli_error_contract(
    error: Exception,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    def fail(*args: object, **kwargs: object) -> Never:
        raise error

    monkeypatch.setattr("number_compiler.api.projections.prime_value.value", fail)
    assert cli.main(["prime", "--nth", "0"]) == 2
    captured = capsys.readouterr()
    assert not captured.out
    assert str(error) in captured.err
    assert "Traceback" not in captured.err


def test_scalar_binding_requires_a_callable_with_the_declared_shape(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    specification = family_registry.CAPABILITIES[FamilyId.PRIME]
    monkeypatch.setattr(
        family_registry,
        "CAPABILITIES",
        dict(family_registry.CAPABILITIES)
        | {
            FamilyId.PRIME: replace(
                specification,
                scalar_value=AdapterBinding("builtins", "int"),
            )
        },
    )
    assert cli.main(["prime", "--nth", "0"]) == 2
    assert "incompatible interface" in capsys.readouterr().err


def test_scalar_binding_is_registry_selected_and_observations_use_projection(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    calls: list[bool] = []

    def value(query: object, shared_cache: bool) -> int:
        calls.append(shared_cache)
        return 101

    monkeypatch.setattr("number_compiler.api.projections.prime_value.value", value)
    assert cli.main(["prime", "--nth", "0"], shared_cache=False) == 0
    assert capsys.readouterr().out.strip() == "101"
    assert calls == [False]
    assert cli.main(["prime", "--nth", "0", "--info", "metrics"]) == 0
    captured = capsys.readouterr()
    assert captured.out.strip() == "2"
    assert "metrics" in captured.err
    assert calls == [False]
