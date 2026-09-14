"""P0 gates: failure handling is not a completed shadow-cylinder extractor.

These deliberately fail while the production candidate-to-bit construction is
unavailable. They must not be replaced with UNKNOWN expectations or xfails.
"""

import json

import pytest

from number_compiler.api.cli import main
from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler


@pytest.mark.parametrize(
    "family,parameter,status",
    [
        ("fermat", 4, "prime"),
        ("fermat", 5, "composite"),
        ("mersenne", 11, "composite"),
        ("mersenne", 13, "prime"),
    ],
)
def test_candidate_shadow_bit_decides_without_classical_recurrence(
    family: str,
    parameter: int,
    status: str,
) -> None:
    result = CanonicalSequenceCompiler().resolve_special_theorem(family, parameter)
    assert result.decided, "P0: candidate-derived shadow-cylinder prime bit is missing"
    assert result.primality is not None
    assert result.primality.status == status
    assert result.primality.specialization_raw_squarings == 0
    assert result.primality.carrier_states_enumerated == 0
    assert result.primality.scalable_construction
    assert result.etale_ring_multiplications == 0
    assert "classical" not in result.projection_method


@pytest.mark.parametrize(
    "family,parameter,status",
    [
        ("fermat", 4, "prime"),
        ("fermat", 5, "composite"),
        ("mersenne", 11, "composite"),
        ("mersenne", 13, "prime"),
    ],
)
def test_cli_consumes_candidate_shadow_bit(
    family: str,
    parameter: int,
    status: str,
    capsys: pytest.CaptureFixture[str],
) -> None:
    exit_code = main(
        [
            family,
            "--nth",
            str(parameter),
            "--no-value",
            "--info",
            "primality",
            "--format",
            "json",
        ]
    )
    row = json.loads(capsys.readouterr().out)
    primality = row["info"]["primality"]
    assert exit_code == 0, "P0: production CLI cannot recover the candidate prime bit"
    assert primality["decided"] and primality["status"] == status
    assert primality["certificate"]["scalable_construction"]
    assert primality["certificate"]["specialization_raw_squarings"] == 0
    assert primality["certificate"]["carrier_states_enumerated"] == 0
    assert primality["etale_ring_multiplications"] == 0
