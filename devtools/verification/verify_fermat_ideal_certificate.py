"""Verify a validation-only bounded Fermat/Pépin reference witness.

Usage: ``PYTHONPATH=src python devtools/verification/verify_fermat_ideal_certificate.py proof.json``
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from devtools.benchmarks.report_schema import sequence
from devtools.report_values import object_list, string_keyed_mapping
from devtools.verification.fermat_integral_ideal_reference import (
    FermatIntegralIdealWitness,
)

MAX_CERTIFICATE_BYTES = 2_000_000


def _decode_int(value: object) -> int:
    if type(value) is not str or len(value) > 65_536:
        raise ValueError("invalid or oversized integer encoding")
    if not value.startswith(("-0x", "0x")):
        raise ValueError("only signed hexadecimal proof integers are accepted")
    try:
        return int(value, 0)
    except ValueError as error:
        raise ValueError("invalid hexadecimal proof integer") from error


def _parse_vector(value: object, *, maximum: int) -> tuple[int, ...]:
    if not object_list(value) or len(value) > maximum:
        raise ValueError("invalid bounded proof vector")
    return tuple(_decode_int(item) for item in sequence(value))


def _signed_digit(value: object) -> int:
    if type(value) is not int or value not in (-1, 0, 1):
        raise ValueError("invalid signed output vector")
    return value


def verify(path: str | Path) -> dict[str, object]:
    source_path = Path(path)
    with source_path.open("rb") as certificate_file:
        payload = certificate_file.read(MAX_CERTIFICATE_BYTES + 1)
    if len(payload) > MAX_CERTIFICATE_BYTES:
        raise ValueError("certificate exceeds the file-size budget")
    raw_data: object = json.loads(payload)
    data = string_keyed_mapping(raw_data)
    if data is None:
        raise ValueError("unsupported certificate scheme")
    if data.get("scheme") != "fermat-integral-ideal-v1":
        raise ValueError("unsupported certificate scheme")
    index, level, claimed_width = (
        data.get("index"),
        data.get("level"),
        data.get("width"),
    )
    if type(index) is not int or not 1 <= index <= 6:
        raise ValueError("source width is outside the verifier budget")
    if type(level) is not int or not 0 <= level <= 15:
        raise ValueError("source level is outside the verifier budget")
    width = 1 << index
    if type(claimed_width) is not int or claimed_width != width:
        raise ValueError("claimed source width does not match the Fermat index")
    raw_digits = data.get("signed_digits")
    if not object_list(raw_digits):
        raise ValueError("invalid signed output vector")
    digits_raw = sequence(raw_digits)
    if len(digits_raw) != width:
        raise ValueError("invalid signed output vector")
    derivation = data.get("derivation")
    if type(derivation) is not str:
        raise ValueError("source derivation is missing")
    witness = FermatIntegralIdealWitness(
        index,
        level,
        _parse_vector(data.get("folded_hex"), maximum=width),
        _parse_vector(data.get("carry_hex"), maximum=width + 1),
        tuple(_signed_digit(digit) for digit in digits_raw),
        derivation=derivation,
    )
    status = witness.terminal_result()
    return {
        "scheme": "fermat-integral-ideal-v1",
        "index": index,
        "width": width,
        "status": status,
        "source_recomputed": True,
        "integer_carry_cochain_verified": True,
        "binomial_terms_checked": witness.exponent + 1,
        "modular_squarings": 0,
    }


def main() -> int:
    if len(sys.argv) != 2:
        raise SystemExit("Usage: verify_fermat_ideal_certificate.py PROOF.json")
    try:
        print(json.dumps(verify(sys.argv[1]), indent=2))
    except (OSError, TypeError, ValueError) as error:
        print(f"INVALID: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
