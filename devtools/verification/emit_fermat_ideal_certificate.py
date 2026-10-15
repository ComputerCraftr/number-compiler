"""Emit a validation-only bounded integer Fermat/Pépin witness.

Usage: ``PYTHONPATH=src python devtools/verification/emit_fermat_ideal_certificate.py 4 F4.json``

This reconstructive reference is not a production primality path. No modular
exponentiation or primality oracle is used. F5 is refused at the explicit
binomial-source term budget.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from devtools.verification.fermat_integral_ideal_reference import (
    FermatIntegralIdealWitness,
)


def _hex(value: int) -> str:
    return f"-0x{-value:x}" if value < 0 else f"0x{value:x}"


def emit(index: int, output: str | Path, *, max_terms: int = 65_536) -> str:
    witness = FermatIntegralIdealWitness.from_source(index, max_terms=max_terms)
    status = witness.terminal_result(max_terms=max_terms)
    payload = {
        "scheme": "fermat-integral-ideal-v1",
        "source": "(1+z)^(2^(w-1)); integer binomial recurrence; z^w=-1",
        "index": witness.index,
        "level": witness.level,
        "width": witness.width,
        "folded_hex": [_hex(value) for value in witness.folded],
        "carry_hex": [_hex(value) for value in witness.carries],
        "signed_digits": list(witness.signed_digits),
        "identity": "P-E=(D-c0)*(z^w+1)+(2-z)*C",
        "derivation": witness.derivation,
    }
    Path(output).write_text(json.dumps(payload, indent=2) + "\n")
    return status


def main() -> int:
    if len(sys.argv) != 3:
        raise SystemExit("Usage: emit_fermat_ideal_certificate.py INDEX OUTPUT.json")
    try:
        print(emit(int(sys.argv[1]), sys.argv[2]))
    except (ValueError, ArithmeticError) as error:
        print(f"UNAVAILABLE: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
