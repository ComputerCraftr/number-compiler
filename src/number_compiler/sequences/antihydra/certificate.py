"""Independent rational checker for inductive affine dyadic chart certificates.

No transition-coverage assertion is trusted. Both next-bit branches are checked
by exact nonnegative linear combinations. A successful arithmetic certificate
still needs the literal-TM macro refinement theorem before a TM verdict exists.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Any

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.sequences.antihydra.machine import MACHINE_SHA256

Row = tuple[Fraction, Fraction, Fraction]


def rational(value: object) -> Fraction:
    if type(value) is int:
        if value.bit_length() > 4096:
            raise ValueError("certificate coefficient exceeds bit budget")
        return Fraction(value)
    if type(value) is str and len(value) <= 1024:
        parts = value.split("/")
        if len(parts) not in (1, 2) or any(
            not p or not p.lstrip("-").isascii() or not p.lstrip("-").isdigit()
            for p in parts
        ):
            raise ValueError("expected an exact rational certificate coefficient")
        try:
            return Fraction(value)
        except (ValueError, ZeroDivisionError) as exc:
            raise ValueError("invalid rational certificate coefficient") from exc
    raise ValueError("expected an exact rational certificate coefficient")


def row(value: object) -> Row:
    if not isinstance(value, list) or len(value) != 3:
        raise ValueError("chart inequality must have three coefficients")
    return rational(value[0]), rational(value[1]), rational(value[2])


def check_implication(premises: list[Row], target: Row, weights: object) -> None:
    """Farkas sufficient witness: target is a nonnegative combination."""
    if not isinstance(weights, list) or len(weights) != len(premises):
        raise ValueError("missing inequality implication witness")
    factors = [rational(w) for w in weights]
    if any(w < 0 for w in factors):
        raise ValueError("negative implication multiplier")
    actual = tuple(
        sum((w * p[i] for w, p in zip(factors, premises)), Fraction(0))
        for i in range(3)
    )
    if actual != target:
        raise ValueError("inequality implication does not match its target")


def verify(data: object) -> dict[str, object]:
    if not isinstance(data, dict) or data.get("schema") != "antihydra-affine-charts-v1":
        raise ValueError("unsupported non-halting certificate schema")
    if data.get("machine_sha256") != MACHINE_SHA256 or data.get("source") != "blank":
        raise ValueError("certificate is not bound to the pinned blank-tape machine")
    bits = require_integer(data.get("bits"), "chart precision", 1, 16)
    charts = data.get("charts")
    if not isinstance(charts, list) or not 1 <= len(charts) <= 256:
        raise ValueError("certificate requires 1..256 charts")
    modulus = 1 << bits
    constraints: list[list[Row]] = []
    residues: list[int] = []
    for chart in charts:
        match chart:
            case dict():
                pass
            case _:
                raise ValueError("invalid chart")
        residue = require_integer(chart.get("residue"), "chart residue", 0, modulus - 1)
        inequalities = chart.get("inequalities")
        if not isinstance(inequalities, list) or len(inequalities) > 16:
            raise ValueError("at most sixteen affine inequalities per chart")
        residues.append(residue)
        constraints.append(
            [
                row([1, 0, 0]),
                row([0, 1, 0]),
                row([modulus, 0, residue - 8]),
                row([0, 0, 1]),
            ]
            + [row(v) for v in inequalities]
        )
    initial = require_integer(data.get("initial"), "initial chart", 0, len(charts) - 1)
    if 8 % modulus != residues[initial]:
        raise ValueError("initial chart has the wrong source residue")
    if any(
        x * (8 // modulus) + constant < 0 for x, _, constant in constraints[initial]
    ):
        raise ValueError("initial source is outside the proposed invariant")
    checks = 0
    for index, chart in enumerate(charts):
        branches = chart.get("branches")
        if not isinstance(branches, list) or len(branches) != 2:
            raise ValueError("both next source-bit branches must be covered")
        for bit, branch in enumerate(branches):
            match branch:
                case dict():
                    pass
                case _:
                    raise ValueError("invalid successor branch")
            destination = require_integer(
                branch.get("target"), "target chart", 0, len(charts) - 1
            )
            residue = residues[index]
            bias = (3 * (modulus * bit + residue) - (residue & 1)) // 2
            lift, remainder = divmod(bias, modulus)
            if residues[destination] != remainder:
                raise ValueError("target chart violates exact successor residue")
            delta = 2 - 3 * (residue & 1)
            # x=2*y+bit; y>=0 follows integer source chart x>=0.
            premises = [(2 * x, a, x * bit + c) for x, a, c in constraints[index]]
            premises.append(row([1, 0, 0]))
            targets = [
                (3 * x, a, x * lift + a * delta + c)
                for x, a, c in constraints[destination]
            ]
            witnesses = branch.get("witnesses")
            if not isinstance(witnesses, list) or len(witnesses) != len(targets):
                raise ValueError("missing successor inequality witnesses")
            for target, witness in zip(targets, witnesses):
                check_implication(premises, target, witness)
                checks += 1
    return {
        "status": "ARITHMETIC_INVARIANT_VERIFIED",
        "machine_sha256": MACHINE_SHA256,
        "source": "blank",
        "charts": len(charts),
        "inequality_checks": checks,
        "nonhalting_certified": False,
        "missing_proof_bridge": "literal_TM_to_all_admitted_macro_returns",
    }


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for key, value in pairs:
        if key in out:
            raise ValueError("duplicate certificate JSON key")
        out[key] = value
    return out


def verify_file(path: str) -> dict[str, object]:
    try:
        with Path(path).open("rb") as stream:
            raw = stream.read(1_048_577)
    except OSError as exc:
        raise ValueError(f"cannot read certificate: {exc.strerror}") from exc
    if len(raw) > 1_048_576:
        raise ValueError("certificate exceeds one MiB input budget")
    try:
        data = json.loads(raw, object_pairs_hook=_unique_object)
    except (ValueError, UnicodeError, RecursionError) as exc:
        raise ValueError("invalid certificate JSON") from exc
    return verify(data)
