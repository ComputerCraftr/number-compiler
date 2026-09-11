"""Immutable Base∘Base factorization of the SHA-verified decimal T² kernel.

The minimized left-state universe has no transition-closed section into raw
functional states. Certification proves a surjection from all reachable raw
states; the retained representative section is used only for the output law.
Transitions continue to use the original verified minimized kernel tables.
No source symbols, seed computation, or future spatial objects enter this work.
"""

from __future__ import annotations

import hashlib
import json
import zlib
from dataclasses import dataclass
from functools import lru_cache
from importlib.resources import files
from pathlib import Path

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import (
    _BASE10_T2_SHA256,
    BaseBlockEffect,
    _load_base10_t2_kernel,
)


@dataclass(frozen=True, slots=True)
class PairPortSection:
    anchor: int
    continuation: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class FactorizationVerification:
    raw_left_states: int
    raw_right_states: int
    transition_checks: int
    output_checks: int


@dataclass(frozen=True, slots=True)
class DecimalT2Factorization:
    """Kernel-definition tables only; section entries are alternative ports."""

    left: tuple[PairPortSection, ...]
    right: tuple[PairPortSection, ...]
    base_left: tuple[tuple[int, ...], ...]
    base_right: tuple[tuple[int, ...], ...]
    base_outputs: bytes
    base_initial: tuple[int, int]
    verification: FactorizationVerification

    def emit(self, left: int, symbol: int, right: int) -> int:
        if any(
            type(value) is not int or not 0 <= value < size
            for value, size in (
                (left, len(self.left)),
                (symbol, 20),
                (right, len(self.right)),
            )
        ):
            raise ValueError("factorized output port outside its finite domain")
        return _emit(self, self.left[left], symbol, self.right[right])


def _base_tables() -> tuple[
    tuple[tuple[int, ...], ...], tuple[tuple[int, ...], ...], bytes, tuple[int, int]
]:
    base = BaseBlockEffect(10)
    left, right = (
        base.boundary_universe(BoundarySide.LEFT),
        base.boundary_universe(BoundarySide.RIGHT),
    )
    assert left is not None and right is not None
    left_ids = {value: index for index, value in enumerate(left)}
    right_ids = {value: index for index, value in enumerate(right)}
    ltable = tuple(
        tuple(
            left_ids[base.advance(BoundarySide.LEFT, value, symbol)]
            for symbol in range(20)
        )
        for value in left
    )
    rtable = tuple(
        tuple(
            right_ids[base.advance(BoundarySide.RIGHT, value, symbol)]
            for symbol in range(20)
        )
        for value in right
    )
    outputs = bytes(
        base.emit(lvalue, symbol, rvalue)
        for lvalue in left
        for symbol in range(20)
        for rvalue in right
    )
    return (
        ltable,
        rtable,
        outputs,
        (
            left_ids[base.initial(BoundarySide.LEFT)],
            right_ids[base.initial(BoundarySide.RIGHT)],
        ),
    )


def _emit(
    factor: DecimalT2Factorization,
    left: PairPortSection,
    symbol: int,
    right: PairPortSection,
) -> int:
    width = len(factor.base_right)
    first = factor.base_outputs[(left.anchor * 20 + symbol) * width + right.anchor]
    lstate = left.continuation[factor.base_right[right.anchor][symbol]]
    rstate = right.continuation[factor.base_left[left.anchor][symbol]]
    return factor.base_outputs[(lstate * 20 + first) * width + rstate]


def _raw_step(
    factor: DecimalT2Factorization,
    side: BoundarySide,
    state: PairPortSection,
    symbol: int,
) -> PairPortSection:
    same, opposite = (
        (factor.base_left, factor.base_right)
        if side is BoundarySide.LEFT
        else (factor.base_right, factor.base_left)
    )
    width = len(factor.base_right)
    values = []
    for argument, row in enumerate(opposite):
        left, right = (
            (state.anchor, argument)
            if side is BoundarySide.LEFT
            else (argument, state.anchor)
        )
        emitted = factor.base_outputs[(left * 20 + symbol) * width + right]
        values.append(same[state.continuation[row[symbol]]][emitted])
    return PairPortSection(same[state.anchor][symbol], tuple(values))


def certify_decimal_t2_factorization() -> DecimalT2Factorization:
    """Exhaustive finite proof generator; production uses the checked artifact."""
    kernel = _load_base10_t2_kernel()
    ltable, rtable, outputs, initial = _base_tables()
    factor = DecimalT2Factorization(
        (), (), ltable, rtable, outputs, initial, FactorizationVerification(0, 0, 0, 0)
    )
    universes: list[dict[PairPortSection, int]] = []
    sections: list[tuple[PairPortSection, ...]] = []
    transition_checks = 0
    for side, count in (
        (BoundarySide.LEFT, kernel.left_count),
        (BoundarySide.RIGHT, kernel.right_count),
    ):
        opposite_size = len(rtable) if side is BoundarySide.LEFT else len(ltable)
        start = PairPortSection(
            initial[int(side)], (initial[int(side)],) * opposite_size
        )
        known = {start: kernel.initial(side)}
        pending = [start]
        representatives: list[PairPortSection | None] = [None] * count
        cursor = 0
        while cursor < len(pending):
            state = pending[cursor]
            cursor += 1
            kernel_id = known[state]
            if representatives[kernel_id] is None:
                representatives[kernel_id] = state
            for symbol in range(20):
                target = _raw_step(factor, side, state, symbol)
                expected = kernel.advance(side, kernel_id, symbol)
                transition_checks += 1
                previous = known.get(target)
                if previous is not None:
                    if previous != expected:
                        raise ValueError(
                            "raw state has conflicting minimized transition images"
                        )
                else:
                    known[target] = expected
                    pending.append(target)
        if any(value is None for value in representatives):
            raise ValueError(
                "factorization does not cover every minimized primitive port"
            )
        sections.append(tuple(value for value in representatives if value is not None))
        universes.append(known)
    output_checks = 0
    # Verify the quotient law for ALL raw representatives, not only the section.
    for left, lid in universes[0].items():
        for right, rid in universes[1].items():
            for symbol in range(20):
                if _emit(factor, left, symbol, right) != kernel.emit(lid, symbol, rid):
                    raise ValueError(
                        "raw output does not descend through the minimized quotient"
                    )
                output_checks += 1
    return DecimalT2Factorization(
        sections[0],
        sections[1],
        ltable,
        rtable,
        outputs,
        initial,
        FactorizationVerification(
            len(universes[0]), len(universes[1]), transition_checks, output_checks
        ),
    )


def factorization_payload(factor: DecimalT2Factorization) -> bytes:
    """Deterministic kernel artifact encoding, never an execution snapshot."""
    value = {
        "format": "decimal-t2-factorization-v1",
        "t2_sha256": _BASE10_T2_SHA256,
        "left": [[entry.anchor, list(entry.continuation)] for entry in factor.left],
        "right": [[entry.anchor, list(entry.continuation)] for entry in factor.right],
        "base_left": factor.base_left,
        "base_right": factor.base_right,
        "base_outputs": factor.base_outputs.hex(),
        "base_initial": factor.base_initial,
        "verification": [
            factor.verification.raw_left_states,
            factor.verification.raw_right_states,
            factor.verification.transition_checks,
            factor.verification.output_checks,
        ],
    }
    return json.dumps(value, separators=(",", ":"), sort_keys=True).encode("ascii")


_FACTORIZATION_SHA256 = (
    "713d853340b48846f0084c695de06ee98094897bcb77e86509b415444f71e770"
)
_FACTORIZATION_PAYLOAD_SHA256 = (
    "e5e5b0922f392f1f762f81c83a58b20a09d79082bda8dfd2b69a7739e38a3e75"
)


def validate_decimal_t2_factorization(value: object) -> bool:
    """Check actual fixed definition content without trusting cached identity."""
    if type(value) is not DecimalT2Factorization:
        return False
    for section, count, same, opposite in (
        (value.left, 757, 43, 5),
        (value.right, 179, 5, 43),
    ):
        if type(section) is not tuple or len(section) != count:
            return False
        for entry in section:
            if (
                type(entry) is not PairPortSection
                or type(entry.anchor) is not int
                or not 0 <= entry.anchor < same
                or type(entry.continuation) is not tuple
                or len(entry.continuation) != opposite
                or any(
                    type(port) is not int or not 0 <= port < same
                    for port in entry.continuation
                )
            ):
                return False
    for table, count in ((value.base_left, 43), (value.base_right, 5)):
        if type(table) is not tuple or len(table) != count:
            return False
        if any(
            type(row) is not tuple
            or len(row) != 20
            or any(type(port) is not int or not 0 <= port < count for port in row)
            for row in table
        ):
            return False
    if (
        type(value.base_outputs) is not bytes
        or len(value.base_outputs) != 4300
        or type(value.base_initial) is not tuple
        or len(value.base_initial) != 2
        or any(
            type(port) is not int or not 0 <= port < count
            for port, count in zip(value.base_initial, (43, 5), strict=True)
        )
        or type(value.verification) is not FactorizationVerification
    ):
        return False
    checks = value.verification
    if any(
        type(count) is not int or count != expected
        for count, expected in (
            (checks.raw_left_states, 1423),
            (checks.raw_right_states, 179),
            (checks.transition_checks, 32040),
            (checks.output_checks, 5094340),
        )
    ):
        return False
    return (
        hashlib.sha256(factorization_payload(value)).hexdigest()
        == _FACTORIZATION_PAYLOAD_SHA256
    )


@lru_cache(maxsize=1)
def load_decimal_t2_factorization() -> DecimalT2Factorization:
    """Share only a deeply immutable checksum-verified kernel definition."""
    _load_base10_t2_kernel()  # Independently checks the original artifact SHA.
    path = (
        Path(str(files("number_compiler"))) / "kernels" / "base10_t2_factorization.zlib"
    )
    packed = path.read_bytes()
    if hashlib.sha256(packed).hexdigest() != _FACTORIZATION_SHA256:
        raise ValueError("decimal T² factorization artifact checksum mismatch")
    data = json.loads(zlib.decompress(packed))
    if (
        data["format"] != "decimal-t2-factorization-v1"
        or data["t2_sha256"] != _BASE10_T2_SHA256
    ):
        raise ValueError("factorization belongs to another primitive kernel")
    factor = DecimalT2Factorization(
        tuple(PairPortSection(entry[0], tuple(entry[1])) for entry in data["left"]),
        tuple(PairPortSection(entry[0], tuple(entry[1])) for entry in data["right"]),
        tuple(tuple(row) for row in data["base_left"]),
        tuple(tuple(row) for row in data["base_right"]),
        bytes.fromhex(data["base_outputs"]),
        tuple(data["base_initial"]),
        FactorizationVerification(*data["verification"]),
    )
    if (
        factor.base_left,
        factor.base_right,
        factor.base_outputs,
        factor.base_initial,
    ) != _base_tables():
        raise ValueError("factorization does not bind the current complete Base kernel")
    if not validate_decimal_t2_factorization(factor):
        raise ValueError(
            "factorization content does not match its certified definition"
        )
    return factor
