"""Independent digit and phase oracles for the nondecimal source cutover."""

from __future__ import annotations

import random

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add import small_radix
from number_compiler.sequences.reverse_add.binary_phase import BinaryPhase, recognize
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.source_images import (
    ReverseSourceImageWorkspace,
)


def literal(source: bytes, base: int, steps: int) -> bytes:
    for _ in range(steps):
        result = bytearray()
        carry = 0
        for a, b in zip(source, reversed(source), strict=True):
            carry, d = divmod(a + b + carry, base)
            result.append(d)
        if carry:
            result.append(carry)
        source = bytes(result)
    return source


def as_digits(x: int, base: int) -> bytes:
    out = bytearray()
    while True:
        x, r = divmod(x, base)
        out.append(r)
        if not x:
            return bytes(out)


@pytest.mark.parametrize("base", (2, 3))
def test_word_planes(base: int) -> None:
    rng = random.Random(1024 + base)
    native = small_radix.native_kernel()
    for width in (
        1,
        2,
        3,
        5,
        8,
        15,
        31,
        32,
        33,
        62,
        63,
        64,
        65,
        66,
        95,
        127,
        128,
        129,
        191,
        256,
        257,
    ):
        for _ in range(20):
            source = bytes(
                [rng.randrange(base) for _ in range(width - 1)]
                + [rng.randrange(1, base)]
            )
            steps = rng.randrange(1, 80)
            expected = literal(source, base, steps)
            portable, counts = small_radix.portable_advance(source, base, steps)
            assert portable == expected
            assert counts[0] == steps and counts[3] == len(expected) - width
            if native is not None:
                assert native.add_small_radix(source, base, steps) == (expected, counts)


def test_binary_phase_and_nine_ports() -> None:
    for k in range(2, 101):
        for p in range(4):
            phase = BinaryPhase(k, p)
            digits = bytes(phase.iter_digits())
            x = int("".join(str(d) for d in reversed(digits)), 2)
            rev = int("".join(str(d) for d in digits), 2)
            y = x + rev
            assert bytes(phase.jump(1).iter_digits()) == literal(digits, 2, 1)
            assert recognize(digits) == phase
            assert tuple(phase.digit(i) for i in range(phase.width)) == tuple(digits)
            expected = (
                x,
                rev,
                x & rev,
                rev & ~x,
                x & ~rev,
                y & ~x,
                x & ~y,
                x ^ rev ^ y,
                y,
            )
            for m in (1, 2, 3, 4, 5, 6, 17, 1_000_003):
                action = phase.modular_action(m)
                assert action.ports() == tuple(v % m for v in expected)
                assert action.carry == y >> phase.width
                assert action.jump(123).jump(456) == phase.jump(579).modular_action(m)


@pytest.mark.parametrize(
    "seed,entry,phase", ((22, 8, BinaryPhase(2, 0)), (1, 21, BinaryPhase(5, 0)))
)
def test_certified_source_bypasses_physical_replay(
    seed: int, entry: int, phase: BinaryPhase, monkeypatch: pytest.MonkeyPatch
) -> None:
    assert literal(as_digits(seed, 2), 2, entry) == bytes(phase.iter_digits())

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("certified source entered physical execution")

    monkeypatch.setattr(small_radix, "portable_advance", forbidden)
    monkeypatch.setattr(small_radix, "_reflect", forbidden)
    monkeypatch.setattr(small_radix, "native_kernel", forbidden)
    for horizon in (entry, 1000, 10**80 + 1):
        term = ReverseAddPoweredTerm(seed, horizon, base=2)
        expected = phase.jump(horizon - entry)
        try:
            assert term.width() == expected.width
            for i in (0, 1, expected.width // 2, expected.width - 1):
                assert term.digit(i) == expected.digit(i)
            k, p = expected.k, expected.phase
            m = 1_000_003
            t = pow(2, k, m)
            a, b, c = ((48, -6, 0), (48, 18, -3), (96, -12, 0), (96, 12, -3))[p]
            assert term.modular_residue(m) == (a * t * t + b * t + c) % m
            assert (
                term.resource_ledger.counters.get(
                    "reverse_small_radix_physical_rows", 0
                )
                == 0
            )
            workspace = term.source_workspace()
            assert workspace.ledger.audit_payload_contracts().owns_root(
                "reverse_add", workspace
            )
        finally:
            workspace = term.source_workspace()
            workspace.dispose()
            assert workspace.ledger.nodes == workspace.ledger.entries == 0


@pytest.mark.parametrize("base", (2, 3))
@pytest.mark.parametrize("seed", (0, 1, 3, 22, 196, 32767))
def test_long_source_owner(base: int, seed: int) -> None:
    for steps in (129, 257, 1024):
        workspace = ReverseSourceImageWorkspace(
            ResourceLedger(), seed, steps, base=base
        )
        try:
            expected = literal(as_digits(seed, base), base, steps)
            assert bytes(workspace.iter_digits()) == expected
            assert workspace.width() == len(expected)
            assert workspace.digit(0) == expected[0]
            assert (
                workspace.modular_residue(97)
                == sum(d * pow(base, i, 97) for i, d in enumerate(expected)) % 97
            )
            assert workspace.ledger.audit_payload_contracts().owns_root(
                "reverse_add", workspace
            )
            if base == 3 and seed:
                assert (
                    workspace.ledger.counters["reverse_small_radix_physical_rows"]
                    == steps
                )
        finally:
            workspace.dispose()
            assert workspace.ledger.nodes == workspace.ledger.entries == 0


def test_bounded_entry_and_portable(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(small_radix, "native_kernel", lambda: None)
    for base, seed, steps in ((2, 196, 1000), (2, 12345, 257), (3, 196, 257)):
        workspace = ReverseSourceImageWorkspace(
            ResourceLedger(), seed, steps, base=base
        )
        try:
            assert bytes(workspace.iter_digits()) == literal(
                as_digits(seed, base), base, steps
            )
            counters = workspace.ledger.counters
            if base == 2 and seed == 196:
                assert counters["reverse_small_radix_binary_entry_rows"] == 6
                assert counters["reverse_small_radix_physical_rows"] == 6
            else:
                assert counters["reverse_small_radix_physical_rows"] == steps
            assert workspace.ledger.audit_payload_contracts().owns_root(
                "reverse_add", workspace
            )
        finally:
            workspace.dispose()
            assert workspace.ledger.nodes == workspace.ledger.entries == 0


def test_generic_finite_budget_refusal() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 10**8, base=3)
    try:
        with pytest.raises(BlockContextBudgetExceeded):
            workspace.width()
    finally:
        workspace.dispose()
        assert workspace.ledger.nodes == workspace.ledger.entries == 0
