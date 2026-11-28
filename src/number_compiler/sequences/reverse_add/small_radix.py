"""Exact packed Q3/Q5 physical images and the certified binary phase consumer.

The general kernel is spatial word-RAM, not temporal powering. Only the
source-admitted binary phase grammar (and the zero fixed point) skips time.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator, Sequence
from dataclasses import dataclass
from functools import cache
from importlib import import_module
from typing import Protocol, cast

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.kernels import native_reverse_enabled
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as keys

from .binary_phase import BinaryPhase, admit, recognize_packed


class _Native(Protocol):
    def add_small_radix(
        self, source: bytes, base: int, steps: int
    ) -> tuple[bytes, tuple[int, int, int, int]]: ...


@cache
def native_kernel() -> _Native | None:
    try:
        module = import_module("number_compiler.kernels._reverse_quotients")
    except ModuleNotFoundError as error:
        if error.name != "number_compiler.kernels._reverse_quotients":
            raise
        return None
    return cast(_Native, module) if hasattr(module, "add_small_radix") else None


@dataclass(frozen=True, slots=True)
class SmallRadixImage:
    base: int
    phase: BinaryPhase | None = None
    digits: bytes | None = None

    def __post_init__(self) -> None:
        if type(self.base) is not int or self.base not in (2, 3):
            raise ValueError("unsupported small radix")
        if self.phase is not None:
            if (
                self.base != 2
                or type(self.phase) is not BinaryPhase
                or self.digits is not None
            ):
                raise ValueError("invalid binary phase image")
            self.phase.__post_init__()
        elif (
            type(self.digits) is not bytes
            or not self.digits
            or max(self.digits) >= self.base
            or (len(self.digits) > 1 and not self.digits[-1])
        ):
            raise ValueError("invalid packed radix image")

    @property
    def width(self) -> int:
        return (
            self.phase.width
            if self.phase is not None
            else len(cast(bytes, self.digits))
        )

    @property
    def retained_words(self) -> int:
        return (
            4 + (self.phase.k.bit_length() + 63) // 64
            if self.phase is not None
            else 4 + (len(cast(bytes, self.digits)) + 7) // 8
        )

    def digit(self, position: int) -> int:
        if not 0 <= position < self.width:
            raise IndexError(position)
        return (
            self.phase.digit(position)
            if self.phase is not None
            else cast(bytes, self.digits)[position]
        )

    def iter_digits(self) -> Iterator[int]:
        if self.phase is not None:
            yield from self.phase.iter_digits()
        else:
            yield from cast(bytes, self.digits)

    def residue(self, modulus: int) -> int:
        if type(modulus) is not int or modulus < 1:
            raise ValueError("positive modulus required")
        if self.phase is not None:
            return self.phase.residue(modulus)
        result = 0
        for d in reversed(cast(bytes, self.digits)):
            result = (result * self.base + d) % modulus
        return result


# Bytewise reflection of the bitplane, not a per-bit Python loop.
_BIT_REVERSE = bytes(int(f"{i:08b}"[::-1], 2) for i in range(256))


def _reflect(p: int, width: int) -> int:
    n = (width + 7) // 8
    return int.from_bytes(
        p.to_bytes(n, "little").translate(_BIT_REVERSE)[::-1], "little"
    ) >> (8 * n - width)


def portable_advance(
    source: bytes, base: int, steps: int
) -> tuple[bytes, tuple[int, int, int, int]]:
    """Same bitplane identities using Python bignum operations (linear limbs)."""
    width = len(source)
    n = (width + 7) // 8
    lo = bytearray(n)
    hi = bytearray(n)
    for i, d in enumerate(source):
        lo[i // 8] |= (d & 1) << (i % 8)
        hi[i // 8] |= (d >> 1) << (i % 8)
    a = int.from_bytes(lo, "little")
    a2 = int.from_bytes(hi, "little")
    words = full = births = 0
    r0 = r1 = 0
    for _ in range(steps):
        mask = (1 << width) - 1
        b = _reflect(a, width)
        if base == 2:
            e = a ^ b
            g = a & b
        else:
            b2 = _reflect(a2, width)
            a0 = mask ^ (a | a2)
            b0 = mask ^ (b | b2)
            e = (a2 & b0) | (a0 & b2) | (a & b)
            g = (a2 & b) | (a & b2) | (a2 & b2)
            r1 = (a & b0) | (a0 & b) | (a2 & b2)
            r0 = mask ^ (r1 | e)
        x = g | e
        s = x + g
        cin = (s ^ x ^ g) & mask
        if base == 2:
            a = e ^ cin
        else:
            a = (r1 & ~cin) | (r0 & cin)
            a2 = (e & ~cin) | (r1 & cin)
        words += (width + 63) // 64
        full += width // 64
        if s >> width:
            a |= 1 << width
            width += 1
            births += 1
    n = (width + 7) // 8
    final_lo = a.to_bytes(n, "little")
    final_hi = a2.to_bytes(n, "little")
    result = bytes(
        ((final_lo[i // 8] >> (i % 8)) & 1) | (((final_hi[i // 8] >> (i % 8)) & 1) << 1)
        for i in range(width)
    )
    return result, (steps, words, full, births)


def advance(
    source: Sequence[int] | SmallRadixImage,
    base: int,
    steps: int,
    ledger: ResourceLedger,
    scratch_owner: int,
    receive: Callable[[SmallRadixImage], SmallRadixImage] = lambda image: image,
) -> SmallRadixImage:
    if isinstance(source, SmallRadixImage):
        if source.base != base:
            raise ValueError("small radix source changed")
        if source.phase is not None:
            ledger.bump(keys.REVERSE_SMALL_RADIX_BINARY_POWERED_PUBLICATIONS)
            return receive(SmallRadixImage(base, source.phase.jump(steps)))
        source = cast(bytes, source.digits)
    if len(source) == 1 and source[0] == 0:
        ledger.bump(keys.REVERSE_SMALL_RADIX_ZERO_FIXED_PUBLICATIONS)
        return receive(SmallRadixImage(base, digits=b"\0"))
    if base == 2:
        phase = admit(source, steps)
        if phase is not None:
            ledger.bump(keys.REVERSE_SMALL_RADIX_BINARY_POWERED_PUBLICATIONS)
            return receive(SmallRadixImage(base, phase))
    # Fixed-size source admission for unrecognized short binary seeds. These
    # are real, charged physical updates, not a hidden clock in the phase ID.
    # Failure hands the already advanced word to the generic executor.
    if base == 2 and len(source) <= 256 and steps:
        with ledger.reservation(scratch_owner, nodes=128):
            x = 0
            for d in reversed(source):
                x = (x << 1) | d
            prefix = min(64, steps)
            words = full = births = 0
            phase = None
            for entry_step in range(1, prefix + 1):
                width = x.bit_length()
                x = x + _reflect(x, width)
                words += (width + 63) // 64
                full += width // 64
                births += x.bit_length() - width
                phase = recognize_packed(x)
                if phase is not None:
                    prefix = entry_step
                    break
            ledger.bump(keys.REVERSE_SMALL_RADIX_BINARY_ENTRY_ROWS, prefix)
            ledger.bump(keys.REVERSE_SMALL_RADIX_PHYSICAL_ROWS, prefix)
            ledger.bump(keys.REVERSE_SMALL_RADIX_PORTABLE_WORD_EQUIVALENTS, words)
            ledger.bump(keys.REVERSE_SMALL_RADIX_FULL_WORD_COLUMNS, 64 * full)
            ledger.bump(keys.REVERSE_SMALL_RADIX_BIRTHS, births)
            if phase is not None:
                ledger.bump(keys.REVERSE_SMALL_RADIX_BINARY_POWERED_PUBLICATIONS)
                return receive(SmallRadixImage(base, phase.jump(steps - prefix)))
            source = bytes((x >> i) & 1 for i in range(x.bit_length()))
            steps -= prefix
            if not steps:
                return receive(SmallRadixImage(base, digits=source))
    bound = len(source) + steps
    if (
        steps > 1_000_000
        or bound > 4_000_000
        or steps * ((bound + 63) // 64) > 200_000_000
    ):
        raise BlockContextBudgetExceeded("small radix finite word-work budget exceeded")
    # Include input bytes, two plane frontiers and output bytes. Charge before
    # any materialized allocation; the retained image has a separate memo cost.
    slots = 64 + 4 * ((bound + 7) // 8)
    with ledger.reservation(scratch_owner, nodes=slots):
        raw = bytes(source)
        native = native_kernel() if native_reverse_enabled() else None
        if native is not None:
            output, counts = native.add_small_radix(raw, base, steps)
            ledger.bump(keys.REVERSE_SMALL_RADIX_NATIVE_PUBLICATIONS)
            ledger.bump(keys.REVERSE_SMALL_RADIX_NATIVE_WORD_TILES, counts[1])
        else:
            output, counts = portable_advance(raw, base, steps)
            ledger.bump(keys.REVERSE_SMALL_RADIX_PORTABLE_PUBLICATIONS)
            ledger.bump(keys.REVERSE_SMALL_RADIX_PORTABLE_WORD_EQUIVALENTS, counts[1])
        rows, words, full, births = counts
        if (
            rows != steps
            or not 0 <= births <= steps
            or len(output) != len(raw) + births
            or not 0 <= full <= words
            or not steps * ((len(raw) + 63) // 64)
            <= words
            <= steps * ((bound + 63) // 64)
        ):
            raise RuntimeError("small radix endpoint work disagrees with its geometry")
        ledger.bump(keys.REVERSE_SMALL_RADIX_PHYSICAL_ROWS, rows)
        ledger.bump(keys.REVERSE_SMALL_RADIX_FULL_WORD_COLUMNS, 64 * full)
        ledger.bump(keys.REVERSE_SMALL_RADIX_BIRTHS, births)
        return receive(SmallRadixImage(base, digits=output))
