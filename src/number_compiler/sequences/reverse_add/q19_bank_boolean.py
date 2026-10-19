"""Exact coupled five-band/Boolean ports for a certified periodic Q19 action.

These are *outputs* of an already source-guarded action, not authority for an
unobserved growth word, a complete-root temporal return, or a signed whole-
integer innovation.  Every port uses the same source, carry and target frame.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.decimal_pair_partition import (
    decimal_pair_word_projection,
)

if TYPE_CHECKING:
    from .mixed_periodic_bank import MixedFrame


def _bands(word: tuple[int, ...]) -> Mapping[str, tuple[int, ...]]:
    return MappingProxyType(decimal_pair_word_projection(word).wire_channels())


@dataclass(frozen=True, slots=True)
class CoupledBooleanBankFrame:
    """A complete synchronized Boolean/F5/port projection of one bank tick.

    ``borrow_transfer_if_next_quiet[i]`` describes the *following nongrowth* innovation
    borrow (output for ingress 0 and 1). A subsequent growth comparison
    requires a different, shifted-width signed subtraction certificate.
    """

    source: tuple[int, ...]
    target: tuple[int, ...]
    growth: int
    source_bands: Mapping[str, tuple[int, ...]]
    target_bands: Mapping[str, tuple[int, ...]]
    carries: tuple[tuple[int, int], ...]
    reflected_xor: tuple[int, ...]
    reflected_and: tuple[int, ...]
    pascal_parity: tuple[int, ...]
    shifted_growth_xor: tuple[int, ...] | None
    gt_high_birth: tuple[int, ...]
    eq_birth: tuple[int, ...]
    borrow_transfer_if_next_quiet: tuple[tuple[int, int], ...]
    gt_high_from_lt_high: tuple[int, ...] | None
    gt_high_from_eq: tuple[int, ...] | None

    @classmethod
    def from_frame(
        cls, source: tuple[int, ...], frame: MixedFrame
    ) -> CoupledBooleanBankFrame:
        from .mixed_periodic_bank import MixedPeriodicCore

        if type(source) is not tuple or len(source) != len(frame.target):
            raise ValueError("Boolean source and target periods differ")
        current = MixedPeriodicCore(source)
        if type(frame.growth) is not int or frame.growth not in (0, 1):
            raise ValueError("bank frame has an invalid growth port")
        _, exact_frame = current.advance(frame.growth)
        if exact_frame != frame:
            raise ValueError("bank frame is not the exact source-period transition")
        if any(not 0 <= value <= 18 for value in frame.target):
            raise ValueError("invalid target symmetric coefficient")
        if any(
            a + b != value
            for a, b, value in zip(
                frame.digits_low, frame.digits_reflected, frame.target, strict=True
            )
        ):
            raise ValueError("bank digits disagree with the pair output")
        source_bands = _bands(source)
        later = _bands(frame.target)
        xor = tuple(a ^ b for a, b in frame.incoming)
        both = tuple(a & b for a, b in frame.incoming)
        if frame.growth == 0:
            shifted_xor = None
            pascal_parity = xor
            # This is the exact GT-high innovation birth logic, not a fit to
            # sampled words. The EQ case must keep *both* reflected ports.
            gt = tuple(
                int(
                    s in (8, 18)
                    or (s in (7, 17) and (a or b))
                    or (s == 9 and not a and not b)
                )
                for s, (a, b) in zip(source, frame.incoming, strict=True)
            )
            eq = tuple(
                int(s % 5 == 4 and (a ^ b))
                for s, (a, b) in zip(source, frame.incoming, strict=True)
            )
            if gt != later["gt_high"] or eq != later["eq"]:
                raise AssertionError("nongrowth five-band Boolean lift disagrees")
        else:
            # Growth has a shifted reflected source at (i-1) and a genuine
            # reflected carry K_(s_i)(b). Do not use the unshifted EQ-XOR rule.
            shifted_xor_bits = []
            parity_bits = []
            for i, (a, b) in enumerate(frame.incoming):
                s = source[i]
                prior_symbol = source[(i - 1) % len(source)]
                reflected_out = int(s > 9 or (s == 9 and b == 1))
                low_out = int(s > 9 or (s == 9 and a == 1))
                high_out = int(
                    prior_symbol > 9 or (prior_symbol == 9 and reflected_out == 1)
                )
                candidate = (
                    s + prior_symbol + a + reflected_out - 10 * (low_out + high_out)
                )
                parity = (s ^ prior_symbol ^ a ^ reflected_out) & 1
                f5 = (s + prior_symbol + a + reflected_out) % 5
                if (candidate, parity, f5) != (
                    frame.target[i],
                    frame.target[i] % 2,
                    frame.target[i] % 5,
                ):
                    raise AssertionError("growth Boolean/Pascal lift disagrees")
                shifted_xor_bits.append(a ^ reflected_out)
                parity_bits.append(parity)
            shifted_xor = tuple(shifted_xor_bits)
            pascal_parity = tuple(parity_bits)
            gt = later["gt_high"]
            eq = later["eq"]
        if pascal_parity != tuple(value % 2 for value in frame.target):
            raise AssertionError("Pascal parity port disagrees with target F2")
        transfers = []
        future_ports = MixedPeriodicCore(frame.target).ingresses()
        for value, flag, (_left, eta) in zip(
            frame.target,
            frame.borrow_identity_if_next_quiet,
            future_ports,
            strict=True,
        ):
            # The forced outgoing borrow is rho=K_(s_i)(eta), NOT eta.
            # A resetting LT/GT coefficient can override its external ingress.
            rho = int(value > 9 or (value == 9 and eta == 1))
            transfers.append((0, 1) if flag else (rho, rho))
        return cls(
            source=source,
            target=frame.target,
            growth=frame.growth,
            source_bands=source_bands,
            target_bands=later,
            carries=frame.incoming,
            reflected_xor=xor,
            reflected_and=both,
            pascal_parity=pascal_parity,
            shifted_growth_xor=shifted_xor,
            gt_high_birth=gt,
            eq_birth=eq,
            borrow_transfer_if_next_quiet=tuple(transfers),
            gt_high_from_lt_high=(
                tuple(a & b for a, b in zip(source_bands["lt_high"], gt, strict=True))
                if frame.growth == 0
                else None
            ),
            gt_high_from_eq=(
                tuple(a & b for a, b in zip(source_bands["eq"], gt, strict=True))
                if frame.growth == 0
                else None
            ),
        )


__all__ = ["CoupledBooleanBankFrame"]
