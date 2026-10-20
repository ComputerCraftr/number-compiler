"""Exact cyclic positional phase counts for source-owned binary tripling.

The *positional weight* 2**j (not the exponent m in 3**m) factors through
j modulo 2*w when F=2**w+1.  A block's source/output bit counts and carry
ingress counts therefore live in Z[C_(2*w)].  These counts preserve the
complete signed fold at z=2 and can be CONCAT/REPEAT-powered across a
**source-authenticated spatial word** without enumerating its repetitions.

A cyclotomic temporal period at a *fixed* inward position does not certify
that an unknown spatial middle is a repeated word.  Unknown positions retain
symbolic phase counts with exact capacities; they are NEVER replaced by zero.
No Fermat-candidate modular squaring is performed in this module.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.morphism_core import binary_power


def _validate_fold_width(fold_width: int) -> int:
    if (
        type(fold_width) is not int
        or fold_width < 2
        or fold_width & (fold_width - 1)
        or fold_width > 8192
    ):
        raise ValueError("fold width must be a power of 2 in [2,8192]")
    return 2 * fold_width


def phase_weights(fold_width: int) -> tuple[int, ...]:
    """Signed integer representatives of binary powers, one per C_(2w) phase."""
    period = _validate_fold_width(fold_width)
    return tuple(
        (1 << r) if r < fold_width else -(1 << (r - fold_width)) for r in range(period)
    )


def signed_phase_fold(counts: tuple[int, ...], fold_width: int) -> int:
    """The exact homomorphism Z[C_(2w)] -> Z/(2**w+1), z -> 2."""
    period = _validate_fold_width(fold_width)
    if len(counts) != period or any(type(c) is not int for c in counts):
        raise ValueError("invalid cyclic phase counts")
    modulus = (1 << fold_width) + 1
    result = 0
    for coefficient in reversed(counts):
        result = (2 * result + coefficient) % modulus
    return result


def phase_rotate(counts: tuple[int, ...], shift: int) -> tuple[int, ...]:
    """Shift relative bit positions into the common absolute C_(2w) phase."""
    p = len(counts)
    if type(shift) is not int or p == 0:
        raise ValueError("invalid phase rotation")
    delta = shift % p
    return tuple(counts[(r - delta) % p] for r in range(p))


def phase_add(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    if len(a) != len(b):
        raise ValueError("incompatible phase histograms")
    return tuple(x + y for x, y in zip(a, b, strict=True))


def phase_capacity(start: int, width: int, fold_width: int) -> tuple[int, ...]:
    """Exact number of potential bit sites in each phase in [start,start+width)."""
    p = _validate_fold_width(fold_width)
    if (
        type(start) is not int
        or start < 0
        or start.bit_length() > 4096
        or type(width) is not int
        or width < 0
        or width.bit_length() > 4096
    ):
        raise ValueError("invalid interval")
    first = start % p
    return tuple(
        0 if (d := (r - first) % p) >= width else 1 + (width - 1 - d) // p
        for r in range(p)
    )


@dataclass(frozen=True, slots=True)
class BinaryPhaseCarryAction:
    """Exact spatial carry action for one known binary source block.

    Input carry ranges over 0/1/2.  Source counts do not depend on the
    input carry; output digits and internal carry counts are conditional.
    All masks use LOCAL bit positions and compose using cyclic phase shifts.
    """

    width: int
    fold_width: int
    source_counts: tuple[int, ...]
    output_counts: tuple[tuple[int, ...], ...]
    ingress_counts: tuple[tuple[int, ...], ...]
    carry_out: tuple[int, int, int]

    @classmethod
    def identity(cls, fold_width: int) -> BinaryPhaseCarryAction:
        p = _validate_fold_width(fold_width)
        z = (0,) * p
        return cls(0, fold_width, z, (z, z, z), (z, z, z), (0, 1, 2))

    @classmethod
    def from_word(
        cls, source: int, width: int, fold_width: int
    ) -> BinaryPhaseCarryAction:
        p = _validate_fold_width(fold_width)
        if (
            type(source) is not int
            or source < 0
            or type(width) is not int
            or not 0 <= width <= 65536
            or source.bit_length() > width
        ):
            raise ValueError("source word does not fit its certified width")
        data = source.to_bytes((width + 7) // 8, "little")
        dcounts = [0] * p
        output: list[list[int]] = [[0] * p for _ in range(3)]
        carries: list[list[int]] = [[0] * p for _ in range(3)]
        end: list[int] = []
        for i in range(width):
            dcounts[i % p] += (data[i // 8] >> (i % 8)) & 1
        for cin in (0, 1, 2):
            c = cin
            for i in range(width):
                k = i % p
                d = (data[i // 8] >> (i % 8)) & 1
                carries[cin][k] += c
                u = 3 * d + c
                output[cin][k] += u & 1
                c = u >> 1
            end.append(c)
        result = cls(
            width,
            fold_width,
            tuple(dcounts),
            tuple(tuple(x) for x in output),
            tuple(tuple(x) for x in carries),
            (end[0], end[1], end[2]),
        )
        result.verify()
        return result

    def verify(self) -> None:
        p = _validate_fold_width(self.fold_width)
        if (
            type(self.width) is not int
            or self.width < 0
            or self.width.bit_length() > 4096
            or len(self.source_counts) != p
            or len(self.output_counts) != 3
            or len(self.ingress_counts) != 3
            or len(self.carry_out) != 3
        ):
            raise ArithmeticError("malformed phase action")
        if self.width == 0 and self.carry_out != (0, 1, 2):
            raise ArithmeticError("empty carry action is not identity")
        capacity = phase_capacity(0, self.width, self.fold_width)
        if any(
            type(v) is not int or v < 0 or v > capacity[r]
            for r, v in enumerate(self.source_counts)
        ):
            raise ArithmeticError("source histogram violates interval capacity")
        modulus = (1 << self.fold_width) + 1
        source_fold = signed_phase_fold(self.source_counts, self.fold_width)
        outgoing_weight = pow(2, self.width % (2 * self.fold_width), modulus)
        for cin in (0, 1, 2):
            cout = self.carry_out[cin]
            e = self.output_counts[cin]
            k = self.ingress_counts[cin]
            if (
                type(cout) is not int
                or cout not in (0, 1, 2)
                or len(e) != p
                or len(k) != p
                or any(
                    type(e[r]) is not int or e[r] < 0 or e[r] > capacity[r]
                    for r in range(p)
                )
                or any(
                    type(k[r]) is not int or k[r] < 0 or k[r] > 2 * capacity[r]
                    for r in range(p)
                )
            ):
                raise ArithmeticError("carry/digit histogram violates bounds")
            for r in range(p):
                # K records carry entering each local digit, including cin.
                # Rotating K to outgoing ports introduces two true seams.
                predicted = (
                    3 * self.source_counts[r]
                    + k[r]
                    - 2 * k[(r + 1) % p]
                    + 2 * cin * (r == p - 1)
                    - 2 * cout * (r == (self.width - 1) % p)
                )
                if self.width == 0:
                    # No bits: the action is identity and has no seam ports.
                    predicted = 0
                if predicted != e[r]:
                    raise ArithmeticError("cyclic carry identity violated")
            signed_lhs = signed_phase_fold(e, self.fold_width)
            signed_rhs = (3 * source_fold + cin - outgoing_weight * cout) % modulus
            if signed_lhs != signed_rhs:
                raise ArithmeticError("signed Fermat projection violated")

    def then(self, upper: BinaryPhaseCarryAction) -> BinaryPhaseCarryAction:
        self.verify()
        upper.verify()
        if self.fold_width != upper.fold_width:
            raise ValueError("cannot concatenate different fold widths")
        src = phase_add(
            self.source_counts, phase_rotate(upper.source_counts, self.width)
        )
        out: list[tuple[int, ...]] = []
        car: list[tuple[int, ...]] = []
        end: list[int] = []
        for ci in (0, 1, 2):
            c_mid = self.carry_out[ci]
            out.append(
                phase_add(
                    self.output_counts[ci],
                    phase_rotate(upper.output_counts[c_mid], self.width),
                )
            )
            car.append(
                phase_add(
                    self.ingress_counts[ci],
                    phase_rotate(upper.ingress_counts[c_mid], self.width),
                )
            )
            end.append(upper.carry_out[c_mid])
        result = BinaryPhaseCarryAction(
            self.width + upper.width,
            self.fold_width,
            src,
            tuple(out),
            tuple(car),
            (end[0], end[1], end[2]),
        )
        result.verify()
        return result

    def power(self, repetitions: int) -> BinaryPhaseCarryAction:
        """Exact REPEAT if and only if the spatial source word is certified."""
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("invalid repeated block count")
        self.verify()
        if (
            repetitions.bit_length() > 4096
            or 2 * repetitions.bit_length() * (2 * self.fold_width) > 2_000_000
        ):
            raise ValueError("phase power exceeds composition budget")
        return binary_power(
            self,
            repetitions,
            identity=self.identity(self.fold_width),
            compose=BinaryPhaseCarryAction.then,
        ).value


@dataclass(frozen=True, slots=True)
class SymbolicPhaseInterval:
    """Unknown source bit phase counts: bounded, NEVER assumed to be zero."""

    start: int
    width: int
    fold_width: int
    source_capacity: tuple[int, ...]

    @classmethod
    def from_interval(
        cls, start: int, width: int, fold_width: int
    ) -> SymbolicPhaseInterval:
        if type(width) is not int or width <= 0:
            raise ValueError("symbolic interval must be nonempty")
        return cls(start, width, fold_width, phase_capacity(start, width, fold_width))

    @property
    def possible_carry_capacity(self) -> tuple[int, ...]:
        """Safe (not independently certified) physical-carry upper bounds."""
        return tuple(2 * n for n in self.source_capacity)

    @property
    def total_unknown_sites(self) -> int:
        return sum(self.source_capacity)

    @property
    def coefficients(self) -> tuple[int, ...]:
        return phase_weights(self.fold_width)
