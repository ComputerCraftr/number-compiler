"""Exact proof-language programs for special-number source support experiments.

The Fermat/Mersenne temporal quotient is already binary-powerable.  The missing
release theorem is the *source injection*: construct one candidate-ring defect
whose local value is zero on every passing Frobenius/Kummer component and a
unit on every failing component.

This module defines the production-safe arithmetic language used to state such
a constructor.  The language is intentionally small and honestly charged.  It
contains no deferred exponent token, factor/CRT input, carrier enumeration,
Pépin/Lucas--Lehmer oracle, polynomial materializer, or recurrence replay.

A :class:`FoldedSupportProgram` by itself is **not** a primality certificate.
It only computes a candidate-derived ring element.  A separate theorem witness
must prove that the program computes the folded-support defect before production
may consume it as a :class:`SpecialFrobeniusDefectPacket`.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd

from number_compiler.sequences.power_numbers.frobenius_chunk import (
    SpecialFrobeniusChunkSpec,
)
from number_compiler.sequences.power_numbers.numbers import (
    fermat_factor_stride,
    fermat_number,
    mersenne_factor_stride,
    mersenne_number,
)

_ATOMS = frozenset(
    {
        "zero",
        "one",
        "neg_one",
        "parameter",
        "start_level",
        "span",
        "baseline_v2",
        "base_stride_v2",
        "required_v2",
        "modulus_bits",
        "trace_seed",
        "factor_stride",
        "base_stride",
        "required_stride",
        "folded_half_degree",
        "sparse_root",
    }
)
_UNARY = frozenset({"neg", "square", "gcd_n"})
_BINARY = frozenset({"add", "sub", "mul"})


def _special_modulus(spec: SpecialFrobeniusChunkSpec) -> int:
    if spec.family == "fermat":
        return fermat_number(spec.parameter)
    return mersenne_number(spec.parameter)


def _atom_value(name: str, spec: SpecialFrobeniusChunkSpec, modulus: int) -> int:
    if name == "zero":
        return 0
    if name == "one":
        return 1
    if name == "neg_one":
        return modulus - 1
    if name == "parameter":
        return spec.parameter % modulus
    if name == "start_level":
        return spec.start_level % modulus
    if name == "span":
        return spec.span % modulus
    if name == "baseline_v2":
        return spec.baseline_local_v2 % modulus
    if name == "base_stride_v2":
        return spec.base_stride_v2 % modulus
    if name == "required_v2":
        return spec.required_local_v2 % modulus
    if name == "modulus_bits":
        return spec.modulus_bits % modulus
    if name == "trace_seed":
        return 5 if spec.family == "fermat" else 4
    if name == "factor_stride":
        stride = (
            fermat_factor_stride(spec.parameter)
            if spec.family == "fermat"
            else mersenne_factor_stride(spec.parameter)
        )
        return stride % modulus
    if name == "base_stride":
        return pow(2, spec.base_stride_v2, modulus)
    if name == "required_stride":
        return pow(2, spec.required_local_v2, modulus)
    if name == "folded_half_degree":
        return pow(2, spec.folded_half_degree_log2, modulus)
    if name == "sparse_root":
        exponent = (
            1 << (spec.parameter - 1)
            if spec.family == "fermat"
            else (spec.parameter - 1) // 2
        )
        return pow(2, exponent, modulus)
    raise ValueError(name)


@dataclass(frozen=True, slots=True)
class FoldedSupportInstruction:
    """One canonical arithmetic SLP instruction.

    ``atom`` stores its atom name in ``arg0``.  Unary and binary operations
    reference only prior instruction indices; this makes the program a DAG in
    topological order and prevents recursive/deferred work from hiding behind a
    node.
    """

    op: str
    arg0: int | str
    arg1: int | None = None

    def __post_init__(self) -> None:
        if self.op == "atom":
            if not isinstance(self.arg0, str) or self.arg0 not in _ATOMS:
                raise ValueError((self.op, self.arg0))
            if self.arg1 is not None:
                raise ValueError(self.arg1)
            return
        if self.op in _UNARY:
            if not isinstance(self.arg0, int) or self.arg0 < 0 or self.arg1 is not None:
                raise ValueError((self.op, self.arg0, self.arg1))
            return
        if self.op in _BINARY:
            if not isinstance(self.arg0, int) or not isinstance(self.arg1, int):
                raise ValueError((self.op, self.arg0, self.arg1))
            if self.arg0 < 0 or self.arg1 < 0:
                raise ValueError((self.arg0, self.arg1))
            return
        raise ValueError(self.op)


@dataclass(frozen=True, slots=True)
class FoldedSupportEvaluation:
    value: int
    support_gcd: int
    ring_additions: int
    ring_multiplications: int
    gcd_operations: int
    source_atoms: int
    instructions: int

    @property
    def charged_operations(self) -> int:
        return self.ring_additions + self.ring_multiplications + self.gcd_operations


@dataclass(frozen=True, slots=True)
class FoldedSupportProgram:
    """A fully explicit candidate-ring straight-line program.

    The output is the final instruction.  There is deliberately no generic
    ``pow``/``repeat``/``binomial``/``factorial`` instruction: if a theorem
    needs such an operation it must first expose a separately proved compact
    evaluator whose actual work is charged.
    """

    instructions: tuple[FoldedSupportInstruction, ...]

    def __post_init__(self) -> None:
        if not self.instructions:
            raise ValueError("empty folded-support program")
        for index, ins in enumerate(self.instructions):
            refs: tuple[int, ...]
            if ins.op == "atom":
                refs = ()
            elif ins.op in _UNARY:
                refs = (int(ins.arg0),)
            else:
                if ins.arg1 is None:
                    raise AssertionError(ins)
                refs = (int(ins.arg0), int(ins.arg1))
            if any(ref >= index for ref in refs):
                raise ValueError((index, ins, refs))

    @property
    def node_count(self) -> int:
        return len(self.instructions)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "folded-support-program-v1",
            tuple((ins.op, ins.arg0, ins.arg1) for ins in self.instructions),
        )

    @property
    def description_bits(self) -> int:
        ref_bits = max(1, (len(self.instructions) - 1).bit_length())
        total = 0
        for ins in self.instructions:
            total += 3
            if ins.op == "atom":
                total += len(str(ins.arg0).encode("utf-8")) * 8
            elif ins.op in _UNARY:
                total += ref_bits
            else:
                total += 2 * ref_bits
        return total

    def evaluate(self, spec: SpecialFrobeniusChunkSpec) -> FoldedSupportEvaluation:
        modulus = _special_modulus(spec)
        values: list[int] = []
        adds = muls = gcds = atoms = 0
        for index, ins in enumerate(self.instructions):
            if ins.op == "atom":
                value = _atom_value(str(ins.arg0), spec, modulus)
                atoms += 1
            elif ins.op == "neg":
                value = -values[int(ins.arg0)]
                adds += 1
            elif ins.op == "square":
                value = values[int(ins.arg0)] * values[int(ins.arg0)]
                muls += 1
            elif ins.op == "gcd_n":
                value = gcd(values[int(ins.arg0)], modulus)
                gcds += 1
            elif ins.op == "add":
                if ins.arg1 is None:
                    raise AssertionError(ins)
                value = values[int(ins.arg0)] + values[int(ins.arg1)]
                adds += 1
            elif ins.op == "sub":
                if ins.arg1 is None:
                    raise AssertionError(ins)
                value = values[int(ins.arg0)] - values[int(ins.arg1)]
                adds += 1
            elif ins.op == "mul":
                if ins.arg1 is None:
                    raise AssertionError(ins)
                value = values[int(ins.arg0)] * values[int(ins.arg1)]
                muls += 1
            else:  # pragma: no cover - constructor invariant
                raise AssertionError(ins.op)
            values.append(value % modulus)
            if len(values) != index + 1:  # pragma: no cover
                raise AssertionError(index)
        out = values[-1]
        return FoldedSupportEvaluation(
            out,
            gcd(out, modulus),
            adds,
            muls,
            gcds,
            atoms,
            len(values),
        )

    @classmethod
    def atom(cls, name: str) -> FoldedSupportProgram:
        return cls((FoldedSupportInstruction("atom", str(name)),))


@dataclass(frozen=True, slots=True)
class SpecialSourceCertificateCandidate:
    """Untrusted candidate certificate produced by research/synthesis.

    ``theorem_proved`` is intentionally not caller-settable: production has no
    constructor that promotes this type to a terminal PASS.  The object exists
    so research can carry the exact proposed program, output and cost without
    conflating empirical agreement with a theorem.
    """

    spec: SpecialFrobeniusChunkSpec
    program: FoldedSupportProgram
    defect: int
    support_gcd: int
    method: str
    theorem_proved: bool = False

    @classmethod
    def evaluate(
        cls,
        spec: SpecialFrobeniusChunkSpec,
        program: FoldedSupportProgram,
        *,
        method: str = "unproved-folded-support-program",
    ) -> SpecialSourceCertificateCandidate:
        evaluation = program.evaluate(spec)
        return cls(
            spec,
            program,
            evaluation.value,
            evaluation.support_gcd,
            str(method),
            False,
        )

    @property
    def semantic_source_code(self) -> int | None:
        """Prime-conditional target-distance code, never a stored assertion."""
        modulus = _special_modulus(self.spec)
        if self.support_gcd != modulus:
            return None
        horizon = (
            (1 << self.spec.parameter) - 2
            if self.spec.family == "fermat"
            else self.spec.parameter - 2
        )
        return horizon + 1


__all__ = [
    "FoldedSupportEvaluation",
    "FoldedSupportInstruction",
    "FoldedSupportProgram",
    "SpecialSourceCertificateCandidate",
]
