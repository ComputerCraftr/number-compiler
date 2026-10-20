"""Compiler-issued arithmetic identity; operator shape is never a certificate."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Final, Literal

from number_compiler.arithmetic.contracts.block_effect import BlockEffect, _effect_key
from number_compiler.arithmetic.contracts.input_validation import is_runtime_instance
from number_compiler.resources.metric_keys import (
    arithmetic_contracts as _contracts_keys,
)

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger


Family = Literal["reverse-add", "collatz"]
OutputEncoding = Literal["digits", "pair", "binary"]
CERTIFIED_TEMPORAL_ACTION_TAG: Final[str] = "certified-temporal-v3"
_ISSUER = object()


@dataclass(frozen=True, slots=True)
class _IssuedClaims:
    """Immutable issuance evidence carried by a certificate, not a registry."""

    origin: object
    family: Family
    base: int
    steps: int
    source_encoding: str
    output_encoding: OutputEncoding
    operator_identity: object


@dataclass(frozen=True, slots=True)
class TemporalFamilyCertificate:
    family: Family
    base: int
    steps: int
    source_encoding: str
    output_encoding: OutputEncoding
    operator_identity: object
    _issuer: object = field(repr=False, compare=False)

    def _validate_issuance(self) -> None:
        issued = self._issuer
        if type(issued) is not _IssuedClaims or issued.origin is not _ISSUER:
            raise ValueError("family certificate was not issued by the compiler")
        if (
            type(self.base) is not int
            or type(self.steps) is not int
            or (
                self.family,
                self.base,
                self.steps,
                self.source_encoding,
                self.output_encoding,
                self.operator_identity,
            )
            != (
                issued.family,
                issued.base,
                issued.steps,
                issued.source_encoding,
                issued.output_encoding,
                issued.operator_identity,
            )
        ):
            raise ValueError("family certificate claims differ from compiler issuance")

    def validate(self, effect: BlockEffect) -> None:
        self._validate_issuance()
        if self.base != effect.base or self.operator_identity != _effect_key(effect):
            raise ValueError("family certificate does not belong to this operator")
        if (
            self.family not in ("reverse-add", "collatz")
            or self.steps != effect.exponent
        ):
            raise ValueError("family certificate exponent or family mismatch")
        if self.steps < 0:
            raise ValueError("negative certified step count")
        expected = "symmetric-pair" if self.family == "reverse-add" else "binary"
        if self.source_encoding != expected:
            raise ValueError("family certificate has the wrong source encoding")
        expected_output = "digits" if self.family == "reverse-add" else "binary"
        if self.output_encoding not in (expected_output, "pair"):
            raise ValueError("family certificate has the wrong output encoding")

    @property
    def temporal_key(self) -> tuple[str, str, int, int, str, str]:
        self._validate_issuance()
        return (
            CERTIFIED_TEMPORAL_ACTION_TAG,
            self.family,
            self.base,
            self.steps,
            self.source_encoding,
            self.output_encoding,
        )


def _verify_program(
    effect: BlockEffect,
    family: Family,
    ledger: ResourceLedger | None,
    output_encoding: OutputEncoding,
    family_leaf_counts: Callable[[BlockEffect], tuple[int, int] | None] | None,
) -> None:
    """Check actual immutable kernel syntax, never just its claimed exponent."""
    from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
    from number_compiler.hashlife.actions.lazy_compiler import ProgramComposition
    from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect

    facts: dict[int, tuple[int, int]] = {}
    active: set[int] = set()
    pending: list[tuple[BlockEffect, bool]] = [(effect, False)]
    while pending:
        node, ready = pending.pop()
        identity = id(node)
        if identity in facts:
            continue
        if node.base != effect.base or node.blank != effect.blank:
            raise ValueError("arithmetic program contains mixed alphabets")
        if ledger is not None:
            ledger.bump(_contracts_keys.CERTIFICATE_DAG_VISITS)
            peak = ledger.counters.get(_contracts_keys.CERTIFICATE_WORKSPACE_PEAK, 0)
            size = len(pending) + len(facts) + len(active)
            if size > peak:
                ledger.bump(
                    _contracts_keys.CERTIFICATE_WORKSPACE_PEAK,
                    size - peak,
                )
        if type(node) is ProgramComposition and is_runtime_instance(
            node, ProgramComposition
        ):
            if not ready:
                if identity in active:
                    raise ValueError("cyclic arithmetic program")
                active.add(identity)
                pending.extend(
                    ((node, True), (node.second, False), (node.first, False))
                )
                continue
            first, second = facts[id(node.first)], facts[id(node.second)]
            if first[1] and second[0]:
                raise ValueError("normalization must follow all reverse stages")
            counts = first[0] + second[0], first[1] + second[1]
            active.remove(identity)
        elif family == "reverse-add" and type(node) is BaseBlockEffect:
            counts = 1, 0
        elif family == "reverse-add" and type(node) is DigitNormalizeBlockEffect:
            counts = 0, 1
        else:
            family_counts = (
                family_leaf_counts(node)
                if family == "collatz" and family_leaf_counts is not None
                else None
            )
            if family_counts is None:
                raise ValueError(
                    "operator has no certified arithmetic-family implementation"
                )
            if (
                type(family_counts) is not tuple
                or len(family_counts) != 2
                or any(type(value) is not int or value < 0 for value in family_counts)
            ):
                raise TypeError("family certificate leaf returned invalid counts")
            counts = family_counts
        if counts[0] != node.exponent or counts[1] > 1:
            raise ValueError("arithmetic program does not match its declared semantics")
        facts[identity] = counts
    expected_terminals = int(family == "reverse-add" and output_encoding == "digits")
    if facts[id(effect)][1] != expected_terminals:
        raise ValueError("reverse digit projection requires one terminal normalization")


def issue_certificate(
    effect: BlockEffect,
    family: Family,
    steps: int,
    *,
    ledger: ResourceLedger | None = None,
    output_encoding: OutputEncoding | None = None,
    family_leaf_counts: Callable[[BlockEffect], tuple[int, int] | None] | None = None,
) -> TemporalFamilyCertificate:
    """Issue only after checking the executable DAG's arithmetic language."""
    if (
        family not in ("reverse-add", "collatz")
        or steps < 0
        or effect.exponent != steps
    ):
        raise ValueError("invalid arithmetic family or exponent")
    output = (
        ("digits" if family == "reverse-add" else "binary")
        if output_encoding is None
        else output_encoding
    )
    if output not in ("digits", "pair", "binary") or (
        family == "collatz" and output != "binary"
    ):
        raise ValueError("invalid arithmetic output encoding")
    _verify_program(effect, family, ledger, output, family_leaf_counts)
    encoding = "symmetric-pair" if family == "reverse-add" else "binary"
    identity = _effect_key(effect)
    return TemporalFamilyCertificate(
        family,
        effect.base,
        steps,
        encoding,
        output,
        identity,
        _IssuedClaims(
            _ISSUER,
            family,
            effect.base,
            steps,
            encoding,
            output,
            identity,
        ),
    )
