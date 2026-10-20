"""A copied certificate cannot relabel the compiler's authorized semantics."""

from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.temporal_family import issue_certificate
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.bounded_application import (
    build_bounded_application,
)
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from tests.support.dataclass_records import replace_record


@pytest.mark.parametrize(
    "changed",
    (
        {"family": "collatz", "source_encoding": "binary"},
        {"base": 3},
        {"steps": 2},
        {"steps": True},
        {"source_encoding": "binary"},
        {"operator_identity": ("forged",)},
        {"_issuer": object()},
    ),
)
def test_changed_certificate_claims_reject_before_dispatch_or_temporal_key(
    changed: dict[str, object],
) -> None:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    effect = compiler.compose(BaseBlockEffect(2), DigitNormalizeBlockEffect(2))
    original = issue_certificate(effect, "reverse-add", 1)
    copied = replace_record(original, changed)
    before = ledger.snapshot()
    with pytest.raises(ValueError, match="certificate"):
        copied.validate(effect)
    with pytest.raises(ValueError, match="certificate"):
        _ = copied.temporal_key
    with pytest.raises(ValueError, match="certificate"):
        build_bounded_application(
            effect,
            (2, 2),
            logical_length=4,
            certificate=copied,
            ledger=ledger,
            compiler=compiler,
        )
    with pytest.raises(ValueError, match="certificate"):
        HashLifeBlockIndex(
            effect,
            (2, 2),
            logical_length=4,
            certificate=copied,
            ledger=ledger,
            compiler=compiler,
        )
    assert ledger.snapshot() == before


def test_unchanged_certificate_copy_keeps_its_immutable_issuance() -> None:
    compiler = LazyCompiler(ResourceLedger())
    effect = compiler.compose(BaseBlockEffect(2), DigitNormalizeBlockEffect(2))
    certificate = issue_certificate(effect, "reverse-add", 1)
    copied = replace(certificate)
    copied.validate(effect)
    assert copied.temporal_key == certificate.temporal_key
    assert object.__getattribute__(copied, "_issuer") is object.__getattribute__(
        certificate, "_issuer"
    )
