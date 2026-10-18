"""Shared live 196-generation-79 border source for carry regressions."""

from __future__ import annotations

from collections.abc import Iterator
from contextlib import contextmanager

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.q19_border_control import (
    CertifiedBorderGrowth,
)
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)

from .reverse_add_source_data import iterate_reverse_add


@contextmanager
def source_196_generation_79_border() -> Iterator[
    tuple[int, ResourceLedger, ReversePairQ19OutputOwner, CertifiedBorderGrowth]
]:
    """Issue the canonical 9-step, three-pair border certificate once."""
    value = iterate_reverse_add(196, 79)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(value, 10), base=10)
    try:
        certificate = owner.certify_border_growth(
            owner.initial, steps=9, window_digits=3
        )
        yield value, ledger, owner, certificate
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


__all__ = ["source_196_generation_79_border"]
