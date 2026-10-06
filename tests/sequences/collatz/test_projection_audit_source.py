"""Radix audit metadata remains bound to its exact family source owner."""

from dataclasses import replace

import pytest

from number_compiler.projection.source_audit import (
    RadixProjectionAuditSource,
    RadixProjectionSourceAuditor,
    checked_projection_audit_source,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


def test_projection_audit_source_preserves_original_authority() -> None:
    term = PoweredCollatzTerm(27, 16)
    before = dict(term._ledger.counters)
    source = term.radix_projection_audit_source(term._ledger)
    assert source is not None
    assert source.owner is term
    assert source.source is term._source_construction.source
    assert source.projections is term._radix_projections
    assert source.steps == term.steps
    assert source.seed_digits is term.seed_digits
    assert term._ledger.counters == before
    assert term.radix_projection_audit_source(ResourceLedger()) is None


def test_projection_audit_source_rejects_a_derived_owner() -> None:
    class DerivedTerm(PoweredCollatzTerm):
        pass

    term = DerivedTerm(27, 16)
    assert term.radix_projection_audit_source(term._ledger) is None


@pytest.mark.parametrize("defect", ["copied-owner", "digits", "boolean-steps"])
def test_projection_audit_source_rejects_forged_metadata(defect: str) -> None:
    term = PoweredCollatzTerm(27, 16)
    source = term.radix_projection_audit_source(term._ledger)
    assert source is not None

    class Lookalike(RadixProjectionSourceAuditor):
        def radix_projection_audit_source(
            self, ledger: ResourceLedger
        ) -> RadixProjectionAuditSource:
            assert source is not None
            if defect == "copied-owner":
                return source
            if defect == "digits":
                return replace(source, owner=self, seed_digits=(0,))
            return replace(source, owner=self, steps=True)

    with pytest.raises(ValueError, match="bound to its owner"):
        checked_projection_audit_source(Lookalike(), term._ledger)
