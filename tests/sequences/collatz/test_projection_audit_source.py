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
from tests.support.radix_projection import radix_projections


def test_projection_audit_source_preserves_original_authority() -> None:
    term = PoweredCollatzTerm(27, 16)
    before = dict(term.resource_ledger.counters)
    source = term.radix_projection_audit_source(term.resource_ledger)
    assert source is not None
    assert source.owner is term
    assert source.source is term.original_source_construction.source
    assert source.projections is radix_projections(term)
    assert source.steps == term.steps
    assert source.seed_digits is term.seed_digits
    assert term.resource_ledger.counters == before
    assert term.radix_projection_audit_source(ResourceLedger()) is None


def test_projection_audit_source_rejects_a_derived_owner() -> None:
    class DerivedTerm(PoweredCollatzTerm):
        pass

    term = DerivedTerm(27, 16)
    assert term.radix_projection_audit_source(term.resource_ledger) is None


@pytest.mark.parametrize("defect", ["copied-owner", "digits", "boolean-steps"])
def test_projection_audit_source_rejects_forged_metadata(defect: str) -> None:
    term = PoweredCollatzTerm(27, 16)
    source = term.radix_projection_audit_source(term.resource_ledger)
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
        checked_projection_audit_source(Lookalike(), term.resource_ledger)
