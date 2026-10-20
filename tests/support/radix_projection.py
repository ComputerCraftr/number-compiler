"""Read an already-published radix consumer without starting execution."""

from collections.abc import MutableMapping

from number_compiler.projection.lazy_radix import RadixProjection
from number_compiler.projection.microblock_cache import MicroblockCache
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


def radix_projection(term: PoweredCollatzTerm, radix: int) -> RadixProjection:
    snapshot = term.radix_projection_audit_source(term.resource_ledger)
    assert snapshot is not None
    return snapshot.projections[radix]


def radix_projections(term: PoweredCollatzTerm) -> MutableMapping[int, RadixProjection]:
    """Read the exact existing bindings for audit and fault-injection tests."""
    snapshot = term.radix_projection_audit_source(term.resource_ledger)
    assert snapshot is not None
    return snapshot.projections


def microblock_cache(term: PoweredCollatzTerm) -> MicroblockCache:
    """Find the exact cache registered with this term's resource owner."""
    return next(
        root
        for root in term.resource_ledger.iter_execution_roots()
        if isinstance(root, MicroblockCache)
    )
