"""Shared lifecycle assertion for the term-owned mod-99 result memo."""

from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def assert_accumulator99_cache_lifecycle(term: ReverseAddPoweredTerm) -> None:
    """Require one bounded retained result and complete explicit eviction."""
    ledger = term.resource_ledger
    assert (ledger.entries, ledger.nodes) == (1, 40)
    assert ledger.evict_query_memos()
    assert (ledger.entries, ledger.nodes) == (0, 0)


__all__ = ["assert_accumulator99_cache_lifecycle"]
