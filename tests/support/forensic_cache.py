"""Typed cache inspection at deliberate fault-injection test boundaries."""

from typing import cast

from number_compiler.resources.ledger import OwnedMemo
from number_compiler.resources.process_cache import CacheRecord, FullKey, ProcessCache


def process_cache_records(cache: ProcessCache) -> OwnedMemo[FullKey, CacheRecord]:
    """Inspect exact retained records for corruption and atomicity assertions."""
    return cast(
        OwnedMemo[FullKey, CacheRecord], object.__getattribute__(cache, "_entries")
    )
