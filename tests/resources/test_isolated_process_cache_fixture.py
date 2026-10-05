"""The cache-isolation fixture must preserve unrelated process state."""

from collections.abc import Iterator

import pytest

from number_compiler.resources import process_cache
from number_compiler.resources.process_cache import ProcessCache


@pytest.fixture
def seeded_prior_process_cache() -> Iterator[ProcessCache]:
    prior_global = process_cache._PROCESS_CACHE
    prior = ProcessCache()
    with process_cache._PROCESS_CACHE_LOCK:
        process_cache._PROCESS_CACHE = prior
    with prior.acquire("fixture-audit", "1", ("prior",)) as lease:
        assert lease.put(("sentinel",), (17,))
    try:
        yield prior
        assert process_cache._PROCESS_CACHE is prior
        assert prior.stats().entries == 1
    finally:
        with process_cache._PROCESS_CACHE_LOCK:
            process_cache._PROCESS_CACHE = prior_global


def test_isolated_process_cache_is_fresh_and_restores_prior_cache(
    seeded_prior_process_cache: ProcessCache,
    isolated_process_cache: ProcessCache,
) -> None:
    assert process_cache.get_process_cache() is isolated_process_cache
    assert isolated_process_cache is not seeded_prior_process_cache
    assert isolated_process_cache.stats().entries == 0
    assert seeded_prior_process_cache.stats().entries == 1

    with isolated_process_cache.acquire("fixture-audit", "1", ("isolated",)) as lease:
        assert lease.put(("sentinel",), (23,))
    assert isolated_process_cache.stats().entries == 1
