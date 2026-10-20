"""The cache-isolation fixture must preserve unrelated process state."""

from collections.abc import Iterator

import pytest

from number_compiler.resources.process_cache import (
    ProcessCache,
    get_process_cache,
    temporary_process_cache,
)


@pytest.fixture
def seeded_prior_process_cache() -> Iterator[ProcessCache]:
    prior = ProcessCache()
    with temporary_process_cache(prior):
        with prior.acquire("fixture-audit", "1", ("prior",)) as lease:
            assert lease.put(("sentinel",), (17,))
        yield prior
        assert get_process_cache() is prior
        assert prior.stats().entries == 1


@pytest.fixture
def isolated_process_cache_after_seeded_prior(
    seeded_prior_process_cache: ProcessCache,
) -> Iterator[ProcessCache]:
    isolated = ProcessCache()
    with temporary_process_cache(isolated):
        try:
            yield isolated
        finally:
            isolated.reset()


def test_isolated_process_cache_is_fresh_and_restores_prior_cache(
    seeded_prior_process_cache: ProcessCache,
    isolated_process_cache_after_seeded_prior: ProcessCache,
) -> None:
    isolated = isolated_process_cache_after_seeded_prior
    assert get_process_cache() is isolated
    assert isolated is not seeded_prior_process_cache
    assert isolated.stats().entries == 0
    assert seeded_prior_process_cache.stats().entries == 1

    with isolated.acquire("fixture-audit", "1", ("isolated",)) as lease:
        assert lease.put(("sentinel",), (23,))
    assert isolated.stats().entries == 1
