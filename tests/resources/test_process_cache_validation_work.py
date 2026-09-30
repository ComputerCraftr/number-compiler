"""Adversarial work and admission checks for immutable cache wire values."""

from __future__ import annotations

from cProfile import Profile
from typing import Never, cast

import pytest

from number_compiler.resources import process_cache as cache_module
from number_compiler.resources.process_cache import ImmutableValue, ProcessCache


def test_shared_payload_dag_validation_does_not_expand_every_path() -> None:
    payload: ImmutableValue = ("leaf",)
    for _ in range(12):
        payload = (payload, payload)
    cache = ProcessCache(enabled=False)
    with cache.acquire("wire", "1", ("source",)) as lease:
        with Profile() as profile:
            assert not lease.put(("payload",), payload)
        stack_pops = sum(
            entry.callcount
            for entry in profile.getstats()
            if entry.code == "<method 'pop' of 'list' objects>"
        )
        # Thirteen shared tuple nodes, not the 8,191 expanded paths. The slack
        # includes the public lease/key validation and accounting work.
        assert 0 < stack_pops < 128


def test_shared_tuple_reached_deeper_still_checks_descendant_depth() -> None:
    shared: ImmutableValue = (("leaf",),)
    deep = shared
    for _ in range(62):
        deep = (deep,)
    cache = ProcessCache(enabled=False)
    with (
        cache.acquire("wire", "1", ("source",)) as lease,
        pytest.raises(ValueError, match="nesting limit"),
    ):
        # LIFO validation encounters the shallow alias first.
        lease.put(("payload",), (deep, shared))


def test_disabled_publication_skips_sizing_but_validates_payload(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cache = ProcessCache(enabled=False)
    with cache.acquire("wire", "1", ("source",)) as lease:
        before = cache.stats()

        def forbidden_size(_value: object) -> Never:
            raise AssertionError("disabled publication measured unused retention")

        monkeypatch.setattr(cache_module, "_deep_size", forbidden_size)
        assert not lease.put(("payload",), (1, 2, 3))
        with pytest.raises(TypeError, match="cache payload"):
            lease.put(("payload",), cast(ImmutableValue, [1, 2]))
        after = cache.stats()
        assert after.bytes == before.bytes
        assert after.entries == after.puts == 0
        assert after.bypasses == before.bypasses + 1


def test_disabled_explicit_accounting_claim_is_still_checked() -> None:
    cache = ProcessCache(enabled=False)
    with cache.acquire("wire", "1", ("source",)) as lease:
        with pytest.raises(ValueError, match="conservative estimate"):
            lease.put(("payload",), (1, 2), accounted_bytes=1)
        assert cache.stats().bypasses == 0
