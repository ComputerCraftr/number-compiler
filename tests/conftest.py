"""Record frozen-tree test evidence without sharing execution runtimes."""

from __future__ import annotations

import json
import os
from collections.abc import Callable, Iterator

import pytest

pytest_plugins = ("devtools.checks.pytest_policy",)

from devtools.checks.test_run_evidence import (
    EXECUTION_MODE,
    GIT_COMMIT_AFTER,
    GIT_COMMIT_BEFORE,
    GIT_DIRTY_AFTER,
    GIT_DIRTY_BEFORE,
    GIT_OBJECT_FORMAT_AFTER,
    GIT_OBJECT_FORMAT_BEFORE,
    GIT_TREE_AFTER,
    GIT_TREE_BEFORE,
    MANIFEST,
    NODE_ID,
    PROVENANCE_MODE,
    PROVENANCE_MODE_ENV,
    classify_execution_mode,
)
from devtools.git_source import GitSource, git_source
from devtools.paths import repository_root
from number_compiler.resources.process_cache import (
    CacheLease,
    ImmutableValue,
    ProcessCache,
)

_ROOT = repository_root()
_STAMP = pytest.StashKey[GitSource]()


@pytest.fixture
def publication_blocked_cache(monkeypatch: pytest.MonkeyPatch) -> ProcessCache:
    """Admit the lease but leave no retained-byte headroom for publications."""
    cache = ProcessCache()
    original_acquire = cache.acquire

    def acquire_then_pin_budget(
        namespace: str, version: str, source_key: tuple[ImmutableValue, ...]
    ) -> CacheLease:
        lease = original_acquire(namespace, version, source_key)
        cache.max_bytes = cache.stats().bytes
        return lease

    monkeypatch.setattr(cache, "acquire", acquire_then_pin_budget)
    return cache


@pytest.fixture
def isolated_process_cache(monkeypatch: pytest.MonkeyPatch) -> Iterator[ProcessCache]:
    """Give cache-reset tests a fresh global without clearing other tests' state.

    The fixture scope is one test, so requests within a test still share the
    same process cache. The prior process cache is restored even when the test
    fails, and the isolated instance is invalidated before it is detached.
    """
    from number_compiler.resources import process_cache

    isolated = ProcessCache()
    with monkeypatch.context() as scoped:
        with process_cache._PROCESS_CACHE_LOCK:
            scoped.setattr(process_cache, "_PROCESS_CACHE", isolated)
        try:
            yield isolated
        finally:
            isolated.reset()
            with process_cache._PROCESS_CACHE_LOCK:
                scoped.undo()


def pytest_sessionstart(session: pytest.Session) -> None:
    session.config.stash[_STAMP] = git_source(_ROOT)


def pytest_collection_modifyitems(items: list[pytest.Item]) -> None:
    for item in items:
        item.user_properties.append((NODE_ID, item.nodeid))
        relative = item.path.relative_to(item.config.rootpath).as_posix()
        if relative.startswith("tests/validation/"):
            item.add_marker(pytest.mark.validation)
        filename = item.path.name
        if "/proofs/" in f"/{relative}":
            item.add_marker(pytest.mark.proof)
        if filename.startswith(
            ("test_semantic_", "test_quotient_", "test_diamond_quotient")
        ):
            item.add_marker(pytest.mark.algebra)
        if any(
            word in filename
            for word in ("payload", "source_authority", "exact_tree", "representation")
        ):
            item.add_marker(pytest.mark.representation)
        if any(
            word in filename
            for word in ("resource", "inventory", "metric", "reporting", "accounting")
        ):
            item.add_marker(pytest.mark.accounting)
        if filename.startswith("test_cli"):
            item.add_marker(pytest.mark.cli)


@pytest.fixture(scope="session", autouse=True)
def execution_evidence(
    request: pytest.FixtureRequest,
    record_testsuite_property: Callable[[str, object], None],
) -> Iterator[None]:
    before = request.config.stash[_STAMP]
    record_testsuite_property(
        PROVENANCE_MODE, os.environ.get(PROVENANCE_MODE_ENV, "development")
    )
    record_testsuite_property(GIT_COMMIT_BEFORE, before.commit)
    record_testsuite_property(GIT_TREE_BEFORE, before.tree)
    record_testsuite_property(GIT_OBJECT_FORMAT_BEFORE, before.object_format)
    record_testsuite_property(GIT_DIRTY_BEFORE, str(before.dirty).lower())
    record_testsuite_property(
        MANIFEST, json.dumps([item.nodeid for item in request.session.items])
    )
    options = request.config.option
    parallel = hasattr(request.config, "workerinput") or bool(
        getattr(options, "numprocesses", None)
    )
    record_testsuite_property(
        EXECUTION_MODE,
        classify_execution_mode(
            parallel=parallel,
            keyword=str(options.keyword),
            mark_expression=str(options.markexpr),
            deselected=bool(getattr(options, "deselect", ())),
            last_failed=bool(getattr(options, "lf", False)),
            collection_args=tuple(str(argument) for argument in request.config.args),
        ),
    )
    yield
    after = git_source(_ROOT)
    record_testsuite_property(GIT_COMMIT_AFTER, after.commit)
    record_testsuite_property(GIT_TREE_AFTER, after.tree)
    record_testsuite_property(GIT_OBJECT_FORMAT_AFTER, after.object_format)
    record_testsuite_property(GIT_DIRTY_AFTER, str(after.dirty).lower())
