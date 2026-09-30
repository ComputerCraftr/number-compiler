"""Record frozen-tree test evidence without sharing execution runtimes."""

from __future__ import annotations

import json
from collections.abc import Callable, Iterator

import pytest

from devtools.checks.test_run_evidence import (
    EXECUTION_MODE,
    FINGERPRINT_AFTER,
    FINGERPRINT_BEFORE,
    MANIFEST,
    NODE_ID,
    classify_execution_mode,
    source_fingerprint,
)
from devtools.paths import repository_root
from number_compiler.resources.process_cache import (
    CacheLease,
    ImmutableValue,
    ProcessCache,
)

_ROOT = repository_root()
_STAMP = pytest.StashKey[str]()


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


def pytest_sessionstart(session: pytest.Session) -> None:
    session.config.stash[_STAMP] = source_fingerprint(_ROOT)


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
    record_testsuite_property(FINGERPRINT_BEFORE, request.config.stash[_STAMP])
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
    record_testsuite_property(FINGERPRINT_AFTER, source_fingerprint(_ROOT))
