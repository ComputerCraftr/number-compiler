"""Admission routes for the published comma prefix.

Exact prefix admission uses exhaustive finite-region closure, not OEIS decision
bits as a branch oracle while the global theorem registry is empty. Once an
exact global-release provider is registered, its authenticated theorem can
admit the infinite source-20 path without the finite forest certificate.
"""

from __future__ import annotations

from hashlib import blake2b, sha256
from hmac import compare_digest
from importlib.resources import as_file, files
from pathlib import Path
from secrets import token_bytes
from typing import Final

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.unresolved_term import UnresolvedSequenceTerm
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import comma as _comma_keys
from number_compiler.resources.process_cache import MISSING, get_process_cache

CERTIFICATE_ID: Final[str] = "a367620-closed-regions-v1"
CERTIFICATE_ASSET = "comma_prefix_v1.jsonl.gz"
# Filled only from the independently generated, reviewed immutable certificate.
CERTIFICATE_SHA256 = "f6e864b26ca9c8164ed91594d995aca15b19e027166d469844be37268896e4eb"
CERTIFIED_MAX_INDEX = 412_987_860
FIRST_FORK_INDEX = 412_987_859
FIRST_FORK_VALUE = 19_999_999_918
FIRST_FORK_CHILDREN = (19_999_999_999, 20_000_000_000)
CertificateMemo = OwnedMemo[tuple[str, str], str]
_CACHE_AUTHORITY = token_bytes(32)


def new_certificate_memo(ledger: ResourceLedger) -> CertificateMemo:
    owner = ledger.register("comma-certificate-admission", "query_memo")
    return OwnedMemo(ledger, owner, nodes_per_entry=1, evictable=True)


def _admission_marker(generation: int) -> tuple[tuple[str, str], str]:
    local_key = (CERTIFICATE_ID, f"{CERTIFICATE_SHA256}:{generation}")
    tag = blake2b(
        repr(
            (
                local_key,
                20,
                10,
                CERTIFIED_MAX_INDEX,
                FIRST_FORK_INDEX,
                FIRST_FORK_VALUE,
                FIRST_FORK_CHILDREN,
            )
        ).encode(),
        key=_CACHE_AUTHORITY,
        digest_size=32,
    ).hexdigest()
    return local_key, tag


class UnresolvedCommaTerm(UnresolvedSequenceTerm):
    """The requested index is beyond currently admitted prefix evidence."""


def _charge(ledger: ResourceLedger, max_work: int, amount: int = 1) -> None:
    spent = ledger.counters.get(_comma_keys.COMMA_WORK, 0) + ledger.counters.get(
        _comma_keys.COMMA_CERTIFICATE_WORK, 0
    )
    if amount > max_work - spent:
        ledger.bump(_comma_keys.COMMA_BUDGET_REFUSALS)
        ledger.bump(_comma_keys.COMMA_CERTIFICATE_BUDGET_REFUSALS)
        raise BlockContextBudgetExceeded("comma certificate work budget exceeded")
    ledger.bump(_comma_keys.COMMA_CERTIFICATE_WORK, amount)


def unresolved_boundary(index: int) -> UnresolvedCommaTerm:
    return UnresolvedCommaTerm(
        index,
        CERTIFIED_MAX_INDEX,
        CERTIFICATE_ID,
        "the requested index exceeds the checked comma prefix",
    )


def _checked_asset(path: Path, ledger: ResourceLedger, max_work: int) -> None:
    digest = sha256()
    total = 0
    with path.open("rb") as stream:
        while True:
            _charge(ledger, max_work)
            chunk = stream.read(65536)
            if not chunk:
                break
            total += len(chunk)
            if total > 8 * 1024 * 1024:
                raise ValueError("comma certificate exceeds its compressed size limit")
            ledger.bump(_comma_keys.COMMA_CERTIFICATE_READ_BYTES, len(chunk))
            ledger.bump(_comma_keys.COMMA_OPERAND_BIT_WORK, 8 * len(chunk))
            digest.update(chunk)
    if digest.hexdigest() != CERTIFICATE_SHA256:
        raise ValueError("comma certificate checksum differs from its admitted version")


def _matches_marker(value: object, expected: str) -> bool:
    return (
        type(value) is str
        and len(value) == len(expected)
        and value.isascii()
        and compare_digest(value, expected)
    )


def _verify(
    ledger: ResourceLedger,
    max_work: int,
    shared_cache: bool,
    memo: CertificateMemo | None,
) -> None:
    def check(path: Path) -> None:
        # The verifier is needed only on a cold admission. A warm process-cache
        # hit must not import the forest parser or its gzip/JSON dependencies.
        from number_compiler.sequences.comma.forest_verifier import (
            verify_forest_certificate,
        )

        result = verify_forest_certificate(path, ledger, max_work)
        if (
            result.roots_exhausted != 49
            or result.sector_entries <= 0
            or result.prefix_index != FIRST_FORK_INDEX
            or result.prefix_value != FIRST_FORK_VALUE
            or result.prefix_children != FIRST_FORK_CHILDREN
        ):
            raise ValueError(
                "comma certificate verifier omitted required source coverage"
            )

    if memo is not None and memo.ledger is not ledger:
        raise ValueError("foreign comma certificate admission owner")

    def local_hit(local_key: tuple[str, str], tag: str) -> bool:
        _charge(ledger, max_work)
        previous = memo.get(local_key) if memo is not None else None
        if previous is None:
            return False
        if not _matches_marker(previous, tag):
            raise ValueError("forged comma certificate admission marker")
        return True

    def check_asset() -> None:
        asset = files("number_compiler").joinpath("kernels", CERTIFICATE_ASSET)
        with as_file(asset) as path:
            _checked_asset(path, ledger, max_work)
            check(path)

    # Bypassed queries keep only their own admission, independent of process
    # resets. Shared admissions instead consume a generation-bound lease even
    # on query-local hits; a reset during lookup must invalidate that authority.
    if not shared_cache:
        local_key, tag = _admission_marker(-1)
        if local_hit(local_key, tag):
            ledger.bump(_comma_keys.COMMA_CERTIFICATE_LOCAL_HITS)
            return
        ledger.bump(_comma_keys.COMMA_CERTIFICATE_CACHE_BYPASSES)
        check_asset()
        if memo is not None:
            memo[local_key] = tag
        return
    with get_process_cache().acquire(
        "comma-prefix-certificate", CERTIFICATE_ID, (20, 10, CERTIFICATE_SHA256)
    ) as lease:
        local_key, tag = _admission_marker(lease.stats().generation)

        def publish_local() -> None:
            try:
                if memo is not None:
                    memo[local_key] = tag
                lease.stats()
            except Exception:
                if memo is not None:
                    memo.pop(local_key, None)
                raise

        if local_hit(local_key, tag):
            lease.stats()  # Recheck authority after the query-local lookup.
            ledger.bump(_comma_keys.COMMA_CERTIFICATE_LOCAL_HITS)
            return
        key = (CERTIFIED_MAX_INDEX, FIRST_FORK_INDEX, FIRST_FORK_VALUE)
        expected = (CERTIFICATE_SHA256, tag)
        _charge(ledger, max_work)
        cached = lease.get(key)
        if cached is not MISSING:
            if (
                type(cached) is not tuple
                or len(cached) != 2
                or not _matches_marker(cached[0], expected[0])
                or not _matches_marker(cached[1], expected[1])
            ):
                raise ValueError("foreign comma certificate cache payload")
            publish_local()
            ledger.bump(_comma_keys.COMMA_CERTIFICATE_CACHE_HITS)
            return
        ledger.bump(_comma_keys.COMMA_CERTIFICATE_CACHE_MISSES)
        check_asset()
        _charge(ledger, max_work)
        if lease.put(key, expected):
            ledger.bump(_comma_keys.COMMA_CERTIFICATE_CACHE_PUBLICATIONS)
        publish_local()


def certificate_status(
    index: int,
    ledger: ResourceLedger,
    max_work: int,
    *,
    shared_cache: bool = True,
    memo: CertificateMemo | None = None,
) -> dict[str, object]:
    """Report existing query evidence without initiating admission or asset I/O.

    This snapshot is never an authorization token. Value consumers must call
    ``require_certified_index``, including after a process-cache reset.
    """
    index = require_integer(index, "comma index", 1)
    require_integer(max_work, "comma work budget", 1)
    if type(shared_cache) is not bool:
        raise TypeError("shared_cache must be a bool")
    if memo is not None and memo.ledger is not ledger:
        raise ValueError("foreign comma certificate admission owner")
    admitted = index <= CERTIFIED_MAX_INDEX
    verified = False
    if admitted and memo is not None and len(memo):
        generation = get_process_cache().generation if shared_cache else -1
        local_key, tag = _admission_marker(generation)
        previous = memo.get(local_key)
        if previous is not None:
            if not _matches_marker(previous, tag):
                raise ValueError("forged comma certificate admission marker")
            verified = not shared_cache or get_process_cache().generation == generation
    return {
        "family": "a367620",
        "status": "available" if admitted else "unknown",
        "certificate_id": CERTIFICATE_ID,
        "certificate_sha256": CERTIFICATE_SHA256,
        "certified_max_index": CERTIFIED_MAX_INDEX,
        "requested_index": index,
        "runtime_verified": verified,
        "isabelle_instance_checked": False,
        "proof_scope": "finite_root_and_first_fork_branch_closure",
        "reason": (
            "query has checked finite regions; complete Isabelle instance remains open"
            if verified
            else "prefix evidence available; this query has not verified it"
            if admitted
            else "the requested index exceeds the checked comma prefix"
        ),
    }


def require_certified_index(
    index: int,
    ledger: ResourceLedger,
    max_work: int,
    *,
    shared_cache: bool = True,
    memo: CertificateMemo | None = None,
    global_provider: object | None = None,
) -> None:
    index = require_integer(index, "comma index", 1)
    max_work = require_integer(max_work, "comma work budget", 1)
    if type(shared_cache) is not bool:
        raise TypeError("shared_cache must be a bool")
    if memo is not None and memo.ledger is not ledger:
        raise ValueError("foreign comma certificate admission owner")
    _charge(ledger, max_work)
    if global_provider is not None:
        from number_compiler.sequences.comma.future_provider import (
            SemanticFutureProviderLease,
            SemanticFutureProviderStore,
        )

        if type(global_provider) is not SemanticFutureProviderLease:
            raise TypeError(
                "comma global prefix authority needs its exact provider lease"
            )
        store = getattr(global_provider, "_store", None)
        if type(store) is not SemanticFutureProviderStore:
            raise TypeError("malformed comma global provider store binding")
        if getattr(store, "ledger", None) is not ledger:
            raise ValueError("foreign comma global provider admission owner")
        global_provider.require_global_release_admission()
        ledger.bump(_comma_keys.COMMA_GLOBAL_RELEASE_PREFIX_ADMISSIONS)
        return
    if index > CERTIFIED_MAX_INDEX:
        raise unresolved_boundary(index)
    _verify(ledger, max_work, shared_cache, memo)


def require_selected_child(
    *,
    source_index: int,
    source_value: int,
    children: tuple[int, ...],
    certificate_version: str,
    ledger: ResourceLedger,
    max_work: int,
    shared_cache: bool = True,
    memo: CertificateMemo | None = None,
) -> int:
    if (
        certificate_version != CERTIFICATE_ID
        or type(source_index) is not int
        or type(source_value) is not int
        or type(children) is not tuple
        or any(type(child) is not int for child in children)
        or source_index != FIRST_FORK_INDEX
        or source_value != FIRST_FORK_VALUE
        or children != FIRST_FORK_CHILDREN
    ):
        raise unresolved_boundary(source_index + 1)
    require_certified_index(
        source_index + 1, ledger, max_work, shared_cache=shared_cache, memo=memo
    )
    # The other child is a checked finite component. Every infinite root-20
    # continuation must therefore take this child, not merely the smaller one.
    return children[0]
