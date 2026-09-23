"""Runtime-checked finite branch certificates for the published comma prefix.

Exact prefix admission uses exhaustive finite-region closure, not OEIS decision
bits as a branch oracle. Kernel checking of the complete certificate instance
is a separate release obligation and is reported explicitly.
"""

from __future__ import annotations

from hashlib import blake2b, sha256
from hmac import compare_digest
from importlib.resources import as_file, files
from pathlib import Path
from secrets import token_bytes

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.unresolved_term import UnresolvedSequenceTerm
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.process_cache import MISSING, get_process_cache

CERTIFICATE_ID = "a367620-closed-regions-v1"
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


class UnresolvedCommaTerm(UnresolvedSequenceTerm):
    """The requested index is beyond currently admitted prefix evidence."""


def _charge(ledger: ResourceLedger, max_work: int, amount: int = 1) -> None:
    spent = ledger.counters.get("comma_work", 0) + ledger.counters.get(
        "comma_certificate_work", 0
    )
    if amount > max_work - spent:
        ledger.bump("comma_budget_refusals")
        ledger.bump("comma_certificate_budget_refusals")
        raise BlockContextBudgetExceeded("comma certificate work budget exceeded")
    ledger.bump("comma_certificate_work", amount)


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
            ledger.bump("comma_certificate_read_bytes", len(chunk))
            ledger.bump("comma_operand_bit_work", 8 * len(chunk))
            digest.update(chunk)
    if digest.hexdigest() != CERTIFICATE_SHA256:
        raise ValueError("comma certificate checksum differs from its admitted version")


def _verify(
    ledger: ResourceLedger,
    max_work: int,
    shared_cache: bool,
    memo: CertificateMemo | None,
) -> None:
    from number_compiler.sequences.comma.forest_verifier import (
        verify_forest_certificate,
    )

    def check(path: Path) -> None:
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

    asset = files("number_compiler").joinpath("kernels", CERTIFICATE_ASSET)
    with as_file(asset) as path:
        _checked_asset(path, ledger, max_work)
        generation = get_process_cache().generation if shared_cache else -1
        local_key = (CERTIFICATE_ID, f"{CERTIFICATE_SHA256}:{generation}")
        tag = blake2b(
            repr(
                (local_key, 20, 10, CERTIFIED_MAX_INDEX, FIRST_FORK_CHILDREN)
            ).encode(),
            key=_CACHE_AUTHORITY,
            digest_size=32,
        ).hexdigest()
        _charge(ledger, max_work)
        if memo is not None:
            if memo.ledger is not ledger:
                raise ValueError("foreign comma certificate admission owner")
            previous = memo.get(local_key)
            if previous is not None:
                if type(previous) is not str or not compare_digest(previous, tag):
                    raise ValueError("forged comma certificate admission marker")
                ledger.bump("comma_certificate_local_hits")
                return
        if not shared_cache:
            ledger.bump("comma_certificate_cache_bypasses")
            check(path)
            if memo is not None:
                memo[local_key] = tag
            return
        with get_process_cache().acquire(
            "comma-prefix-certificate", CERTIFICATE_ID, (20, 10, CERTIFICATE_SHA256)
        ) as lease:
            key = (CERTIFIED_MAX_INDEX, FIRST_FORK_INDEX, FIRST_FORK_VALUE)
            expected = (CERTIFICATE_SHA256, tag)
            _charge(ledger, max_work)
            cached = lease.get(key)
            if cached is not MISSING:
                if cached != expected or type(cached) is not tuple:
                    raise ValueError("foreign comma certificate cache payload")
                ledger.bump("comma_certificate_cache_hits")
                if memo is not None:
                    memo[local_key] = tag
                return
            ledger.bump("comma_certificate_cache_misses")
            check(path)
            _charge(ledger, max_work)
            if lease.put(key, expected):
                ledger.bump("comma_certificate_cache_publications")
            if memo is not None:
                memo[local_key] = tag


def certificate_status(
    index: int,
    ledger: ResourceLedger,
    max_work: int,
    *,
    shared_cache: bool = True,
    memo: CertificateMemo | None = None,
) -> dict[str, object]:
    index = require_integer(index, "comma index", 1)
    max_work = require_integer(max_work, "comma work budget", 1)
    if type(shared_cache) is not bool:
        raise TypeError("shared_cache must be a bool")
    _charge(ledger, max_work)
    admitted = index <= CERTIFIED_MAX_INDEX
    if admitted:
        _verify(ledger, max_work, shared_cache, memo)
    return {
        "family": "a367620",
        "status": "available" if admitted else "unknown",
        "certificate_id": CERTIFICATE_ID,
        "certificate_sha256": CERTIFICATE_SHA256,
        "certified_max_index": CERTIFIED_MAX_INDEX,
        "requested_index": index,
        "runtime_verified": admitted,
        "isabelle_instance_checked": False,
        "proof_scope": "finite_root_and_first_fork_branch_closure",
        "reason": (
            "runtime-checked finite regions; complete Isabelle instance remains open"
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
) -> None:
    status = certificate_status(
        index, ledger, max_work, shared_cache=shared_cache, memo=memo
    )
    if status["status"] != "available":
        raise unresolved_boundary(index)


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
