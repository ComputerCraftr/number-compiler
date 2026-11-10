"""Fail-closed global semantic-future admission for public A367620 queries.

Finite forest evidence is retained only as historical audit material. Public
values require the exact registered global Isabelle release artifact and a
source-owned, generation-valid provider lease. An empty registry refuses every
index without loading package data or guessing a branch.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Final

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.unresolved_term import UnresolvedSequenceTerm
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import comma as _comma_keys
from number_compiler.sequences.comma.future_authority import (
    GLOBAL_RELEASE_CONTRACT_ID,
    GLOBAL_RELEASE_SESSION_ID,
    GLOBAL_RELEASE_THEOREM_ID,
)

if TYPE_CHECKING:
    from number_compiler.sequences.comma.future_provider import SemanticFutureProvider


CERTIFICATE_ID: Final[str] = GLOBAL_RELEASE_CONTRACT_ID
NO_ADMITTED_INDEX = 0


class UnresolvedCommaTerm(UnresolvedSequenceTerm):
    """A requested comma term lacks an admitted global release artifact."""


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
    index = require_integer(index, "comma index", 1)
    return UnresolvedCommaTerm(
        index,
        NO_ADMITTED_INDEX,
        CERTIFICATE_ID,
        "no kernel-admitted global comma future is registered",
    )


def _registered_global_release_digest() -> str | None:
    from number_compiler.sequences.comma.future_provider import (
        registered_global_release_artifact_sha256,
    )

    return registered_global_release_artifact_sha256()


def _require_global_provider(
    global_provider: object | None,
    ledger: ResourceLedger,
    *,
    record_metrics: bool = True,
) -> SemanticFutureProvider:
    from number_compiler.sequences.comma.future_provider import (
        SemanticFutureProviderLease,
    )

    if type(global_provider) is not SemanticFutureProviderLease:
        raise TypeError("comma global prefix authority needs its exact provider lease")
    if global_provider.resource_ledger is not ledger:
        raise ValueError("foreign comma global provider admission owner")
    provider = (
        global_provider.resolve_provider()
        if record_metrics
        else global_provider.status_provider()
    )
    if provider is None:
        raise PermissionError("comma provider lease is stale or no longer retained")
    provider.require_global_release_admission()
    expected = _registered_global_release_digest()
    if expected is None or provider.artifact_sha256 != expected:
        raise PermissionError("comma provider differs from the global release registry")
    return provider


def certificate_status(
    index: int,
    ledger: ResourceLedger,
    max_work: int,
    *,
    global_provider: object | None = None,
) -> dict[str, object]:
    """Return metadata only; this function never loads or constructs a provider."""
    index = require_integer(index, "comma index", 1)
    require_integer(max_work, "comma work budget", 1)
    if type(ledger) is not ResourceLedger:
        raise TypeError("comma status needs its exact query ledger")
    digest = _registered_global_release_digest()
    runtime_verified = False
    if global_provider is not None:
        provider = _require_global_provider(
            global_provider, ledger, record_metrics=False
        )
        digest = provider.artifact_sha256
        runtime_verified = True
    registered = digest is not None
    return {
        "family": "a367620",
        "status": "available" if registered else "unknown",
        "certificate_id": CERTIFICATE_ID,
        "certificate_sha256": digest,
        "certified_max_index": None,
        "requested_index": index,
        "runtime_verified": runtime_verified,
        "isabelle_instance_checked": registered,
        "proof_scope": "global_decimal_root_future_safety",
        "proof_session_id": GLOBAL_RELEASE_SESSION_ID if registered else None,
        "proof_theorem_id": GLOBAL_RELEASE_THEOREM_ID if registered else None,
        "coverage": "all_positive_indices" if registered else "none",
        "global_release_registered": registered,
        "reason": (
            "the registered global release provider is admitted for this query"
            if runtime_verified
            else "the global release theorem is registered; runtime provider is not loaded"
            if registered
            else "no kernel-admitted global comma future is registered"
        ),
    }


def require_certified_index(
    index: int,
    ledger: ResourceLedger,
    max_work: int,
    *,
    global_provider: object | None = None,
) -> None:
    index = require_integer(index, "comma index", 1)
    require_integer(max_work, "comma work budget", 1)
    if type(ledger) is not ResourceLedger:
        raise TypeError("comma admission needs its exact query ledger")
    if global_provider is None:
        raise unresolved_boundary(index)
    _charge(ledger, max_work)
    _require_global_provider(global_provider, ledger)
    ledger.bump(_comma_keys.COMMA_GLOBAL_RELEASE_PREFIX_ADMISSIONS)
