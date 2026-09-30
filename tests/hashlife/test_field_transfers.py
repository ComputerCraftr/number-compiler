"""Recursive field images separate source occurrences from semantic macrocells."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaToken,
)
from tests.support.assertions import assert_rejected_atomically
from tests.support.recursive_field_images import _PortID, _transfer_setup


def test_point_and_width_use_parent_transfer_without_exact_future_images() -> None:
    (
        _,
        source,
        signature,
        geometry,
        action,
        images,
        adapter,
        transfers,
        executor,
    ) = _transfer_setup()
    incoming = _PortID(adapter.port_owner, "test-boundary", 0)
    application = executor.application(action, source, geometry, signature, incoming)
    assert application.point(0) == 0
    assert application.active_width() == 1
    assert adapter.compile_calls == 1
    assert transfers.retained_transfers == transfers.retained_bindings == 1
    assert images.retained_images == images.retained_bindings == 0
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    assert collect_ledger_metrics(application.ledger).total_internal_action_work >= 1


def test_cold_transfer_point_cannot_publish_exact_images(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        _,
        source,
        signature,
        geometry,
        action,
        images,
        adapter,
        transfers,
        executor,
    ) = _transfer_setup()

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("point path attempted to construct an exact field image")

    monkeypatch.setattr(images, "probe", forbidden)
    monkeypatch.setattr(images, "publish", forbidden)
    application = executor.application(
        action,
        source,
        geometry,
        signature,
        _PortID(adapter.port_owner, "test-boundary", 0),
    )
    assert application.point(0) == 0
    assert transfers.retained_transfers == 1
    assert images.retained_images == images.retained_bindings == 0


def test_concrete_port_values_share_one_parametric_parent_transfer() -> None:
    (
        _,
        source,
        signature,
        geometry,
        action,
        images,
        adapter,
        transfers,
        executor,
    ) = _transfer_setup()
    zero = executor.application(
        action,
        source,
        geometry,
        signature,
        _PortID(adapter.port_owner, "test-boundary", 0),
    )
    one = executor.application(
        action,
        source,
        geometry,
        signature,
        _PortID(adapter.port_owner, "test-boundary", 1),
    )
    assert zero.point(0) == 0
    assert one.point(0) == 1
    assert zero.active_width() == 1
    assert one.active_width() == 2
    assert adapter.compile_calls == 1
    assert transfers.retained_transfers == transfers.retained_bindings == 1
    assert images.retained_images == 0


def test_eviction_drops_transfer_bindings_but_preserves_canonical_ids() -> None:
    (
        ledger,
        source,
        signature,
        geometry,
        action,
        _,
        adapter,
        transfers,
        executor,
    ) = _transfer_setup()
    first = executor.transfer(action, source, geometry, signature)
    ledger.evict_query_memos()
    assert transfers.resolve(first).extent_bound == 2
    assert transfers.retained_bindings == 0
    second = executor.transfer(action, source, geometry, signature)
    assert second == first
    assert transfers.resolve(second).extent_bound == 2
    assert adapter.compile_calls == 2


@pytest.mark.parametrize("alias", (True, 0.0, 1.0))
def test_transfer_integer_aliases_reject_before_lookup_or_mutation(
    alias: bool | float,
) -> None:
    (
        ledger,
        source,
        signature,
        geometry,
        action,
        _,
        adapter,
        transfers,
        executor,
    ) = _transfer_setup()
    valid = executor.transfer(action, source, geometry, signature)
    forged = type(valid)(valid.owner, valid.kind, valid.local_id)
    object.__setattr__(forged, "local_id", alias)
    before = assert_rejected_atomically(
        ledger, lambda: transfers.resolve(forged), ValueError, match="malformed"
    )

    foreign = type(valid)(ArenaToken("foreign-transfer"), valid.kind, valid.local_id)
    with pytest.raises(ValueError, match="different arena"):
        transfers.resolve(foreign)
    assert ledger.snapshot() == before
    assert adapter.compile_calls == 1


def test_field_transfer_observation_rechecks_handle_before_transfer_lookup(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        _,
        source,
        signature,
        geometry,
        action,
        _,
        adapter,
        transfers,
        executor,
    ) = _transfer_setup()
    application = executor.application(
        action,
        source,
        geometry,
        signature,
        _PortID(adapter.port_owner, "test-boundary", 0),
    )
    transfer = application._transfer()
    malformed = _PortID(adapter.port_owner, "test-boundary", 0)
    object.__setattr__(malformed, "local_id", False)

    def poison(_reference: object) -> Never:
        raise AssertionError("malformed port reached transfer storage")

    monkeypatch.setattr(transfers, "resolve", poison)
    with pytest.raises(ValueError, match="malformed scoped handle"):
        executor.point(transfer, source, malformed, 0)
    with pytest.raises(ValueError, match="malformed scoped handle"):
        executor.width(transfer, source, malformed)
