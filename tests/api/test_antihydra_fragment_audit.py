"""Independent source-binding controls for retained Antihydra fragments."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.antihydra.observers import SpaceTimeProjection
from number_compiler.sequences.antihydra.projection_fragments import (
    ProjectionFragment,
    ProjectionFragmentCache,
    ProjectionFragmentKey,
)
from number_compiler.sequences.antihydra.runtime import CylinderEngine, Run, run


def _projection(
    result: Run,
    *,
    width: int,
    time_width: int,
    sign: int,
    time_sign: int,
    modulus: int,
) -> SpaceTimeProjection:
    return SpaceTimeProjection(
        result,
        width,
        time_width,
        sign,
        time_sign,
        modulus,
        1_000_000,
    )


def _key_seal(
    key: ProjectionFragmentKey,
) -> tuple[int | tuple[int, int, int, int, int, int], ...]:
    return (
        key.source_owner,
        key.requested,
        key.start,
        key.cylinder,
        key.spatial_width,
        key.temporal_width,
        key.spatial_sign,
        key.temporal_sign,
        key.modulus,
        key.head_phase,
        key.time_phase,
    )


def _install_forged_binding(
    cache: ProjectionFragmentCache,
    key: ProjectionFragmentKey,
    fragment: ProjectionFragment,
) -> None:
    """Install a fully resealed malformed candidate at the injection boundary."""
    nodes = cache._nodes(key)
    cache.ledger.reserve_many(((cache.owner, 1, nodes), (cache.seal_owner, 1, 2)))
    cache.fragments[key] = fragment
    cache.seals[key] = (
        _key_seal(key),
        fragment.typed_ports,
        fragment.sampled_sweep_classes,
    )


def _forge_key(
    key: ProjectionFragmentKey,
    field: str,
    value: int,
) -> ProjectionFragmentKey:
    if field == "start":
        return replace(key, start=value)
    if field == "head_phase":
        return replace(key, head_phase=value)
    if field == "time_phase":
        return replace(key, time_phase=value)
    if field == "source_owner":
        return replace(key, source_owner=value)
    if field == "spatial_width":
        return replace(key, spatial_width=value)
    raise AssertionError("unknown forged fragment-key field")


def test_fragment_audit_scans_one_source_prefix_for_mixed_demands() -> None:
    engine = CylinderEngine()
    result = engine.execute(192)
    shorter = engine.execute(128)
    first = _projection(
        result,
        width=2,
        time_width=2,
        sign=-1,
        time_sign=1,
        modulus=3,
    )
    second = _projection(
        result,
        width=2,
        time_width=2,
        sign=1,
        time_sign=-1,
        modulus=5,
    )
    third = _projection(
        shorter,
        width=2,
        time_width=2,
        sign=-1,
        time_sign=-1,
        modulus=7,
    )
    first.evaluate()
    second.evaluate()
    third.evaluate()

    cache = result._engine.projection_fragments
    fragments = tuple(cache.fragments.items())
    seals = {key: cache.seals[key] for key, _ in fragments}
    cache.fragments.clear()
    cache.seals.clear()
    for key, fragment in reversed(fragments):
        cache.fragments[key] = fragment
        cache.seals[key] = seals[key]
    starts_by_source: dict[int, list[int]] = {}
    for key in cache.fragments:
        starts_by_source.setdefault(key.source_owner, []).append(key.start)
    assert starts_by_source == {
        result._term.segment_owner: [128, 64, 0, 128, 64, 0],
        shorter._term.segment_owner: [64, 0],
    }
    assert len({key.modulus for key in cache.fragments}) == 3
    before = result.ledger.counters.get(
        "antihydra_payload_audit_projection_fragment_steps", 0
    )

    audit = audit_registered_payloads(result.ledger)

    assert (
        audit.forbidden_future_payloads,
        audit.unbounded_future_integers,
        audit.unknown_payloads,
    ) == (0, 0, 0)
    # The two demand families on the first term need one 128-return prefix;
    # the shorter term needs one 64-return prefix. Auditing all eight fragments
    # independently would instead replay 448 returns.
    assert (
        result.ledger.counters["antihydra_payload_audit_projection_fragment_steps"]
        - before
        == 192
    )


@pytest.mark.parametrize(
    "field,value",
    (
        ("start", 1),
        ("start", True),
        ("head_phase", 0),
        ("time_phase", 0),
        ("source_owner", -1),
        ("spatial_width", 0),
    ),
)
def test_fragment_audit_rejects_resealed_forged_source_binding(
    field: str,
    value: int,
) -> None:
    result = run(64)
    projection = _projection(
        result,
        width=2,
        time_width=3,
        sign=-1,
        time_sign=1,
        modulus=5,
    )
    projection.evaluate()
    cache = result._engine.projection_fragments
    original_key = next(iter(cache.fragments))
    original_fragment = cache.fragments[original_key]
    forged_key = _forge_key(original_key, field, value)
    forged_fragment = replace(original_fragment, key=forged_key)
    cache.clear()
    _install_forged_binding(cache, forged_key, forged_fragment)

    audit = audit_registered_payloads(result.ledger)

    assert audit.forbidden_future_payloads > 0


def test_fragment_audit_rejects_resealed_foreign_term_authority() -> None:
    engine = CylinderEngine()
    result = engine.execute(64)
    foreign = engine.execute(128)
    projection = _projection(
        result,
        width=2,
        time_width=2,
        sign=-1,
        time_sign=1,
        modulus=3,
    )
    projection.evaluate()
    cache = engine.projection_fragments
    original_key = next(iter(cache.fragments))
    original_fragment = cache.fragments[original_key]
    forged_key = replace(
        original_key,
        source_owner=foreign._term.segment_owner,
    )
    forged_fragment = replace(original_fragment, key=forged_key)
    cache.clear()
    _install_forged_binding(cache, forged_key, forged_fragment)

    assert audit_registered_payloads(engine.ledger).forbidden_future_payloads > 0


def test_fragment_audit_does_not_approve_changed_seal_content() -> None:
    result = run(64)
    projection = _projection(
        result,
        width=2,
        time_width=2,
        sign=-1,
        time_sign=1,
        modulus=3,
    )
    projection.evaluate()
    cache = result._engine.projection_fragments
    key = next(iter(cache.fragments))
    original = cache.seals[key]
    cache.seals[key] = (original[0], original[1], original[2] + 1)
    try:
        assert audit_registered_payloads(result.ledger).forbidden_future_payloads > 0
    finally:
        cache.seals[key] = original
