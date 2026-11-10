"""Independent source-binding controls for retained Antihydra fragments."""

from __future__ import annotations

from dataclasses import replace
from typing import cast

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
    nodes = cache.retained_nodes(key)
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
    value: object,
) -> ProjectionFragmentKey:
    if field not in {
        "start",
        "head_phase",
        "time_phase",
        "source_owner",
        "spatial_width",
    }:
        raise AssertionError("unknown forged fragment-key field")
    forged = replace(key)
    # Build a valid independent key, then inject corruption after publication
    # construction. In particular, bool must reach the audit instead of being
    # rejected by the public dataclass constructor.
    object.__setattr__(forged, field, value)
    return forged


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

    cache = result.source_engine.projection_fragments
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
        result.source_term.segment_owner: [128, 64, 0, 128, 64, 0],
        shorter.source_term.segment_owner: [64, 0],
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

    term = result.source_term
    engine = term.engine
    driver = engine.projection_fragment_driver
    image = term.arithmetic_workspace
    section = engine.projection_workspace
    from number_compiler.sequences.antihydra.projection_core import (
        AntihydraProjectionDriver,
    )

    assert type(driver) is AntihydraProjectionDriver
    assert image is not None and section is not None
    family_audit = result.ledger.audit_payload_contracts()
    roots = (
        engine,
        cache,
        term,
        image,
        driver.cursor,
        driver.adapter,
        section,
    )
    assert all(
        family_audit.owns_root("antihydra", root, ledger=result.ledger)
        for root in roots
    )
    assert family_audit.family("antihydra", ledger=result.ledger)[1] == frozenset()


def test_term_contract_rejects_matching_module_and_class_lookalike() -> None:
    from number_compiler.sequences.antihydra.payload_audit import (
        register_term_contract,
    )
    from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm

    def fail_if_ledger_is_read(_root: object) -> object:
        raise AssertionError("lookalike fields must not be read")

    lookalike_type = type(
        AntihydraArithmeticTerm.__name__,
        (),
        {
            "__module__": AntihydraArithmeticTerm.__module__,
            "ledger": property(fail_if_ledger_is_read),
        },
    )
    lookalike = cast(AntihydraArithmeticTerm, lookalike_type())

    with pytest.raises(TypeError, match="exact owner type"):
        register_term_contract(lookalike)


def test_antihydra_contract_owners_rebind_after_registry_reset() -> None:
    from number_compiler.sequences.antihydra.payload_audit import (
        register_arithmetic_image_contract,
        register_cursor_contract,
        register_engine_contract,
        register_fragment_adapter_contract,
        register_fragment_cache_contract,
        register_section_workspace_contract,
        register_term_contract,
    )

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
    ledger = result.ledger
    term = result.source_term
    engine = term.engine
    driver = engine.projection_fragment_driver
    image = term.arithmetic_workspace
    section = engine.projection_workspace
    from number_compiler.sequences.antihydra.projection_core import (
        AntihydraProjectionDriver,
    )

    assert type(driver) is AntihydraProjectionDriver
    assert image is not None and section is not None
    roots = (
        engine,
        engine.projection_fragments,
        term,
        image,
        driver.cursor,
        driver.adapter,
        section,
    )

    prior = ledger.audit_payload_contracts()
    assert all(prior.owns_root("antihydra", root, ledger=ledger) for root in roots)
    ledger.clear_payload_audit_contracts()
    assert not prior.is_current_for(ledger)
    assert ledger.audit_payload_contracts().family("antihydra", ledger=ledger) == (
        frozenset(),
        frozenset(),
    )

    register_engine_contract(engine)
    register_fragment_cache_contract(engine.projection_fragments)
    register_term_contract(term)
    register_arithmetic_image_contract(image)
    register_cursor_contract(driver.cursor)
    register_fragment_adapter_contract(driver.adapter)
    register_section_workspace_contract(section)
    rebound = ledger.audit_payload_contracts()
    assert all(rebound.owns_root("antihydra", root, ledger=ledger) for root in roots)
    assert rebound.family("antihydra", ledger=ledger)[1] == frozenset()


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
    value: object,
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
    cache = result.source_engine.projection_fragments
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
        source_owner=foreign.source_term.segment_owner,
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
    cache = result.source_engine.projection_fragments
    key = next(iter(cache.fragments))
    original = cache.seals[key]
    cache.seals[key] = (original[0], original[1], original[2] + 1)
    try:
        assert audit_registered_payloads(result.ledger).forbidden_future_payloads > 0
    finally:
        cache.seals[key] = original
