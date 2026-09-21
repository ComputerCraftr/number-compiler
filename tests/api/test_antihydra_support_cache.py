"""Independent controls for bounded image reuse and arithmetic cache admission."""

import gc
import subprocess
import sys
from collections.abc import Hashable
from dataclasses import replace
from random import Random
from weakref import ref

import pytest

from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundSchedulerCore,
    SourceImageCandidate,
    SourceImageView,
)
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.antihydra.observers import SpaceTimeProjection
from number_compiler.sequences.antihydra.projection_core import (
    AntihydraFragmentID,
    AntihydraProjectionDriver,
)
from number_compiler.sequences.antihydra.projection_occurrences import (
    ProjectionOccurrenceCursor,
)
from number_compiler.sequences.antihydra.runtime import CylinderEngine, run


def test_empty_fragment_cache_does_not_import_observation_executor() -> None:
    subprocess.run(
        [
            sys.executable,
            "-I",
            "-c",
            (
                "import sys\n"
                "import number_compiler.sequences.antihydra.projection_fragments\n"
                "assert 'number_compiler.hashlife.execution.source_bound_images' "
                "not in sys.modules\n"
            ),
        ],
        check=True,
        capture_output=True,
        text=True,
        timeout=5,
    )


@pytest.mark.parametrize(
    "width,time_width,sign,time_sign,modulus",
    (
        (2, 2, -1, 1, 3),
        (3, 4, -1, -1, 7),
        (2, 3, 1, -1, 4),
        (1, 1, -1, -1, 2),
    ),
)
def test_image_period_reduction_preserves_all_typed_ports(
    width: int,
    time_width: int,
    sign: int,
    time_sign: int,
    modulus: int,
) -> None:
    result = run(0)
    rng = Random(912)
    cases = [(a, b) for a in (0, 1, 12) for b in (3, 4, 75, 1000)]
    cases += [(rng.randrange(10000), rng.randrange(3, 100000)) for _ in range(12)]
    for a, b in cases:
        projection = SpaceTimeProjection(
            result, width, time_width, sign, time_sign, modulus, 1000000
        )
        original = projection._section(a, b)[0]
        reduced = projection._section(*projection._section_key(a, b))[0]
        assert original == reduced


def test_cached_images_are_exact_and_released_after_demand() -> None:
    cached, uncached = run(512), run(512)
    primitive_before = cached.ledger.counters.get(
        "source_image_primitive_applications", 0
    )
    compositions_before = cached.ledger.counters.get(
        "source_image_chronological_compositions", 0
    )
    baseline = SpaceTimeProjection(
        uncached, 2, 2, -1, 1, 3, 1000000, cache_entries=0
    ).evaluate()
    observed = SpaceTimeProjection(cached, 2, 2, -1, 1, 3, 1000000).evaluate()
    assert {k: v for k, v in observed.items() if k != "sampled_sweep_classes"} == {
        k: v for k, v in baseline.items() if k != "sampled_sweep_classes"
    }
    assert cached.ledger.counters["spacetime_projection_fragment_publications"] == 8
    assert cached.ledger.counters["spacetime_projection_fragment_evaluations"] == 8
    assert (
        cached.ledger.counters["source_image_primitive_applications"] - primitive_before
        == 64
    )
    assert (
        cached.ledger.counters["source_image_chronological_compositions"]
        - compositions_before
        == 56
    )
    assert cached.ledger.counters.get("observer_macro_discovery_steps", 0) == 0
    assert cached.ledger.counters.get("observer_retained_support_steps", 0) == 0
    assert (
        cached.ledger.counters["antihydra_projection_block_image_discovery_steps"]
        == 512
    )
    assert (
        cached.ledger.counters.get("spacetime_projection_fragment_leaf_returns", 0) == 0
    )
    assert cached.ledger.counters["spacetime_projection_fragment_translations"] == 8
    leaf_rows = [
        row
        for row in cached.ledger.inventory()
        if row.name == "antihydra.observer.leaf-roofs"
    ]
    # The composed cylinder-fragment path obtains its checked roof directly
    # from each bounded arithmetic leaf; the retired scalar support iterator
    # and its separate two-leaf workspace are never constructed.
    assert leaf_rows == []
    for row in cached.ledger.inventory():
        if (
            row.name.startswith("antihydra.spacetime")
            and ".fragments." not in row.name
            and ".fragment-seals." not in row.name
        ):
            assert row.entries == row.nodes == 0
    assert audit_registered_payloads(cached.ledger).forbidden_future_payloads == 0

    before = dict(cached.ledger.counters)
    repeated = SpaceTimeProjection(cached, 2, 2, -1, 1, 3, 1000000).evaluate()
    assert repeated == observed
    after = cached.ledger.counters
    assert (
        after["spacetime_projection_fragment_hits"]
        - before.get("spacetime_projection_fragment_hits", 0)
        == 8
    )
    assert (
        after["antihydra_projection_block_image_discovery_steps"]
        == before["antihydra_projection_block_image_discovery_steps"]
    )
    assert (
        after["source_image_primitive_applications"]
        == before["source_image_primitive_applications"]
    )


def test_fragment_eviction_keeps_only_detached_projection_ownership() -> None:
    result = run(128)
    first_query = SpaceTimeProjection(result, 2, 2, -1, 1, 3, 1000000, cache_entries=1)
    expected = first_query.evaluate()
    cache = result._engine.projection_fragments
    first_keys = tuple(cache.fragments)
    assert len(first_keys) == 1

    SpaceTimeProjection(result, 2, 2, 1, -1, 5, 1000000, cache_entries=1).evaluate()
    assert len(cache.fragments) == 1
    assert tuple(cache.fragments) != first_keys
    assert result.ledger.counters["spacetime_projection_fragment_evictions"] > 0

    assert first_query.evaluate() == expected
    assert audit_registered_payloads(result.ledger).forbidden_future_payloads == 0
    assert result.ledger.max_nodes is not None
    assert result.ledger.peak_nodes <= result.ledger.max_nodes


def test_equal_translated_section_images_are_combined_in_the_coefficient_ring() -> None:
    result = run(0)
    projection = SpaceTimeProjection(result, 2, 2, -1, 1, 5, 1000000)
    area = projection.width * projection.time_width
    image, _ = projection._section(1, 3)
    expected = [[0] * area for _ in range(12)]
    projection._shift(expected, image, 1, 1)
    projection._shift(expected, image, 1, 1)

    actual = [[0] * area for _ in range(12)]
    workspace = projection.result._engine.projection_workspace
    if workspace is None:
        from number_compiler.sequences.antihydra.projection_workspace import (
            SectionImageWorkspace,
        )

        workspace = SectionImageWorkspace(result.ledger)
        projection.result._engine.projection_workspace = workspace
    workspace.start(area)
    try:
        key = projection._section_key(1, 3)
        projection._flush_section_classes(actual, {(key, 1, 1): 2}, workspace, 0)
    finally:
        workspace.clear()
    assert actual == expected


@pytest.mark.parametrize(
    "field,value",
    (
        ("constant", 1 << 10000),
        ("width", True),
        ("output", -1),
        ("minimum", 10),
        ("ledger_coefficient", 9),
    ),
)
def test_shared_audit_rejects_forged_cylinder_fields(field: str, value: int) -> None:
    engine = CylinderEngine()
    result = engine.execute(64)
    engine.cylinder(0, 64)
    key = next(iter(engine.memo))
    engine.memo[key] = replace(engine.memo[key], **{field: value})
    assert audit_registered_payloads(result.ledger).forbidden_future_payloads > 0


def test_shared_audit_rejects_wrong_key_and_live_unaccounted_stack() -> None:
    engine = CylinderEngine()
    result = engine.execute(64)
    engine.cylinder(0, 64)
    key = next(iter(engine.memo))
    block = engine.memo[key]
    engine.memo[(64, 100)] = block
    assert audit_registered_payloads(result.ledger).forbidden_future_payloads > 0
    del engine.memo[(64, 100)]
    assert audit_registered_payloads(result.ledger).forbidden_future_payloads == 0
    with pytest.raises(RuntimeError, match="prior ledger reservation"):
        engine.stack.append((64, 0, False))
    engine.ledger.reserve(engine.workspace, entries=1, nodes=1)
    engine.stack.append((64, 0, False))
    assert audit_registered_payloads(result.ledger).forbidden_future_payloads > 0
    engine.stack.clear()
    engine.ledger.release(engine.workspace, entries=1, nodes=1)


def test_audit_recomputation_work_is_visible() -> None:
    result = run(64)
    before = result.ledger.counters.get("dyadic_payload_audit_branch_steps", 0)
    audit = audit_registered_payloads(result.ledger)
    assert (
        audit.forbidden_future_payloads,
        audit.unbounded_future_integers,
        audit.unknown_payloads,
    ) == (0, 0, 0)
    assert result.ledger.counters["dyadic_payload_audit_branch_steps"] - before == 64
    assert result.ledger.counters["antihydra_payload_audit_physical_steps"] == 64


def test_repeated_queries_and_budget_failure_reuse_empty_workspace() -> None:
    result = run(64)
    first = SpaceTimeProjection(result, 2, 2, -1, 1, 3, 1000000).evaluate()
    owners = len(result.ledger.inventory())
    with pytest.raises(ValueError, match="budget"):
        SpaceTimeProjection(result, 3, 4, 1, -1, 7, 1).evaluate()
    SpaceTimeProjection(result, 3, 4, 1, -1, 7, 1000000).evaluate()
    assert SpaceTimeProjection(result, 2, 2, -1, 1, 3, 1000000).evaluate() == first
    assert len(result.ledger.inventory()) == owners
    assert all(row.accounting_delta in (0, None) for row in result.ledger.inventory())


def test_halt_image_never_aliases_positive_ledger_image() -> None:
    projection = SpaceTimeProjection(run(0), 2, 3, -1, -1, 4, 1000000)
    for b in (3, 99, 1000001):
        assert projection._section_key(0, b) != projection._section_key(24, b)


def test_retained_projection_fragment_rejects_same_shape_substitution() -> None:
    result = run(64)
    request = SpaceTimeProjection(result, 2, 2, -1, 1, 3, 1_000_000)
    request.evaluate()
    cache = result._engine.projection_fragments
    key = next(iter(cache.fragments))
    original = cache.fragments[key]
    cache.fragments[key] = replace(
        original, sampled_sweep_classes=original.sampled_sweep_classes + 1
    )
    try:
        with pytest.raises(ValueError, match="fragment binding was changed"):
            request.evaluate()
        assert audit_registered_payloads(result.ledger).forbidden_future_payloads > 0
    finally:
        cache.fragments[key] = original


def test_retained_projection_fragment_seal_is_an_independent_snapshot() -> None:
    result = run(64)
    request = SpaceTimeProjection(result, 2, 2, -1, 1, 3, 1_000_000)
    request.evaluate()
    cache = result._engine.projection_fragments
    fragment = next(iter(cache.fragments.values()))
    original = fragment.typed_ports
    changed = list(original)
    changed[0] = tuple((value + 1) % fragment.key.modulus for value in changed[0])
    object.__setattr__(fragment, "typed_ports", tuple(changed))
    try:
        with pytest.raises(ValueError, match="fragment binding was changed"):
            request.evaluate()
        assert audit_registered_payloads(result.ledger).forbidden_future_payloads > 0
    finally:
        object.__setattr__(fragment, "typed_ports", original)


def test_detached_fragment_requires_live_source_image_issuance() -> None:
    result = run(64)
    request = SpaceTimeProjection(result, 2, 2, -1, 1, 3, 1_000_000)
    expected = request.evaluate()
    cache = result._engine.projection_fragments
    key = next(iter(cache.fragments))
    original = cache.fragments[key]
    invalid = replace(original, typed_ports=tuple((0,) * key.area for _ in range(12)))
    cache._drop(key)
    driver = result._engine.projection_fragment_driver
    assert type(driver) is AntihydraProjectionDriver
    for fragment in (original, invalid):
        for issuer in (None, driver, object()):
            with pytest.raises(ValueError, match="active source-image publication"):
                cache.put(fragment, 32, issuer=issuer)
    assert not cache.fragments
    assert request.evaluate() == expected
    audit = audit_registered_payloads(result.ledger)
    assert (audit.forbidden_future_payloads, audit.unknown_payloads) == (0, 0)


def test_live_fragment_cache_computes_coefficients_from_image(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.antihydra.projection_fragments import (
        ProjectionFragment,
        ProjectionFragmentCache,
    )

    result = run(64)
    request = SpaceTimeProjection(result, 2, 2, -1, 1, 3, 1_000_000)
    expected = request.evaluate()
    cache = result._engine.projection_fragments
    original_fragment = next(iter(cache.fragments.values()))
    invalid = replace(original_fragment, typed_ports=((0, 0, 0, 0),) * 12)
    cache.clear()
    put = ProjectionFragmentCache.put
    calls = 0

    def check_live(
        target: ProjectionFragmentCache,
        image: object,
        capacity: int,
        *,
        issuer: object = None,
    ) -> ProjectionFragment:
        nonlocal calls
        calls += 1
        assert type(issuer) is AntihydraProjectionDriver
        assert issuer.adapter.projection is request
        with pytest.raises(ValueError, match="active source-image publication"):
            put(target, invalid, capacity, issuer=issuer)
        return put(target, image, capacity, issuer=issuer)

    monkeypatch.setattr(ProjectionFragmentCache, "put", check_live)
    assert request.evaluate() == expected
    assert calls == 1


def test_projection_reauthenticates_source_when_it_is_demanded() -> None:
    result = run(64)
    request = SpaceTimeProjection(result, 2, 2, -1, 1, 3, 1_000_000)
    block = result._term.segments[0].cylinder
    original = block.parity_word
    object.__setattr__(block, "parity_word", original ^ 1)
    try:
        with pytest.raises(ValueError, match="arithmetic support was changed"):
            request.evaluate()
    finally:
        object.__setattr__(block, "parity_word", original)


def test_fragment_authority_includes_both_twists_and_lane_sizes() -> None:
    result = run(64)
    for width, time_width, sign, time_sign in (
        (2, 3, -1, 1),
        (2, 3, 1, 1),
        (2, 3, -1, -1),
        (3, 2, -1, 1),
    ):
        SpaceTimeProjection(
            result,
            width,
            time_width,
            sign,
            time_sign,
            5,
            1_000_000,
        ).evaluate()
    keys = tuple(result._engine.projection_fragments.fragments)
    assert len(keys) == 4
    assert (
        len(
            {
                (
                    key.spatial_width,
                    key.temporal_width,
                    key.spatial_sign,
                    key.temporal_sign,
                )
                for key in keys
            }
        )
        == 4
    )


def test_shared_fragment_driver_reuses_owners_and_releases_request_context() -> None:
    result = run(8)
    inventory_after_first: int | None = None
    for index in range(40):
        request = SpaceTimeProjection(
            result,
            1 + index % 5,
            1 + (index // 5) % 5,
            -1 if index & 1 else 1,
            -1 if index & 2 else 1,
            3 + index % 11,
            20_000_000,
        )
        request.evaluate()
        if inventory_after_first is None:
            inventory_after_first = len(result.ledger.inventory())
    assert len(result.ledger.inventory()) == inventory_after_first
    request_reference = ref(request)
    del request
    gc.collect()
    assert request_reference() is None

    driver = result._engine.projection_fragment_driver
    assert type(driver) is AntihydraProjectionDriver
    assert driver.adapter.projection is None
    assert not driver.adapter._records
    assert not driver.adapter._seals
    assert not driver.core._nodes
    assert not driver.core._applications
    audit = audit_registered_payloads(result.ledger)
    assert (
        audit.forbidden_future_payloads,
        audit.unbounded_future_integers,
        audit.unknown_payloads,
    ) == (0, 0, 0)


def test_shared_fragment_failure_clears_images_and_active_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.antihydra.projection_core import (
        _AntihydraFragmentAdapter,
    )

    result = run(64)
    original = _AntihydraFragmentAdapter.apply_primitive
    calls = 0

    def fail_second_leaf(
        adapter: _AntihydraFragmentAdapter,
        action: Hashable,
        source: SourceImageView,
    ) -> SourceImageCandidate:
        nonlocal calls
        calls += 1
        if calls == 2:
            raise ValueError("injected primitive failure")
        return original(adapter, action, source)

    monkeypatch.setattr(_AntihydraFragmentAdapter, "apply_primitive", fail_second_leaf)
    with pytest.raises(ValueError, match="injected primitive failure"):
        SpaceTimeProjection(result, 2, 2, -1, 1, 3, 1_000_000).evaluate()
    driver = result._engine.projection_fragment_driver
    assert type(driver) is AntihydraProjectionDriver
    assert driver.adapter.projection is None
    assert not driver.adapter._records
    assert not driver.adapter._seals
    assert not driver.core._nodes
    assert not driver.core._origins
    assert not driver.core._applications
    assert not driver.core._projections


def test_fragment_payload_authority_rotates_between_builds() -> None:
    from number_compiler.sequences.antihydra.projection_core import (
        _AntihydraFragmentAdapter,
    )

    result = run(8)
    projection = SpaceTimeProjection(result, 2, 2, -1, 1, 3, 1_000_000)
    adapter = _AntihydraFragmentAdapter(result.ledger)
    cursor = ProjectionOccurrenceCursor(result.ledger)
    cursor.begin(projection)
    occurrence = cursor.next()
    assert occurrence is not None
    adapter.configure(cursor, occurrence, 0)
    stale = adapter.admit_source(adapter.source()).payload
    assert type(stale) is AntihydraFragmentID
    adapter.clear_context()
    adapter.configure(cursor, occurrence, 0)
    adapter.admit_source(adapter.source())
    try:
        with pytest.raises(ValueError, match="different arena"):
            adapter.resolve(stale)
    finally:
        adapter.clear_context()
        cursor.clear()


def test_fragment_prefix_seal_rejects_in_place_field_change() -> None:
    from number_compiler.sequences.antihydra.projection_core import (
        AntihydraFragmentAction,
        AntihydraFragmentID,
        _AntihydraFragmentAdapter,
    )

    result = run(8)
    projection = SpaceTimeProjection(result, 2, 2, -1, 1, 3, 1_000_000)
    adapter = _AntihydraFragmentAdapter(result.ledger)
    core = SourceBoundSchedulerCore(result.ledger)
    cursor = ProjectionOccurrenceCursor(result.ledger)
    cursor.begin(projection)
    occurrence = cursor.next()
    assert occurrence is not None
    adapter.configure(cursor, occurrence, 0)
    core.register(adapter)
    image = core.apply(adapter, adapter.source(), AntihydraFragmentAction(0, 8))
    handle = core.view(image).payload
    assert type(handle) is AntihydraFragmentID
    record = adapter.resolve(handle)
    assert record.prefix is not None
    original = record.prefix.output
    object.__setattr__(record.prefix, "output", original + 1)
    try:
        with pytest.raises(ValueError, match="payload was changed"):
            adapter.resolve(handle)
    finally:
        object.__setattr__(record.prefix, "output", original)
        core.clear()
        adapter.clear_context()
        cursor.clear()
