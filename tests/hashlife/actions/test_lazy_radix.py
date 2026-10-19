from random import Random
from typing import cast

import pytest

from number_compiler.api.number_api import PoweredCollatzTermPayload
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.projection.lazy_radix import RadixProjection, collatz_radix_digit
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from tests.support.performance_assertions import performance_bound
from tests.support.reference_arithmetic import collatz_literal as _collatz


@pytest.mark.validation  # Complete 12-source, four-radix point matrix.
def test_nonbinary_public_point_queries_never_lower_binary_endpoints(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("radix point query materialized an endpoint")

    monkeypatch.setattr(PoweredCollatzTerm, "digits", forbidden)
    monkeypatch.setattr(PoweredCollatzTerm, "iter_digits", forbidden)
    monkeypatch.setattr(PoweredCollatzTerm, "materialize", forbidden)
    rng = Random(522)
    for _ in range(12):
        seed, steps = rng.randrange(1, 1 << 20), rng.randrange(65)
        expected = _collatz(seed, steps)
        term = PoweredCollatzTerm(seed, steps)
        for radix in (3, 6, 10, 36):
            payload = PoweredCollatzTermPayload(term, radix)
            digits = digits_lsd(expected, radix)
            with performance_bound(
                35, f"radix {radix} point matrix for seed {seed}, steps {steps}"
            ):
                assert tuple(payload.digit(i) for i in range(len(digits))) == tuple(
                    digits
                )
                with pytest.raises(IndexError):
                    payload.digit(len(digits))
                with pytest.raises(IndexError):
                    payload.digit(1 << 100)
            metrics = payload.term.metrics()
            assert metrics.explicitly_materialized_endpoints == 0
            audit = collect_ledger_metrics(payload.term.resource_ledger)
            assert audit.forbidden_future_payloads == 0
            assert audit.resource_audit_complete == 1
            assert metrics.resource_accounting_mismatch == 0
            assert metrics.maximum_arithmetic_bits <= 64


def test_radix_microblocks_are_one_capped_index_owned_leaf_cache() -> None:
    term = PoweredCollatzTerm(140137, 11)
    expected = _collatz(term.seed, term.steps)
    digits = digits_lsd(expected, 3)
    projection = RadixProjection(3, term.width(), term.resource_ledger)
    assert projection._microblocks is term._microblocks
    assert tuple(projection.digit(term, i) for i in range(len(digits))) == tuple(digits)
    cache = term._microblocks
    assert len(cache) <= cache.MAX_ENTRIES
    assert cache.payload_bytes <= cache.MAX_PAYLOAD_BYTES
    assert all(block.bit_count <= 64 for block in cache.blocks.values())
    assert not any(
        hasattr(projection, name)
        for name in ("_point", "_range", "_evaluate", "_programs", "_ranges")
    )
    term.metrics()
    audit = collect_ledger_metrics(term.resource_ledger)
    assert audit.resource_audit_complete == 1
    assert audit.forbidden_future_payloads == 0


def test_radix_registry_reuses_projection_and_microblocks_without_replay_state() -> (
    None
):
    term = PoweredCollatzTerm(12345, 7)
    expected = _collatz(term.seed, term.steps) % 3
    assert collatz_radix_digit(term, 3, 0) == expected
    projection = term._radix_projections[3]
    entries = term.resource_ledger.snapshot().entries
    assert collatz_radix_digit(term, 3, 0) == expected
    assert term._radix_projections[3] is projection
    assert projection._microblocks is term._microblocks
    assert term.resource_ledger.snapshot().entries == entries
    term.resource_ledger.evict_query_memos()
    assert not projection._fused_actions
    assert collatz_radix_digit(term, 3, 0) == expected
    assert term.metrics().retained_cache_accounting_delta == 0


def test_wide_radix_point_fails_before_registry_growth_but_explicit_digits_work() -> (
    None
):
    from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError

    term = PoweredCollatzTerm(27, 1)
    entries = term.resource_ledger.snapshot().entries
    with pytest.raises(UnsupportedInterfaceError, match="2\\*\\*63"):
        collatz_radix_digit(term, (1 << 63) + 1, 0)
    assert term.resource_ledger.snapshot().entries == entries
    assert term._radix_projections == {}
    assert tuple(PoweredCollatzTermPayload(term, 1 << 100).digits()) == (82,)


def test_radix_block_arithmetic_tracks_exact_operand_width() -> None:
    radix = (1 << 63) - 25
    seed, steps = (1 << 70) + 0x12345, 11
    expected = _collatz(seed, steps)
    term = PoweredCollatzTerm(seed, steps)
    projection = RadixProjection(radix, term.width(), term.resource_ledger)
    digits = digits_lsd(expected, radix)
    assert tuple(
        projection.digit(term, index) for index in range(len(digits))
    ) == tuple(digits)
    with pytest.raises(IndexError):
        projection.digit(term, len(digits))
    assert term.resource_ledger.counters["collatz_image_projection_operand_bits"] > 64
    assert term._microblocks.payload_bytes <= term._microblocks.MAX_PAYLOAD_BYTES


def test_projection_constructor_rejects_invalid_dimensions_before_registration() -> (
    None
):
    ledger = ResourceLedger()
    before = ledger.snapshot()
    for radix, width in ((True, 3), (3.0, 3), (3, True), (3, 3.0)):
        with pytest.raises(TypeError, match="exact integers"):
            RadixProjection(cast("int", radix), cast("int", width), ledger)
        assert ledger.snapshot() == before
    from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError

    with pytest.raises(UnsupportedInterfaceError):
        RadixProjection(1, 3, ledger)
    assert ledger.snapshot() == before
    for width in (0, -1):
        with pytest.raises(ValueError):
            RadixProjection(3, width, ledger)
        assert ledger.snapshot() == before
