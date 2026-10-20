"""Native C1 ternary normal form may retain only certified ORIGINAL digits."""

from functools import partial
from typing import Never, cast

import pytest

from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
    source_reads_only,
)
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.projection.lazy_radix import collatz_radix_digit
from number_compiler.projection.radix_original_source import (
    OriginalRadixArena,
    OriginalRadixSource,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from tests.support.assertions import assert_rejected_atomically
from tests.support.radix_projection import radix_projection


@pytest.mark.parametrize("radix", (3, 6, 12, 1 << 63))
def test_original_reencoding_is_bounded_and_exact(radix: int) -> None:
    value = (1 << 129) + 13
    authority = OriginalSourceConstruction(
        ExactSource(tuple((value >> bit) & 1 for bit in range(value.bit_length())), 2)
    )
    ledger = ResourceLedger()
    arena = OriginalRadixArena(ledger)
    source = source_reads_only(arena.encode)(authority, radix)
    assert (
        sum(digit * radix**position for position, digit in enumerate(source.digits))
        == value
    )
    assert ledger.counters["maximum_arithmetic_bits"] <= 64
    assert ledger.nodes == len(source.digits) + 1
    before = ledger.counters["original_radix_source_bit_reads"]
    assert arena.encode(authority, radix) is source
    assert ledger.counters["original_radix_source_bit_reads"] == before


def test_source_authority_and_foreign_encoding_admission() -> None:
    arena = OriginalRadixArena(ResourceLedger())
    authority = OriginalSourceConstruction(ExactSource((1, 0, 1), 2))
    original = arena.encode(authority, 3)
    before = arena.ledger.snapshot()
    for bad in (object(), lambda: authority):
        with pytest.raises(TypeError):
            arena.encode(cast("OriginalSourceConstruction", bad), 3)
    for radix in (True, 1, 1 << 64):
        with pytest.raises(ValueError):
            arena.encode(authority, radix)
    copied = OriginalRadixSource(authority, 3, original.digits)
    with pytest.raises(ValueError):
        arena.point(copied, 0)
    assert arena.ledger.snapshot() == before


def test_odd_ternary_normal_form_is_universal_and_never_forms_future_word(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError(
            "native normal form cannot replay physical points or lower"
        )

    for name in ("digit", "materialize", "digits", "iter_digits"):
        monkeypatch.setattr(PoweredCollatzTerm, name, forbidden)
    for seed in range(1, 64, 2):
        term = PoweredCollatzTerm(seed, 1)
        expected = 3 * seed + 1
        index = 0
        while expected:
            assert collatz_radix_digit(term, 3, index) == expected % 3
            expected //= 3
            index += 1
        with pytest.raises(IndexError):
            collatz_radix_digit(term, 3, index)
        arena = radix_projection(term, 3).native_source_arena
        assert arena is not None
        for encoding in arena.sources.values():
            assert (
                sum(
                    digit * 3**position
                    for position, digit in enumerate(encoding.digits)
                )
                == seed
            )


def test_budget_rejection_precedes_source_conversion() -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    authority = OriginalSourceConstruction(ExactSource((1, 0, 1), 2))
    arena = OriginalRadixArena(ResourceLedger(0, 0))
    assert_rejected_atomically(
        arena.ledger, lambda: arena.encode(authority, 3), BlockContextBudgetExceeded
    )
    assert not arena.sources


def test_affine_summary_budget_failure_publishes_no_partial_nodes() -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    authority = OriginalSourceConstruction(ExactSource((1, 0, 1), 2))
    ledger = ResourceLedger(max_nodes=4, max_cache_entries=32)
    arena = OriginalRadixArena(ledger)
    source = arena.encode(authority, 3)
    before = ledger.entries, ledger.nodes
    with pytest.raises(BlockContextBudgetExceeded):
        arena.affine_shifted_point(source, 1, 0, 2)
    assert (ledger.entries, ledger.nodes) == before
    assert not arena.audit_snapshot().shift_nodes
    assert not arena.audit_snapshot().carry_nodes
    assert not arena.audit_snapshot().affine_summaries


def test_affine_summary_numeric_aliases_reject_before_publication() -> None:
    authority = OriginalSourceConstruction(ExactSource((1, 0, 1), 2))
    arena = OriginalRadixArena(ResourceLedger())
    source = arena.encode(authority, 3)
    before = arena.ledger.snapshot()
    with pytest.raises(ValueError):
        arena.affine_shifted_point(source, 1, True, 2)
    with pytest.raises(ValueError):
        arena.affine_shifted_point(source, 1, 0, False)
    assert arena.ledger.snapshot() == before
    assert not arena.audit_snapshot().affine_summaries


@pytest.mark.parametrize("radix", (3, 6, 10, 12, 1 << 63))
def test_only_whole_original_encoding_is_retained_and_shifts_are_transient(
    radix: int,
) -> None:
    value = (1 << 129) + 93
    authority = OriginalSourceConstruction(
        ExactSource(tuple((value >> bit) & 1 for bit in range(value.bit_length())), 2)
    )
    arena = OriginalRadixArena(ResourceLedger())
    encoding = arena.encode(authority, radix)
    retained = arena.ledger.entries, arena.ledger.nodes
    for shift in (0, 1, 2, 31, 32, 61, 62):
        width = arena.shifted_width(encoding, shift)
        actual = sum(
            arena.shifted_point(encoding, shift, index) * radix**index
            for index in range(width)
        )
        assert actual == value >> shift
        with pytest.raises(IndexError):
            arena.shifted_point(encoding, shift, width)
        assert (arena.ledger.entries, arena.ledger.nodes) == retained
    assert len(arena.sources) == 1 and encoding.binary_start == 0
    before = arena.ledger.snapshot()
    for start in (True, 1.0, -1, 1, 2, 61, 129, 130, 131):
        with pytest.raises(ValueError, match="source coordinate zero"):
            arena.encode(authority, radix, binary_start=cast("int", start))
    copied = OriginalRadixSource(authority, radix, (1,), 129)
    with pytest.raises(ValueError):
        arena.point(copied, 0)
    assert arena.ledger.snapshot() == before


@pytest.mark.parametrize("steps", (0, 1, 2))
@pytest.mark.parametrize("radix", (3, 6, 12, 3 << 61))
def test_fixed_physical_kernel_source_views_all_phases(
    steps: int, radix: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("native kernel law cannot lower or replay binary points")

    for name in ("digit", "digits", "iter_digits", "materialize"):
        monkeypatch.setattr(PoweredCollatzTerm, name, forbidden)
    for seed in (*range(1, 41), 404987, (1 << 253) + 127):
        term = PoweredCollatzTerm(seed, steps)
        expected = seed
        for _ in range(steps):
            expected = 3 * expected + 1 if expected & 1 else expected // 2
        index = 0
        while expected:
            assert collatz_radix_digit(term, radix, index) == expected % radix
            expected //= radix
            index += 1
        with pytest.raises(IndexError):
            collatz_radix_digit(term, radix, index)
        projection = radix_projection(term, radix)
        assert not any(
            hasattr(projection, item) for item in ("_programs", "_ranges", "_transfers")
        )
        assert projection.fused_arena is None
        assert term.resource_ledger.counters.get("maximum_arithmetic_bits", 0) <= 64
        if projection.native_source_arena is not None:
            for encoding in projection.native_source_arena.sources.values():
                assert encoding.binary_start == 0
                assert (
                    sum(
                        digit * radix**position
                        for position, digit in enumerate(encoding.digits)
                    )
                    == seed
                )


def test_suffix_source_audit_rejects_geometry_alias() -> None:
    from number_compiler.projection.radix_original_source import OriginalRadixKey
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    term = PoweredCollatzTerm(404987, 2)
    assert collatz_radix_digit(term, 3, 3) == ((3 * 404987 + 1) // 2) // 27 % 3
    arena = radix_projection(term, 3).native_source_arena
    assert arena is not None
    assert collect_ledger_metrics(term.resource_ledger).forbidden_future_payloads == 0
    key, encoding = next(iter(arena.sources.items()))
    wrong = OriginalRadixKey(key.construction, key.radix, key.binary_start + 1)
    del arena.sources[key]
    arena.sources[wrong] = encoding
    before = term.resource_ledger.snapshot()
    assert collect_ledger_metrics(term.resource_ledger).forbidden_future_payloads > 0
    assert term.resource_ledger.snapshot() == before


@pytest.mark.parametrize("radix", (5, 7, 10, 36, (1 << 63) - 25))
def test_fixed_two_step_radix_uses_only_original_source_and_finite_carry(
    radix: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("fixed C² radix must not replay binary points or lower")

    for name in ("digit", "digits", "iter_digits", "materialize"):
        monkeypatch.setattr(PoweredCollatzTerm, name, forbidden)
    for seed in (1, 2, 3, 4, 5, 6, 27, 404987, (1 << 253) + 127):
        term = PoweredCollatzTerm(seed, 2)
        expected = 3 * seed + 1 if seed & 1 else seed // 2
        expected = 3 * expected + 1 if expected & 1 else expected // 2
        index = 0
        while expected:
            assert collatz_radix_digit(term, radix, index) == expected % radix
            expected //= radix
            index += 1
        with pytest.raises(IndexError):
            collatz_radix_digit(term, radix, index)
        projection = radix_projection(term, radix)
        assert not any(
            hasattr(projection, item) for item in ("_programs", "_ranges", "_transfers")
        )
        assert term.resource_ledger.counters.get("maximum_arithmetic_bits", 0) <= 64
        assert (
            collect_ledger_metrics(term.resource_ledger).forbidden_future_payloads == 0
        )


@pytest.mark.parametrize("radix", (2, 10, (1 << 63) - 25))
def test_affine_source_digits_reuse_hierarchical_three_carry_summaries(
    monkeypatch: pytest.MonkeyPatch,
    radix: int,
) -> None:
    seed = (1 << 127) + 27
    term = PoweredCollatzTerm(seed, 2)
    expected = (3 * seed + 1) // 2

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("affine observation rescanned shifted source digits")

    monkeypatch.setattr(OriginalRadixArena, "shifted_point", forbidden)
    monkeypatch.setattr(OriginalRadixArena, "shifted_width", forbidden)
    arena: OriginalRadixArena | None = None
    if radix == 2:
        binary_arena = OriginalRadixArena(term.resource_ledger)
        arena = binary_arena
        encoding = binary_arena.encode(term.original_source_construction, radix)

        def read_digit(coordinate: int) -> int:
            return binary_arena.affine_shifted_point(encoding, 1, coordinate, 2)

    else:

        def read_digit(coordinate: int) -> int:
            return collatz_radix_digit(term, radix, coordinate)

    digits: list[int] = []
    coordinate = 0
    while expected:
        digit = read_digit(coordinate)
        assert digit == expected % radix
        digits.append(digit)
        expected //= radix
        coordinate += 1
    with pytest.raises(IndexError):
        read_digit(coordinate)
    if radix != 2:
        projection = radix_projection(term, radix)
        native = projection.native_source_arena
        assert native is not None
        arena = native
    assert arena is not None and len(arena.audit_snapshot().affine_summaries) == 1
    summary = next(iter(arena.audit_snapshot().affine_summaries.values()))
    assert len(summary.shift_tree) == len(summary.carry_tree) == 2 * summary.size
    assert not hasattr(summary, "digits") and not hasattr(summary, "carries")
    encoding = next(iter(arena.sources.values()))
    assert term.resource_ledger.counters["radix_original_affine_carry_cells"] == len(
        encoding.digits
    )
    prefix_before = term.resource_ledger.counters.get(
        "original_affine_prefix_summary_visits", 0
    )
    shift_before = term.resource_ledger.counters.get(
        "original_affine_shift_summary_visits", 0
    )
    middle = len(digits) // 2
    assert read_digit(middle) == digits[middle]
    summary_visits = (
        term.resource_ledger.counters.get("original_affine_prefix_summary_visits", 0)
        - prefix_before
        + term.resource_ledger.counters.get("original_affine_shift_summary_visits", 0)
        - shift_before
    )
    assert summary_visits <= 2 * summary.size.bit_length()
    source_cells = term.resource_ledger.counters["original_affine_summary_source_cells"]
    for index, digit in enumerate(digits):
        assert read_digit(index) == digit
    assert (
        term.resource_ledger.counters["original_affine_summary_source_cells"]
        == source_cells
    )
    assert term.resource_ledger.counters["original_affine_summary_hits"] > 0
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    report = collect_ledger_metrics(term.resource_ledger)
    assert report.forbidden_future_payloads == 0
    assert report.resource_accounting_mismatch == 0


@pytest.mark.parametrize("radix", ((1 << 63), (1 << 63) - 25, 3 << 61, (1 << 32) + 1))
@pytest.mark.parametrize("shift", (1, 31, 32, 33, 62))
def test_fixed_limb_division_cell_never_forms_the_wide_product(
    radix: int, shift: int
) -> None:
    ledger = ResourceLedger()
    arena = OriginalRadixArena(ledger)
    for carry in (0, 1, (1 << shift) - 1):
        for digit in (0, 1, radix - 1):
            quotient, remainder = arena.divide_cell(carry, radix, digit, shift)
            # Wide Python arithmetic is used only by this independent oracle.
            assert (quotient, remainder) == divmod(carry * radix + digit, 1 << shift)
    assert ledger.counters["maximum_arithmetic_bits"] <= 64
    assert ledger.counters.get("unbounded_arithmetic_observations", 0) == 0
    assert ledger.counters.get("original_radix_shift_product_buffer_limbs_peak", 0) <= 4
    assert ledger.counters.get("original_radix_shift_live_buffer_limbs_peak", 0) <= 10
    assert ledger.entries == ledger.nodes == 0


def test_transient_shift_zero_and_invalid_requests_preserve_the_encoding() -> None:
    authority = OriginalSourceConstruction(ExactSource((1,), 2))
    arena = OriginalRadixArena(ResourceLedger())
    encoding = arena.encode(authority, 12)
    assert arena.shifted_width(encoding, 62) == 1
    assert arena.shifted_point(encoding, 62, 0) == 0
    for shift in (True, 0.0, -1, 63):
        before = assert_rejected_atomically(
            arena.ledger,
            partial(arena.shifted_width, encoding, cast("int", shift)),
            ValueError,
        )
    before = arena.ledger.snapshot()
    foreign = OriginalRadixArena(ResourceLedger()).encode(authority, 12)
    with pytest.raises(ValueError):
        arena.shifted_point(foreign, 1, 0)
    with pytest.raises(ValueError):
        arena.shifted_point(encoding, 1, True)
    assert arena.ledger.snapshot() == before
    assert encoding.digits == (1,) and encoding.binary_start == 0


def test_all_shifted_queries_retain_only_the_complete_original_number() -> None:
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    seed = (1 << 253) + 127
    term = PoweredCollatzTerm(seed, 2)
    for radix in (3, 6, 12, 3 << 61, (1 << 63) - 25):
        expected = (3 * seed + 1) // 2
        index = 0
        while expected:
            assert collatz_radix_digit(term, radix, index) == expected % radix
            index += 1
            expected //= radix
        arena = radix_projection(term, radix).native_source_arena
        assert arena is not None
        assert len(arena.sources) == 1
        for key, encoding in arena.sources.items():
            assert key.binary_start == encoding.binary_start == 0
            assert (
                sum(digit * radix**i for i, digit in enumerate(encoding.digits)) == seed
            )
    report = collect_ledger_metrics(term.resource_ledger)
    assert report.forbidden_future_payloads == 0
    assert report.resource_accounting_mismatch == 0
