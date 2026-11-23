"""The carry-only restart gives the literal output after subsequent physical ticks."""

from collections.abc import Callable

import pytest

from number_compiler.sequences.reverse_add.q19_broadword_publisher import PackedQ19
from number_compiler.sequences.reverse_add.q19_carry_window import physical_carry_image


@pytest.mark.parametrize("seed", (0, 5, 95, 104, 196, 1000, 9999))
def test_source_window_handoff(seed: int) -> None:
    source = PackedQ19.from_digits(tuple(map(int, reversed(str(seed)))))
    current = seed
    for _ in range(12):
        current += int(str(current)[::-1])
    state = physical_carry_image(source)
    assert state == PackedQ19.from_digits(tuple(map(int, reversed(str(current)))))
    for _ in range(4):
        current += int(str(current)[::-1])
        state, emitted = state.advance(emit_digits=True)
        assert emitted == tuple(map(int, reversed(str(current))))


def test_parent_hit_bypasses_children_and_physical_steps(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.process_cache import (
        ProcessCache,
        temporary_process_cache,
    )
    from number_compiler.sequences.reverse_add import q19_event_spans as spans

    left, right = (
        physical_carry_image(PackedQ19.from_digits(seed))
        for seed in ((5, 9), (4, 0, 1))
    )
    assert left == right
    with temporary_process_cache(ProcessCache()):
        result = spans.earliest_palindrome(left, 71, shared_cache=False)
        assert spans.earliest_palindrome(left, 71, shared_cache=True) == result

        def forbid(*_args: object, **_kwargs: object) -> None:
            pytest.fail("completed parent rediscovered a child")

        monkeypatch.setattr(spans, "scan_palindrome_span", forbid)
        assert spans.earliest_palindrome(right, 71, shared_cache=True) == result


@pytest.mark.parametrize(
    "seed,horizon", ((196, 257), (89, 24), (89, 23), (216, 65), (480, 65))
)
def test_first_hit_agrees_with_literal_source(seed: int, horizon: int) -> None:
    from number_compiler.sequences.reverse_add.q19_event_spans import (
        earliest_palindrome,
    )

    current = seed
    expected = None
    for step in range(1, horizon + 1):
        current += int(str(current)[::-1])
        if str(current) == str(current)[::-1]:
            expected = step
            break
    source = PackedQ19.from_digits(tuple(map(int, reversed(str(seed)))))
    assert earliest_palindrome(source, horizon, shared_cache=True) == expected


def test_scan_avoids_output_rows_and_hit_successor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.reverse_add.q19_event_spans import (
        scan_palindrome_span,
    )

    advance = PackedQ19.advance
    transitions = 0

    def checked_advance(
        self: PackedQ19, *, emit_digits: bool = False
    ) -> tuple[PackedQ19, tuple[int, ...] | None]:
        nonlocal transitions
        assert not emit_digits
        transitions += 1
        return advance(self, emit_digits=emit_digits)

    monkeypatch.setattr(PackedQ19, "advance", checked_advance)
    hit = PackedQ19.from_digits((2, 9))
    assert scan_palindrome_span(hit, 1) == 1
    assert transitions == 0
    initial = PackedQ19.from_digits((6, 9, 1))
    result = scan_palindrome_span(initial, 12)
    assert isinstance(result, PackedQ19)
    assert transitions == 12
    assert result == PackedQ19.from_digits(
        tuple(map(int, reversed(str(196))))
    ).advance_repeated(12)


def test_owner_publishes_carry_continuation_and_reuses_completed_root(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add import q19_carry_window
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )
    from tests.support.reference_arithmetic import literal_reverse_add_digits

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, (6, 9, 1), base=10)
    try:
        actual = owner.publish_carry_window_continuation(48)
        assert tuple(owner.iter_digits(actual)) == literal_reverse_add_digits(196, 48)

        def forbid(*_args: object) -> None:
            pytest.fail("completed Q19 occurrence refolded its carry rows")

        monkeypatch.setattr(q19_carry_window, "physical_carry_image", forbid)
        assert owner.publish_carry_window_continuation(48) is actual
        assert owner.publish_broadword_source(48) is actual
    finally:
        owner.dispose()
    assert ledger.nodes == ledger.entries == 0


def test_owner_resumes_largest_issued_q19_frontier(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )
    from tests.support.reference_arithmetic import literal_reverse_add_digits

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, (6, 9, 1), base=10)
    try:
        first = owner.publish_broadword_source(32)
        assert tuple(owner.iter_digits(first)) == literal_reverse_add_digits(196, 32)

        def reject_source(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("issued Q19 frontier reopened the source")

        with monkeypatch.context() as patch:
            patch.setattr(PackedQ19, "from_digits", reject_source)
            later = owner.publish_broadword_source(48)
        assert tuple(owner.iter_digits(later)) == literal_reverse_add_digits(196, 48)

        earlier = owner.publish_broadword_source(24)
        assert tuple(owner.iter_digits(earlier)) == literal_reverse_add_digits(196, 24)
        with monkeypatch.context() as patch:
            patch.setattr(PackedQ19, "from_digits", reject_source)
            final = owner.publish_broadword_source(56)
        assert tuple(owner.iter_digits(final)) == literal_reverse_add_digits(196, 56)
    finally:
        owner.dispose()
    assert ledger.nodes == ledger.entries == 0


def test_owner_uses_nearest_earlier_q19_frontier(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )
    from tests.support.reference_arithmetic import literal_reverse_add_digits

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, (6, 9, 1), base=10)
    advance = PackedQ19.advance_repeated
    work: list[int] = []

    def count(
        self: PackedQ19,
        steps: int,
        *,
        before_step: Callable[[int, int], None] | None = None,
    ) -> PackedQ19:
        work.append(steps)
        return advance(self, steps, before_step=before_step)

    try:
        owner.publish_broadword_source(40)
        owner.publish_broadword_source(55)
        owner.publish_broadword_source(80)
        issued = owner.issued_occurrence

        def with_reclaimed(key: tuple[int, int]) -> object:
            return None if key[1] == 55 else issued(key)

        with monkeypatch.context() as patch:
            patch.setattr(owner, "issued_occurrence", with_reclaimed)
            patch.setattr(PackedQ19, "advance_repeated", count)
            result = owner.publish_broadword_source(60)
        assert sum(work) == 20
        assert tuple(owner.iter_digits(result)) == literal_reverse_add_digits(196, 60)
    finally:
        owner.dispose()
    assert ledger.nodes == ledger.entries == 0


def test_guarded_owner_resumes_only_a_guarded_frontier(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add import q19_carry_window
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )
    from tests.support.reference_arithmetic import literal_reverse_add_digits

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, (6, 9, 1), base=10)
    advance = PackedQ19.advance_repeated
    work: list[int] = []

    def count(
        self: PackedQ19,
        steps: int,
        *,
        before_step: Callable[[int, int], None] | None = None,
    ) -> PackedQ19:
        work.append(steps)
        return advance(self, steps, before_step=before_step)

    try:
        owner.publish_carry_window_continuation(40)
        owner.publish_broadword_source(48)
        from number_compiler.resources.metric_keys.reverse_add import (
            REVERSE_Q19_REUSED_CONTINUATION_STEPS,
        )

        before_reused = ledger.counters.get(REVERSE_Q19_REUSED_CONTINUATION_STEPS, 0)

        def reject_h12(
            _source: PackedQ19,
            _before_step: Callable[[int, int], None] | None = None,
        ) -> PackedQ19:
            raise AssertionError("H12 prefix replayed")

        with monkeypatch.context() as patch:
            patch.setattr(PackedQ19, "advance_repeated", count)
            patch.setattr(
                q19_carry_window,
                "physical_carry_image",
                reject_h12,
            )
            result = owner.publish_carry_window_continuation(60)
        assert sum(work) == 20
        assert (
            ledger.counters[REVERSE_Q19_REUSED_CONTINUATION_STEPS] - before_reused == 39
        )
        assert tuple(owner.iter_digits(result)) == literal_reverse_add_digits(196, 60)
    finally:
        owner.dispose()
    assert ledger.nodes == ledger.entries == 0


def test_distinct_cli_sources_consume_same_completed_q19_future(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    from number_compiler.api.cli import main
    from number_compiler.resources.process_cache import (
        ProcessCache,
        temporary_process_cache,
    )

    horizon = 1024
    expected = 104
    for _ in range(horizon):
        expected += int(str(expected)[::-1])
    with temporary_process_cache(ProcessCache()):
        assert main(["reverse-add", "--seed", "95", "--nth", str(horizon)]) == 0
        capsys.readouterr()

        advance = PackedQ19.advance_repeated
        segments: list[int] = []

        def prefix_only(
            self: PackedQ19,
            steps: int,
            *,
            before_step: Callable[[int, int], None] | None = None,
        ) -> PackedQ19:
            assert steps == 12, "the receiving issuer replayed the H12 continuation"
            segments.append(steps)
            return advance(self, steps, before_step=before_step)

        with monkeypatch.context() as patch:
            patch.setattr(PackedQ19, "advance_repeated", prefix_only)
            assert main(["reverse-add", "--seed", "104", "--nth", str(horizon)]) == 0
        assert segments == [12]
        assert capsys.readouterr().out.strip() == str(expected)
        assert (
            main(
                ["reverse-add", "--seed", "104", "--nth", str(horizon)],
                shared_cache=False,
            )
            == 0
        )
        assert capsys.readouterr().out.strip() == str(expected)


@pytest.mark.parametrize("carry_window", (False, True))
def test_failed_consumer_leaves_no_completed_future(carry_window: bool) -> None:
    from number_compiler.resources.process_cache import (
        ProcessCache,
        temporary_process_cache,
    )
    from number_compiler.sequences.reverse_add.q19_carry_window import (
        completed_continuation,
    )

    frame = PackedQ19.from_digits((4, 0, 1))

    def account(_n: int, _rounds: int) -> None:
        pass

    with temporary_process_cache(ProcessCache()):
        with pytest.raises(RuntimeError, match="cancelled"):
            with completed_continuation(
                frame,
                20,
                shared_cache=True,
                before_step=account,
                carry_window=carry_window,
            ):
                raise RuntimeError("cancelled consumer")
        with completed_continuation(
            frame, 20, shared_cache=True, before_step=account, carry_window=carry_window
        ) as (_, reused):
            assert not reused


def test_history_image_shared_across_horizons_and_sources(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.process_cache import (
        ProcessCache,
        temporary_process_cache,
    )
    from number_compiler.sequences.reverse_add.q19_carry_window import (
        completed_continuation,
    )

    def forbid_ports(*_args: object, **_kwargs: object) -> None:
        pytest.fail("the packed continuation reconstructed a physical carry history")

    monkeypatch.setattr(PackedQ19, "advance_with_ports", forbid_ports)
    counts: list[int] = []

    def account(count: int, _rounds: int) -> None:
        counts.append(count)

    cache = ProcessCache()
    with temporary_process_cache(cache):
        for seed, span, work in (
            (95, 30, 30),
            (104, 30, 12),
            (104, 34, 4),
            (95, 34, 0),
        ):
            source = PackedQ19.from_digits(tuple(map(int, reversed(str(seed)))))
            counts.clear()
            with completed_continuation(
                source, span, before_step=account, carry_window=True, shared_cache=True
            ) as (result, reused):
                exact = seed
                for _ in range(span):
                    exact += int(str(exact)[::-1])
                assert result == PackedQ19.from_digits(
                    tuple(map(int, reversed(str(exact))))
                )
                assert reused == span - work
                assert len(counts) == work
        # Source bindings share a continuation and its dyadic checkpoints.
        assert cache.stats().entries >= 3


def test_out_of_order_horizon_uses_earlier_dyadic_checkpoint() -> None:
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.resources.process_cache import (
        ProcessCache,
        temporary_process_cache,
    )
    from number_compiler.sequences.reverse_add.q19_carry_window import (
        completed_continuation,
    )

    source = PackedQ19.from_digits((5, 9))
    ledger = ResourceLedger()
    owner = ledger.register("q19-checkpoints", "scratch")
    work: list[int] = []

    def account(count: int, _rounds: int) -> None:
        work.append(count)

    with temporary_process_cache(ProcessCache()):
        with completed_continuation(
            source,
            80,
            shared_cache=True,
            carry_window=True,
            before_step=account,
            ledger=ledger,
            scratch_owner=owner,
        ):
            pass
        work.clear()
        with completed_continuation(
            source,
            50,
            shared_cache=True,
            carry_window=True,
            before_step=account,
            ledger=ledger,
            scratch_owner=owner,
        ) as (result, reused):
            exact = 95
            for _ in range(50):
                exact += int(str(exact)[::-1])
            assert result == PackedQ19.from_digits(
                tuple(map(int, reversed(str(exact))))
            )
            assert reused == 44
            assert len(work) == 6
    assert ledger.account_usage(owner) == (0, 0)
    ledger.mark_disposed(owner)


def test_checkpoint_reservation_failure_publishes_nothing() -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.resources.process_cache import (
        ProcessCache,
        temporary_process_cache,
    )
    from number_compiler.sequences.reverse_add.q19_carry_window import (
        completed_continuation,
    )

    source = PackedQ19.from_digits((5, 9))
    ledger = ResourceLedger(max_nodes=0)
    owner = ledger.register("q19-checkpoints", "scratch")
    cache = ProcessCache()
    try:
        with temporary_process_cache(cache):
            with pytest.raises(BlockContextBudgetExceeded):
                with completed_continuation(
                    source,
                    80,
                    shared_cache=True,
                    carry_window=True,
                    before_step=lambda _count, _rounds: None,
                    ledger=ledger,
                    scratch_owner=owner,
                ):
                    pytest.fail("unreserved checkpoint was published")
            assert cache.stats().entries == 0
            assert ledger.account_usage(owner) == (0, 0)
    finally:
        ledger.mark_disposed(owner)


def test_frontier_does_not_publish_cancelled_suffix() -> None:
    from number_compiler.resources.process_cache import (
        ProcessCache,
        temporary_process_cache,
    )
    from number_compiler.sequences.reverse_add.q19_carry_window import (
        completed_continuation,
    )

    frame = PackedQ19.from_digits((5, 9))
    work: list[int] = []

    def account(count: int, _rounds: int) -> None:
        work.append(count)

    with temporary_process_cache(ProcessCache()):
        with completed_continuation(
            frame, 20, shared_cache=True, carry_window=True, before_step=account
        ):
            pass
        with pytest.raises(RuntimeError, match="cancelled"):
            with completed_continuation(
                frame, 30, shared_cache=True, carry_window=True, before_step=account
            ):
                raise RuntimeError("cancelled")
        work.clear()
        with completed_continuation(
            frame, 30, shared_cache=True, carry_window=True, before_step=account
        ) as (_, reused):
            assert reused == 20
            assert len(work) == 10
        work.clear()
        with completed_continuation(
            frame, 16, shared_cache=True, carry_window=True, before_step=account
        ) as (_, reused):
            assert reused == 12
            assert len(work) == 4


def test_nested_frontier_publication_keeps_the_longer_completed_action() -> None:
    from number_compiler.resources.process_cache import (
        ProcessCache,
        temporary_process_cache,
    )
    from number_compiler.sequences.reverse_add.q19_carry_window import (
        completed_continuation,
    )

    frame = PackedQ19.from_digits((5, 9))
    work: list[int] = []

    def account(count: int, _rounds: int) -> None:
        work.append(count)

    with temporary_process_cache(ProcessCache()):
        with completed_continuation(
            frame, 30, shared_cache=True, carry_window=True, before_step=account
        ):
            with completed_continuation(
                frame, 40, shared_cache=True, carry_window=True, before_step=account
            ):
                pass
        work.clear()
        with completed_continuation(
            frame, 50, shared_cache=True, carry_window=True, before_step=account
        ) as (_, reused):
            assert reused == 40
            assert len(work) == 10


def test_frontier_reset_does_not_reuse_a_stale_image() -> None:
    from number_compiler.resources.process_cache import (
        ProcessCache,
        temporary_process_cache,
    )
    from number_compiler.sequences.reverse_add.q19_carry_window import (
        completed_continuation,
    )

    frame = PackedQ19.from_digits((5, 9))
    work: list[int] = []

    def account(count: int, _rounds: int) -> None:
        work.append(count)

    cache = ProcessCache()
    with temporary_process_cache(cache):
        for expected_reuse in (0, 30):
            work.clear()
            with completed_continuation(
                frame, 30, shared_cache=True, carry_window=True, before_step=account
            ) as (_, reused):
                assert reused == expected_reuse
                assert len(work) == 30 - expected_reuse
        cache.reset()
        work.clear()
        with completed_continuation(
            frame, 30, shared_cache=True, carry_window=True, before_step=account
        ) as (_, reused):
            assert reused == 0
            assert len(work) == 30
