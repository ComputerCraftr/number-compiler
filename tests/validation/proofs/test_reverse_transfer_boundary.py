"""An exit action forgets its interior carry row, even for a short history."""

from __future__ import annotations

import sys
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from itertools import product
from types import FrameType
from typing import Never, cast

import pytest

from devtools.proofs import exact_oracle
from devtools.proofs.carry_action_quotient import CarryThresholdSignature
from devtools.proofs.carry_interval_effects import CarryActionQuotientArena
from devtools.proofs.lazy_reverse import LazyReverseApplication
from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaHandle,
    CarryBit,
    TransferSummaryID,
)
from number_compiler.arithmetic.fields.dyadic_tile import uniform
from number_compiler.arithmetic.functions.finite_port_action import (
    FinitePortActionArena,
    PortVariable,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def carry_history(word: Iterable[int], incoming: int = 0) -> tuple[int, ...]:
    history = []
    for coefficient in word:
        incoming = int(coefficient + incoming >= 10)
        history.append(incoming)
    return tuple(history)


def test_distinct_histories_have_the_same_extensional_action_without_a_row_inverse() -> (
    None
):
    arena = CarryActionQuotientArena()
    port = PortVariable(0, 0, "carry", 0)
    # Both words are valid symmetric reverse-pair sources, but their internal
    # carry rows differ. The shared summary therefore cannot invert either row.
    first = (2, 10, 4, 6, 6, 4, 10, 2)
    second = (4, 0, 6, 4, 4, 6, 0, 4)
    assert carry_history(first) != carry_history(second)
    a = arena.word(iter(first), base=10, port=port)
    b = arena.word(iter(second), base=10, port=port)
    assert a == b == arena.symbol(0, base=10, port=port)
    for incoming in (False, True):
        assert arena.apply(a, {port: incoming}) is False
    # Length is also absent from the extensional image.
    assert arena.word((0,), base=10, port=port) == a
    assert not hasattr(arena, "project_span")
    assert not hasattr(arena, "row_spans")
    report = collect_ledger_metrics(arena.ledger)
    assert report.forbidden_future_payloads == 0
    assert report.resource_audit_complete == 1


def test_production_disjoint_summaries_alias_different_carry_histories() -> None:
    application = LazyReverseApplication(10, 19, 7, (7, 18, 7))
    application.active_width()
    histories = {}
    value = 196
    for generation in range(8):
        digits = tuple(map(int, reversed(str(value))))
        pair = tuple(a + b for a, b in zip(digits, reversed(digits)))
        if generation == 7:
            histories[2] = carry_history(pair[:2])
            histories[6] = carry_history(pair[4:6])
        value += int(str(value)[::-1])
    summaries = {stop: application._range_action(7, stop) for stop in histories}
    assert histories[2] != histories[6]
    assert summaries[2] == summaries[6]
    assert summaries[2] is not None
    assert summaries[2].kind == "carry-interval-effect"
    assert all(key.stop >= 2 and key.stop % 2 == 0 for key in application._ranges)
    # Exact source+program remains reconstructible; only this shared boundary
    # function has no inverse to the two distinct interior output rows.


def test_all_disjoint_block_actions_together_still_forget_the_interior_row() -> None:
    arena = CarryActionQuotientArena()
    port = PortVariable(0, 0, "carry", 0)
    # Symmetric pair words for decimal sources 5554 and 5455. Even the complete
    # collection of disjoint two-cell effects is identical; emitted rows differ.
    first, second = (9, 10, 10, 9), (10, 9, 9, 10)
    assert carry_history(first) == (0, 1, 1, 1)
    assert carry_history(second) == (1, 1, 1, 1)
    left = tuple(
        arena.interval_word(first[start : start + 2], base=10, port=port)
        for start in (0, 2)
    )
    right = tuple(
        arena.interval_word(second[start : start + 2], base=10, port=port)
        for start in (0, 2)
    )
    assert left == right
    left_reverse = tuple(
        arena.word(reversed(first[start : start + 2]), base=10, port=port)
        for start in (0, 2)
    )
    right_reverse = tuple(
        arena.word(reversed(second[start : start + 2]), base=10, port=port)
        for start in (0, 2)
    )
    assert left_reverse == right_reverse
    assert tuple(
        sum(value != 9 for value in first[start : start + 2]) for start in (0, 2)
    ) == (1, 1)
    assert tuple(
        sum(value != 9 for value in second[start : start + 2]) for start in (0, 2)
    ) == (1, 1)
    for action in left:
        assert arena.interval_effect(action).reset_count == 1


def test_two_direction_pair_interface_has_five_classes_for_nine_histories() -> None:
    arena = CarryActionQuotientArena()
    port = PortVariable(0, 0, "carry", 0)
    images = {
        (arena.word((a, b), base=10, port=port), arena.word((b, a), base=10, port=port))
        for a in (0, 9, 10)
        for b in (0, 9, 10)
    }
    assert len(images) == 5


def test_complete_pair_interface_has_seven_canonical_ids_for_nine_histories() -> None:
    arena = CarryActionQuotientArena()
    port = PortVariable(0, 0, "carry", 0)
    images = set()
    for word in product((0, 9, 10), repeat=2):
        action = arena.interval_word(word, base=10, port=port)
        images.add(action)
        effect = arena.interval_effect(action)
        for incoming in (False, True):
            assert arena.apply(effect.forward, {port: incoming}) == bool(
                carry_history(word, incoming)[-1]
            )
            assert arena.apply(effect.backward, {port: incoming}) == bool(
                carry_history(reversed(word), incoming)[-1]
            )
        assert effect.reset_count == min(2, sum(value != 9 for value in word))
    assert len(images) == 7
    assert all(action.kind == "carry-interval-effect" for action in images)
    # This exhausts associativity of the finite SPATIAL interface. It does not
    # assert that equal images have equal arithmetic successors in time.
    for a, b, c in product(images, repeat=3):
        left = arena.compose_intervals(arena.compose_intervals(a, b, port), c, port)
        right = arena.compose_intervals(a, arena.compose_intervals(b, c, port), port)
        assert left == right
    assert collect_ledger_metrics(arena.ledger).forbidden_future_payloads == 0


def test_interval_ids_validate_owner_kind_and_bounds_before_warm_composition() -> None:
    first, other = CarryActionQuotientArena(), CarryActionQuotientArena()
    port = PortVariable(0, 0, "carry", 0)
    local = first.interval_word((9, 10), base=10, port=port)
    identity = first.interval_identity(port)
    assert first.compose_intervals(local, identity, port) == local
    invalid = (
        other.interval_word((9, 10), base=10, port=port),
        first.symbol(10, base=10, port=port),
        ArenaHandle(first.owner, "carry-interval-effect", local.local_id),
        TransferSummaryID(first.owner, "carry-interval-effect", 99999),
    )
    for action in invalid:
        before = first.ledger.snapshot()
        with pytest.raises((TypeError, ValueError)):
            first.interval_effect(cast("TransferSummaryID", action))
        with pytest.raises((TypeError, ValueError)):
            first.compose_intervals(cast("TransferSummaryID", action), identity, port)
        with pytest.raises((TypeError, ValueError)):
            first.compose_intervals(identity, cast("TransferSummaryID", action), port)
        with pytest.raises((TypeError, ValueError)):
            first.reflect_interval(cast("TransferSummaryID", action))
        after = first.ledger.snapshot()
        assert (after.entries, after.nodes, after.counters) == (
            before.entries,
            before.nodes,
            before.counters,
        )


@dataclass(frozen=True)
class RenamedWitness:
    payload: object


@dataclass(frozen=True)
class PackedCarryHistory:
    packed_history: int


@pytest.mark.parametrize(
    "encoding",
    (
        "threshold",
        "wrapped_threshold",
        "packed_cell",
        "packed_scalar",
        "bare_scalar",
        "renamed_list",
        "boolean_row",
    ),
)
def test_short_lossless_history_encodings_are_not_bounded_transfer_summaries(
    encoding: str,
) -> None:
    payload: object
    if encoding in ("threshold", "wrapped_threshold"):
        with exact_oracle():
            payload = CarryThresholdSignature.from_pair(
                (2, 10, 4, 6, 6, 4, 10, 2), base=10
            )
        assert payload.low_payload.bit_length() < 64
        if encoding == "wrapped_threshold":
            payload = RenamedWitness(payload)
    else:
        # Twenty carry bits plus twenty activity bits: a lossless H=20 cell.
        packed = (((1 << 20) - 1) << 20) | 0b101001101
        assert packed.bit_length() == 40
        if encoding == "packed_cell":
            payload = uniform(packed, 0)
        elif encoding == "bare_scalar":
            payload = packed
        elif encoding == "renamed_list":
            payload = RenamedWitness([packed])
        elif encoding == "boolean_row":
            payload = [bool((packed >> position) & 1) for position in range(20)]
        else:
            payload = PackedCarryHistory(packed)
    ledger = ResourceLedger()
    owner = ledger.register("claimed-boundary-function", "transfer_summary")
    stored: LedgerList[object]
    stored = ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    stored.append(payload)
    report = collect_ledger_metrics(ledger)
    assert report.forbidden_future_payloads > 0
    assert report.retained_unbounded_future_integers == 0


def test_source_role_cannot_admit_a_quarantined_proof_record() -> None:
    with exact_oracle():
        proof = CarryThresholdSignature.from_pair((2, 10, 4, 6, 6, 4, 10, 2), base=10)
    ledger = ResourceLedger()
    owner = ledger.register("mislabeled-source", "exact_source")
    stored: LedgerList[object]
    stored = ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    stored.append(RenamedWitness(proof))
    assert collect_ledger_metrics(ledger).forbidden_future_payloads > 0


def test_diamond_summary_ids_are_checked_against_their_actual_state_arena() -> None:
    from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
    from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
    from number_compiler.hashlife.observation.hashlife_projection import (
        HashLifeBlockIndex,
    )
    from number_compiler.hashlife.observation.tile_projection import LazyProjection
    from number_compiler.hashlife.tiles.tile_result_records import PoweredInterfaceKey
    from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect

    ledger = ResourceLedger()
    application = HashLifeBlockIndex(
        DigitNormalizeBlockEffect(10),
        (2,) * 20,
        logical_length=20,
        ledger=ledger,
    )
    assert application.direct_powered_point(10) == 2
    projection = application._lazy_application
    assert type(projection) is LazyProjection
    runtime = projection.scheduler.results
    assert runtime.retained_interfaces > 0
    assert collect_ledger_metrics(ledger).forbidden_future_payloads == 0
    key = next(key for key in runtime._memo if type(key) is PoweredInterfaceKey)
    runtime._memo[key] = LocalInterfaceID(
        ArenaToken("foreign-boundary"),
        "diamond-quotient",
        0,
    )
    # A typed range key alone does not turn an arbitrary packed scalar into an
    # arena ID; its result must resolve in this application's actual state list.
    assert collect_ledger_metrics(ledger).forbidden_future_payloads > 0


def test_public_reverse_point_and_width_cannot_use_oracle_packing_or_output_tapes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import devtools.proofs.carry_action_quotient as proof_carry
    import devtools.proofs.reverse_spacetime as proof_spacetime
    import devtools.proofs.temporal_quotient as proof_cut

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("production entered an exact history or output-tape path")

    monkeypatch.setattr(
        proof_spacetime.ReverseAddCausalSpacetimeEngine, "bootstrap_slab", forbidden
    )
    monkeypatch.setattr(proof_cut, "_pack_row", forbidden)
    monkeypatch.setattr(proof_cut.ReverseAddCarryCutState, "row_values", forbidden)
    monkeypatch.setattr(proof_carry.CarryActionQuotientArena, "project_span", forbidden)
    monkeypatch.setattr(
        proof_carry.CarryActionQuotientArena, "project_affine_span", forbidden
    )
    monkeypatch.setattr(FinitePortActionArena, "cut", forbidden)
    monkeypatch.setattr(ReverseAddPoweredTerm, "digits", forbidden)
    monkeypatch.setattr(ReverseAddPoweredTerm, "materialize", forbidden)
    term = ReverseAddPoweredTerm(196, 24)
    expected = 196
    for _ in range(24):
        expected += int(str(expected)[::-1])
    digits = str(expected)
    assert term.width() == len(digits)
    for position in (0, 3, len(digits) - 1):
        assert term.digit(position) == int(digits[-1 - position])
    assert term.metrics().forbidden_future_payloads == 0


def test_production_workspace_never_memoizes_a_complete_future_carry_row() -> None:
    """Inspect execution locals, since post-return ledger checks miss scratch tapes."""
    application = LazyReverseApplication(10, 19, 24, (7, 18, 7))
    witnessed: list[tuple[int, int]] = []

    def inspect(frame: FrameType, event: str, argument: object) -> None:
        if witnessed:
            return
        if (
            event != "return"
            or frame.f_globals.get("__name__") != "devtools.proofs.lazy_reverse"
        ):
            return
        for value in frame.f_locals.values():
            if not isinstance(value, Mapping) or len(value) < 8:
                continue
            # A folded scan may keep one cursor for each of two fixed edge
            # ports per stage. Coordinates are values, never additional keys.
            if all(
                type(key) is tuple
                and len(key) == 2
                and all(type(part) is int for part in key)
                and type(cursor) is tuple
                and len(cursor) == 2
                and all(type(part) is int for part in cursor)
                and cursor[1] in (0, 1)
                for key, cursor in value.items()
            ):
                assert all(key[1] in (0, 1) for key in value)
                assert len(value) <= 2 * application.horizon
            # A complete spatial row indexed by (generation, position) is a
            # lossless output tape regardless of the workspace variable's name.
            cells = {
                key: bit
                for key, bit in value.items()
                if type(key) is tuple
                and len(key) == 2
                and all(type(part) is int for part in key)
                and (
                    (type(bit) is int and bit in (0, 1))
                    or type(bit) is CarryBit
                    or type(bit) is TransferSummaryID
                )
            }
            for generation in {key[0] for key in cells}:
                if not 0 < generation < len(application._programs):
                    continue
                width = application._programs[generation].width
                if width >= 8 and all(
                    (generation, position) in cells for position in range(1, width + 1)
                ):
                    witnessed.append((generation, width))
                    return

    previous = sys.getprofile()
    sys.setprofile(inspect)
    try:
        application.active_width()
    finally:
        sys.setprofile(previous)
    assert not witnessed, (
        f"exact future carry row retained during evaluation: {witnessed[:1]}"
    )
