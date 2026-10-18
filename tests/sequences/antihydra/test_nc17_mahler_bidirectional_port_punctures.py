"""Source-issued low/center/high ports constrain Mahler matrix fibers."""

from __future__ import annotations

from dataclasses import replace
from itertools import pairwise
from random import Random
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.sequences.antihydra.mahler_center_depth_matrix import (
    MahlerCenterBooleanMatrix,
    MahlerCertifiedCenterDepthTransfer,
)
from number_compiler.sequences.antihydra.mahler_center_exterior_join import (
    MahlerCenterExteriorEvidence,
    MahlerCenterExteriorJoin,
    MahlerExteriorMotif,
)
from number_compiler.sequences.antihydra.mahler_low_border_carry import (
    MahlerBorderCarryMap,
    MahlerLowBorderCarryCertificate,
    MahlerRadix4TwoTickCarry,
)
from number_compiler.sequences.antihydra.mahler_port_puncture import (
    MahlerCenterPortPuncture,
)


def _successor(source: int) -> int:
    return (3 * source + (source & 1)) // 2


def test_exterior_join_guards_numeric_source_before_decimal_conversion() -> None:
    oversized = 10**5000
    with pytest.raises(BlockContextBudgetExceeded, match="256-digit"):
        MahlerCenterExteriorJoin.from_source(oversized)


def test_spatial_low_action_matches_literal_three_port_carry() -> None:
    for radix, multiplier in ((10, 3), (4, 9)):
        for digits in range(5):
            modulus = radix**digits
            for value in range(min(modulus, 35)):
                action = MahlerBorderCarryMap.from_block(radix, value, digits)
                assert action.responses == tuple(
                    (multiplier * value + carry) // modulus
                    for carry in range(multiplier)
                )
                assert action.digits == digits

    action = MahlerBorderCarryMap.from_spatial_motif(10, "64646", 512)
    assert action.digits == 5 * 512
    assert action.responses == tuple(
        (3 * int("64646" * 512) + carry) // 10 ** (5 * 512) for carry in range(3)
    )


def test_radix4_nine_port_stays_on_the_two_physical_step_identity() -> None:
    for source in (7, 64646, 705700, 1234567):
        port = MahlerRadix4TwoTickCarry.from_source(source, digits=6)
        assert port.incoming_carry == (0, 3, 5, 8)[source % 4]
        assert port.high_after_two == _successor(_successor(source)) // 4**6
        assert port.packet()["scope"] == "certified radix-4 two-step spatial re-entry"


def test_declared_bilateral_punctures_reconstruct_each_candidate_source() -> None:
    rng = Random(271828)
    for _ in range(40):
        source = rng.randrange(100000, 10**13)
        start = (len(str(source)) - 2) // 2
        join = MahlerCenterExteriorJoin.from_source(
            source, center_places=2, center_start=start
        )
        for candidate in join.candidates:
            port = MahlerCenterPortPuncture.from_exterior(join, candidate.center)
            expected_source = (
                source + (candidate.center - join.pointed_center) * 10**start
            )
            assert port.source == expected_source
            assert port.next_source == _successor(expected_source)
            assert port.fixed_next_center == candidate.next_fixed_center
            assert port.center_upper_carry == candidate.upper_tripling_carry_out
            assert port.upper_division_inlet == candidate.upper_division_inlet
            assert port.lower_carry == candidate.lower_carry_in
            assert tuple(p.start for p in port.punctures) == (
                0,
                start,
                start + 1,
                start + 2,
            )
            assert port.punctures[-1].carry_out == port.top_carry
            for seam in port.punctures:
                assert seam.carry_responses[seam.carry_in] == seam.carry_out
                assert seam.carry_out in (0, 1, 2)
                assert seam.division_in in (0, 1)
                assert seam.division_out in (0, 1)
            for lower, higher in pairwise(port.punctures):
                assert lower.carry_out == higher.carry_in
                assert lower.division_in == higher.division_out


def test_100007_and_109907_aliases_keep_distinct_source_ports_and_rows() -> None:
    join = MahlerCenterExteriorJoin.from_source(100007, center_places=2)
    assert tuple(candidate.center for candidate in join.candidates) == (0, 99)
    left = MahlerCenterPortPuncture.from_exterior(join, 0)
    right = MahlerCenterPortPuncture.from_exterior(join, 99)

    assert (left.source, right.source) == (100007, 109907)
    assert left.source % 99 == right.source % 99
    assert left.source % 198 == right.source % 198
    assert left.lower_carry == right.lower_carry == 0
    assert (left.center_upper_carry, right.center_upper_carry) == (0, 2)
    assert left.punctures[0].division_in != right.punctures[0].division_in
    assert (left.next_source, right.next_source) == (150011, 164861)

    matrix = MahlerCenterBooleanMatrix.from_exterior(join, admitted_only=False)
    assert matrix.destinations(0) == (left.fixed_next_center,)
    assert matrix.destinations(99) == (right.fixed_next_center,)
    packet = MahlerCertifiedCenterDepthTransfer.from_source(100007, 2).packet()
    assert packet["punctured_port_constraints_active"] is True
    frame_counts = cast(tuple[int, ...], packet["punctured_source_frame_counts"])
    separations = cast(
        tuple[tuple[dict[str, object], ...], ...],
        packet["first_separating_port_punctures"],
    )
    assert frame_counts[0] == 2
    assert separations[0]


def test_compressed_source_motif_carry_is_reused_at_the_center() -> None:
    motif = "64646"
    copies = 4
    low = int(motif * copies)
    width = len(motif) * copies
    source = low + 99 * 10**width + 37 * 10 ** (width + 2)
    join = MahlerCenterExteriorJoin.from_source(
        source,
        center_places=2,
        center_start=width,
        exterior=(
            MahlerExteriorMotif(0, motif, copies),
            MahlerExteriorMotif(width + 2, "37"),
        ),
    )
    low_border = MahlerLowBorderCarryCertificate.from_exterior(join)
    port = MahlerCenterPortPuncture.from_exterior(join, 99)
    assert low_border.carry_map.responses == port.punctures[0].carry_responses
    assert port.punctures[0].width == width
    assert port.next_source == _successor(port.source)


def test_667000_width_birth_uses_authenticated_next_center_position() -> None:
    trace = MahlerCertifiedCenterDepthTransfer.from_source(667000, 1)
    packet = trace.packet()
    assert trace.pointed_sources == (667000, 1000500)
    assert trace.width_births == (1,)
    assert trace.center_positions == (2, 2)
    assert packet["punctured_port_constraints_active"] is True
    puncture_frames = cast(
        tuple[tuple[dict[str, object], ...], ...],
        packet["source_certified_bidirectional_port_punctures"],
    )
    first_frame = puncture_frames[0]
    pointed = next(item for item in first_frame if item["source_center"] == 70)
    assert pointed["next_fixed_center"] == 5


def test_mutated_join_and_cancelled_port_witnesses_are_rejected(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    join = MahlerCenterExteriorJoin.from_source(100007, center_places=2)
    forged = replace(join, low_border_carry_map=MahlerBorderCarryMap.identity(10))
    with pytest.raises(ValueError, match="changed|issuance"):
        MahlerCenterBooleanMatrix.from_exterior(forged)

    original = MahlerCenterPortPuncture._from_verified_evidence

    def changed(
        cls: type[MahlerCenterPortPuncture],
        evidence: MahlerCenterExteriorEvidence,
        center: int,
    ) -> MahlerCenterPortPuncture:
        point = original(evidence, center)
        return replace(point, center_upper_carry=(point.center_upper_carry + 1) % 3)

    monkeypatch.setattr(
        MahlerCenterPortPuncture, "_from_verified_evidence", classmethod(changed)
    )
    with pytest.raises(ArithmeticError, match="port|carry"):
        MahlerCertifiedCenterDepthTransfer.from_source(100007, 1)


def test_issued_port_snapshot_rejects_post_construction_cancellation() -> None:
    trace = MahlerCertifiedCenterDepthTransfer.from_source(100007, 1)
    point = trace.source_port_punctures[0][0]
    object.__setattr__(point, "center_upper_carry", (point.center_upper_carry + 1) % 3)
    with pytest.raises(ValueError, match="source-issued"):
        trace.packet()

    join = MahlerCenterExteriorJoin.from_source(100007, center_places=2)
    certificate = MahlerLowBorderCarryCertificate.from_exterior(join)
    with pytest.raises(ValueError, match="source join"):
        MahlerLowBorderCarryCertificate(
            certificate.source,
            certificate.center_start,
            certificate.carry_map,
            certificate.actual_carry,
            certificate.motif_repetitions,
            certificate.compressed_motif_blocks,
        )


def test_join_authentication_tags_nested_candidate_integers() -> None:
    join = MahlerCenterExteriorJoin.from_source(100007, center_places=2)
    candidate_index = next(
        index
        for index, item in enumerate(join.candidates)
        if item.signed_center_changes
    )
    candidate = join.candidates[candidate_index]
    _bit, sign = candidate.signed_center_changes[0]
    forged_candidate = replace(
        candidate,
        signed_center_changes=((True, sign),) + candidate.signed_center_changes[1:],
    )
    forged_candidates = list(join.candidates)
    forged_candidates[candidate_index] = forged_candidate
    forged = replace(join, candidates=tuple(forged_candidates))
    with pytest.raises(TypeError, match="signed center changes"):
        MahlerCenterBooleanMatrix.from_exterior(forged)

    counter = candidate.tripling_counter
    object.__setattr__(counter, "next_carries", (True, counter.next_carries[1]))
    with pytest.raises(TypeError, match="counter rows"):
        MahlerCenterBooleanMatrix.from_exterior(join)


def test_matrix_reuses_one_checked_join_and_its_motif_carry_maps(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    join = MahlerCenterExteriorJoin.from_source(100007, center_places=2)
    original = MahlerCenterExteriorJoin.from_source
    calls = 0

    def counted(
        cls: type[MahlerCenterExteriorJoin],
        source: int,
        *,
        center_places: int | None = None,
        center_start: int | None = None,
        exterior: tuple[MahlerExteriorMotif, ...] | None = None,
    ) -> MahlerCenterExteriorJoin:
        nonlocal calls
        calls += 1
        return original(
            source,
            center_places=center_places,
            center_start=center_start,
            exterior=exterior,
        )

    monkeypatch.setattr(MahlerCenterExteriorJoin, "from_source", classmethod(counted))
    MahlerCenterBooleanMatrix.from_exterior(join, admitted_only=False)
    assert calls == 1
