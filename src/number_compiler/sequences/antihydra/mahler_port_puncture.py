"""Source-bound bilateral carry/borrow ports at declared Mahler seams."""

from __future__ import annotations

from dataclasses import dataclass
from typing import cast

from number_compiler.sequences.antihydra.mahler_center_exterior_join import (
    MahlerCenterExteriorEvidence,
)
from number_compiler.sequences.antihydra.mahler_low_border_carry import (
    MahlerBorderCarryMap,
)


@dataclass(frozen=True, slots=True)
class MahlerCarryPortPuncture:
    """One exact source-authenticated spatial block seam."""

    start: int
    width: int
    kind: str
    carry_in: int
    carry_out: int
    division_in: int
    division_out: int
    carry_responses: tuple[int, int, int]

    def packet(self) -> dict[str, object]:
        return {
            "start": self.start,
            "width": self.width,
            "kind": self.kind,
            "tripling_carry_in": self.carry_in,
            "tripling_carry_out": self.carry_out,
            "upper_division_inlet": self.division_in,
            "lower_division_outlet": self.division_out,
            "three_context_carry_responses": self.carry_responses,
        }


@dataclass(frozen=True, slots=True)
class MahlerCenterPortPuncture:
    """Complete low/center/high port cone for one conditional center fiber."""

    source: int
    center: int
    fixed_next_center: int
    next_source: int
    lower_carry: int
    center_upper_carry: int
    upper_division_inlet: int
    top_carry: int
    punctures: tuple[MahlerCarryPortPuncture, ...]

    @classmethod
    def from_exterior(
        cls, join: object, candidate_center: int
    ) -> MahlerCenterPortPuncture:
        evidence = MahlerCenterExteriorEvidence.from_join(join)
        return cls.from_verified_evidence(evidence, candidate_center)

    @classmethod
    def from_verified_evidence(
        cls, evidence: MahlerCenterExteriorEvidence, candidate_center: int
    ) -> MahlerCenterPortPuncture:
        """Build from verified evidence checked by the enclosing producer."""
        if type(evidence) is not MahlerCenterExteriorEvidence:
            raise TypeError("port punctures require verified Mahler exterior evidence")
        issued = evidence.join
        if issued.center_places != 2:
            raise TypeError("bilateral port punctures require a two-digit center")
        if type(candidate_center) is not int or not 0 <= candidate_center < 100:
            raise ValueError("candidate center must be an exact decimal pair")
        item = next(
            (
                candidate
                for candidate in issued.candidates
                if candidate.center == candidate_center
            ),
            None,
        )
        if item is None:
            raise ValueError("center is absent from the exterior residue ring")

        start = issued.center_start
        base = 10**start
        source = (
            issued.authenticated_source
            + (candidate_center - issued.pointed_center) * base
        )
        if source <= 0 or (source & 1) != (issued.authenticated_source & 1):
            raise ValueError("candidate changes positivity or authenticated parity")

        segments: list[tuple[int, int, str, MahlerBorderCarryMap, int]] = []
        for span, action in zip(issued.exterior, evidence.span_carry_maps, strict=True):
            if span.start < start or span.start >= start + 2:
                value = (source // 10**span.start) % 10**span.width
                segments.append((span.start, span.width, "exterior", action, value))
        for position in (start, start + 1):
            digit = (candidate_center // 10 ** (position - start)) % 10
            segments.append(
                (position, 1, "center", MahlerBorderCarryMap.digit(10, digit), digit)
            )
        segments.sort(key=lambda segment: segment[0])
        if not segments or segments[0][0] != 0:
            raise ArithmeticError("missing low spatial carry seam")

        carry = source & 1
        cursor = 0
        forward: list[
            tuple[int, int, str, MahlerBorderCarryMap, int, int, int, int]
        ] = []
        for position, width, kind, action, value in segments:
            if position != cursor:
                raise ArithmeticError("gap in exterior/center port partition")
            modulus = 10**width
            carry_in = carry
            raw = (3 * value + carry_in) % modulus
            carry = action.outgoing(carry_in)
            if carry != (3 * value + carry_in) // modulus:
                raise ArithmeticError("spatial carry map disagrees with exact block")
            forward.append((position, width, kind, action, value, carry_in, carry, raw))
            cursor += width
        if cursor != issued.width:
            raise ArithmeticError("high exterior is not covered by source ports")

        top_carry = carry
        division_in = top_carry & 1
        next_source = (top_carry // 2) * 10**issued.width
        lower_carry = -1
        center_upper_carry = -1
        upper_division_inlet = -1
        punctures_reversed: list[MahlerCarryPortPuncture] = []
        for position, width, kind, action, _, carry_in, carry_out, raw in reversed(
            forward
        ):
            if position == start + 2:
                upper_division_inlet = raw & 1
            if position == start + 1:
                center_upper_carry = carry_out
            if position == start:
                lower_carry = carry_in
            next_source += (raw // 2 + (10**width // 2) * division_in) * 10**position
            punctures_reversed.append(
                MahlerCarryPortPuncture(
                    position,
                    width,
                    kind,
                    carry_in,
                    carry_out,
                    division_in,
                    raw & 1,
                    cast(tuple[int, int, int], action.responses),
                )
            )
            division_in = raw & 1
        punctures = tuple(reversed(punctures_reversed))

        if next_source != (3 * source + (source & 1)) // 2:
            raise ArithmeticError(
                "bilateral ports failed exact successor reconstruction"
            )
        if (
            lower_carry != item.lower_carry_in
            or center_upper_carry != item.upper_tripling_carry_out
            or upper_division_inlet != item.upper_division_inlet
            or (next_source // base) % 100 != item.next_fixed_center
            or (next_source % 99, next_source % 198)
            != (item.next_mod99, item.next_mod198)
        ):
            raise ArithmeticError("bilateral punctures disagree with harmonic join")
        return cls(
            source,
            candidate_center,
            item.next_fixed_center,
            next_source,
            lower_carry,
            center_upper_carry,
            upper_division_inlet,
            top_carry,
            punctures,
        )

    def packet(self) -> dict[str, object]:
        return {
            "source_center": self.center,
            "next_fixed_center": self.fixed_next_center,
            "lower_carry_into_center": self.lower_carry,
            "center_carry_into_upper": self.center_upper_carry,
            "upper_division_inlet": self.upper_division_inlet,
            "top_carry": self.top_carry,
            "punctures": tuple(puncture.packet() for puncture in self.punctures),
            "scope": "source-certified spatial seams; no unknown temporal driver",
        }


__all__ = ["MahlerCarryPortPuncture", "MahlerCenterPortPuncture"]
