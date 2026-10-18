"""Bounded spatial carry actions used by source-issued Mahler center views.

The radix-10 action owns the low-to-high tripling carry for one physical
Mahler step. The radix-4 action is a separate two-step spatial identity; its
power never certifies a repeated temporal input word.
"""

from __future__ import annotations

from dataclasses import dataclass, field

RADIX4_LOW_TRANSLATIONS = (0, 3, 5, 8)
MAX_SPATIAL_DIGITS = 4096
MAX_SPATIAL_REPETITIONS = 1 << 32
_LOW_BORDER_ISSUER = object()


@dataclass(frozen=True, slots=True)
class MahlerBorderCarryMap:
    """Incoming carry to outgoing carry action for a concrete LSD block."""

    radix: int
    multiplier: int
    digits: int
    responses: tuple[int, ...]

    def __post_init__(self) -> None:
        if (
            (self.radix, self.multiplier) not in ((10, 3), (4, 9))
            or type(self.digits) is not int
            or not 0 <= self.digits <= MAX_SPATIAL_DIGITS
            or type(self.responses) is not tuple
            or len(self.responses) != self.multiplier
            or any(
                type(value) is not int or not 0 <= value < self.multiplier
                for value in self.responses
            )
        ):
            raise ValueError("invalid Mahler spatial carry boundary map")

    @classmethod
    def identity(cls, radix: int) -> MahlerBorderCarryMap:
        multiplier = {10: 3, 4: 9}.get(radix)
        if type(radix) is not int or multiplier is None:
            raise ValueError("radix must be 4 or 10")
        return cls(radix, multiplier, 0, tuple(range(multiplier)))

    @classmethod
    def digit(cls, radix: int, digit: int) -> MahlerBorderCarryMap:
        if type(radix) is not int or radix not in (4, 10):
            raise ValueError("radix must be 4 or 10")
        if type(digit) is not int or not 0 <= digit < radix:
            raise ValueError("source digit is outside its radix")
        multiplier = 9 if radix == 4 else 3
        return cls(
            radix,
            multiplier,
            1,
            tuple((multiplier * digit + carry) // radix for carry in range(multiplier)),
        )

    @classmethod
    def from_block(cls, radix: int, value: int, digits: int) -> MahlerBorderCarryMap:
        """Construct all bounded responses without expanding a digit string."""
        if type(radix) is not int or radix not in (4, 10):
            raise ValueError("radix must be 4 or 10")
        if (
            type(digits) is not int
            or not 0 <= digits <= MAX_SPATIAL_DIGITS
            or type(value) is not int
            or value < 0
            or value >= radix**digits
        ):
            raise ValueError("invalid concrete carry block")
        multiplier = 9 if radix == 4 else 3
        modulus = radix**digits
        return cls(
            radix,
            multiplier,
            digits,
            tuple(
                (multiplier * value + incoming) // modulus
                for incoming in range(multiplier)
            ),
        )

    def then(self, higher: MahlerBorderCarryMap) -> MahlerBorderCarryMap:
        if type(higher) is not MahlerBorderCarryMap or (
            self.radix,
            self.multiplier,
        ) != (higher.radix, higher.multiplier):
            raise TypeError("incompatible carry boundary maps")
        if self.digits + higher.digits > MAX_SPATIAL_DIGITS:
            raise ValueError("spatial carry extent exceeds digit budget")
        return MahlerBorderCarryMap(
            self.radix,
            self.multiplier,
            self.digits + higher.digits,
            tuple(higher.responses[carry] for carry in self.responses),
        )

    def power(self, copies: int) -> MahlerBorderCarryMap:
        if type(copies) is not int or copies < 0 or copies > MAX_SPATIAL_REPETITIONS:
            raise ValueError("spatial motif copies exceed budget")
        result = self.identity(self.radix)
        factor = self
        remaining = copies
        while remaining:
            if remaining & 1:
                result = result.then(factor)
            remaining >>= 1
            if remaining:
                factor = factor.then(factor)
        return result

    def outgoing(self, incoming: int) -> int:
        if type(incoming) is not int or not 0 <= incoming < self.multiplier:
            raise ValueError("incoming carry outside the admitted ports")
        return self.responses[incoming]

    @classmethod
    def from_spatial_motif(
        cls, radix: int, motif: str, repetitions: int
    ) -> MahlerBorderCarryMap:
        if (
            type(radix) is not int
            or radix not in (4, 10)
            or not isinstance(motif, str)
            or not motif
            or not motif.isascii()
            or len(motif) > MAX_SPATIAL_DIGITS
            or type(repetitions) is not int
            or not 1 <= repetitions <= MAX_SPATIAL_REPETITIONS
        ):
            raise ValueError("invalid spatial carry motif")
        alphabet = "0123" if radix == 4 else "0123456789"
        if any(character not in alphabet for character in motif):
            raise ValueError("spatial carry motif contains an invalid digit")
        motif_action = cls.identity(radix)
        for character in reversed(motif):
            motif_action = motif_action.then(cls.digit(radix, int(character)))
        return motif_action.power(repetitions)


@dataclass(frozen=True, slots=True)
class MahlerLowBorderCarryCertificate:
    """Authenticated decimal carry into a pointed two-digit center."""

    source: int
    center_start: int
    carry_map: MahlerBorderCarryMap
    actual_carry: int
    motif_repetitions: int
    compressed_motif_blocks: int
    _issuer: object = field(default=None, init=False, repr=False, compare=False)
    _issuance_snapshot: tuple[int, tuple[object, ...]] | None = field(
        default=None, init=False, repr=False, compare=False
    )

    def __post_init__(self) -> None:
        if self._issuer is not _LOW_BORDER_ISSUER:
            raise ValueError("low-border certificate must come from a source join")

    @staticmethod
    def _tag(value: object) -> tuple[type[object], object]:
        return type(value), value

    @classmethod
    def _capture(
        cls, certificate: MahlerLowBorderCarryCertificate
    ) -> tuple[object, ...]:
        action = certificate.carry_map
        if type(action) is not MahlerBorderCarryMap:
            action_snapshot: object = (type(action), id(action))
        else:
            responses = action.responses
            action_snapshot = (
                type(action),
                id(action),
                cls._tag(action.radix),
                cls._tag(action.multiplier),
                cls._tag(action.digits),
                cls._tag(responses),
                tuple(cls._tag(value) for value in responses)
                if type(responses) is tuple
                else None,
            )
        return (
            cls._tag(certificate.source),
            cls._tag(certificate.center_start),
            action_snapshot,
            cls._tag(certificate.actual_carry),
            cls._tag(certificate.motif_repetitions),
            cls._tag(certificate.compressed_motif_blocks),
        )

    def _require_issued(self) -> None:
        if self._issuer is not _LOW_BORDER_ISSUER or self._issuance_snapshot != (
            id(self),
            self._capture(self),
        ):
            raise ValueError("low-border certificate is not source-issued")

    @classmethod
    def from_exterior(cls, join: object) -> MahlerLowBorderCarryCertificate:
        from number_compiler.sequences.antihydra.mahler_center_exterior_join import (
            MahlerCenterExteriorEvidence,
        )

        evidence = MahlerCenterExteriorEvidence.from_join(join)
        return cls._from_verified_evidence(evidence)

    @classmethod
    def _from_verified_evidence(
        cls, evidence: object
    ) -> MahlerLowBorderCarryCertificate:
        from number_compiler.sequences.antihydra.mahler_center_exterior_join import (
            MahlerCenterExteriorEvidence,
            MahlerCenterExteriorJoin,
        )

        if type(evidence) is not MahlerCenterExteriorEvidence:
            raise TypeError("low carry requires verified Mahler exterior evidence")
        join = evidence.join
        if type(join) is not MahlerCenterExteriorJoin or join.center_places != 2:
            raise TypeError("low carry certificate requires an issued two-digit center")
        start = join.center_start
        blocks = tuple(item for item in join.exterior if item.start < start)
        if not blocks or sum(item.width for item in blocks) != start:
            raise ValueError("low carry requires complete certified spatial coverage")
        cursor = 0
        for item in blocks:
            if item.start != cursor or item.start + item.width > start:
                raise ValueError("low border has a gap or overlaps the center")
            item.validate_against(join.authenticated_source)
            cursor += item.width
        if cursor != start:
            raise ValueError("low border does not reach the center")
        action = join.low_border_carry_map
        if (
            type(action) is not MahlerBorderCarryMap
            or action.radix != 10
            or action.multiplier != 3
            or action.digits != start
        ):
            raise ArithmeticError("source-issued low-border carry map is malformed")
        repeated = sum(block.repetitions for block in blocks if block.repetitions > 1)
        compressed_blocks = sum(block.repetitions > 1 for block in blocks)
        carry = action.outgoing(join.authenticated_source & 1)
        low = join.authenticated_source % 10**start
        if carry != (3 * low + (join.authenticated_source & 1)) // 10**start:
            raise ArithmeticError("cached low-border carry no longer matches source")
        if any(candidate.lower_carry_in != carry for candidate in join.candidates):
            raise ArithmeticError(
                "low spatial macro disagrees with center source carry"
            )
        result = object.__new__(cls)
        values = (
            join.authenticated_source,
            start,
            action,
            carry,
            repeated,
            compressed_blocks,
        )
        names = (
            "source",
            "center_start",
            "carry_map",
            "actual_carry",
            "motif_repetitions",
            "compressed_motif_blocks",
        )
        for name, value in zip(names, values, strict=True):
            object.__setattr__(result, name, value)
        object.__setattr__(result, "_issuer", _LOW_BORDER_ISSUER)
        object.__setattr__(
            result,
            "_issuance_snapshot",
            (id(result), cls._capture(result)),
        )
        result._require_issued()
        return result

    def upper_transfer(self, center: int, upper_source: int) -> tuple[int, int, int]:
        """Return next center, outgoing carry, and exact next upper block."""
        self._require_issued()
        if type(center) is not int or not 0 <= center < 100:
            raise ValueError("two-digit center required")
        if type(upper_source) is not int or upper_source < 0:
            raise ValueError("nonnegative upper source block required")
        high_carry, remainder = divmod(3 * center + self.actual_carry, 100)
        next_center = remainder // 2 + 50 * ((upper_source + high_carry) & 1)
        next_upper = (3 * upper_source + high_carry) // 2
        return next_center, high_carry, next_upper

    def packet(self) -> dict[str, object]:
        self._require_issued()
        return {
            "low_decimal_digits": self.center_start,
            "lower_carry_ports": self.carry_map.responses,
            "actual_lower_tripling_carry": self.actual_carry,
            "source_certified_spatial_motif_copies": self.motif_repetitions,
            "source_certified_repeated_motif_blocks": self.compressed_motif_blocks,
            "carry_powered_in_space": bool(self.compressed_motif_blocks),
            "scope": "one physical Mahler transition; no temporal driver inferred",
        }


@dataclass(frozen=True, slots=True)
class MahlerRadix4TwoTickCarry:
    """Nine-port spatial re-entry for two physical Mahler steps."""

    source: int
    low_digits: int
    source_digit: int
    low_translation: int
    incoming_carry: int
    outgoing_carry: int
    high_after_two: int
    carry_map: MahlerBorderCarryMap

    @classmethod
    def from_source(cls, source: int, *, digits: int = 6) -> MahlerRadix4TwoTickCarry:
        if (
            type(source) is not int
            or source <= 0
            or type(digits) is not int
            or not 0 <= digits <= 64
        ):
            raise ValueError("invalid pointed two-step radix-4 demand")
        digit = source % 4
        translation = RADIX4_LOW_TRANSLATIONS[digit]
        quotient = source // 4
        block = quotient % (4**digits)
        action = MahlerBorderCarryMap.from_block(4, block, digits)
        incoming = translation
        outgoing = action.outgoing(incoming)
        first = (3 * source + (source & 1)) // 2
        second = (3 * first + (first & 1)) // 2
        high = second // 4**digits
        if high != 9 * (quotient // 4**digits) + outgoing:
            raise ArithmeticError("nine-port G^2 re-entry disagrees with source")
        return cls(
            source,
            digits,
            digit,
            translation,
            incoming,
            outgoing,
            high,
            action,
        )

    def packet(self) -> dict[str, object]:
        return {
            "source_low_radix4_digit": self.source_digit,
            "two_step_low_translation": self.low_translation,
            "digit_depth_after_low_entry": self.low_digits,
            "nine_port_incoming_carry": self.incoming_carry,
            "nine_port_outgoing_carry": self.outgoing_carry,
            "nine_port_responses": self.carry_map.responses,
            "verified_high_after_two_steps": self.high_after_two,
            "high_position_radix4_digits": self.low_digits,
            "scope": "certified radix-4 two-step spatial re-entry",
        }


__all__ = [
    "RADIX4_LOW_TRANSLATIONS",
    "MahlerBorderCarryMap",
    "MahlerLowBorderCarryCertificate",
    "MahlerRadix4TwoTickCarry",
]
