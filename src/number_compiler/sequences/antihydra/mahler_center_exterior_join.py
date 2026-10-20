"""Source-certified Mahler exterior/cyclotomic/center carry product.

This transfers the useful *method* of the 2rev10 cyclotomic-center join,
not its reversal-specific digit stencil.  A complete, authentic exterior
cover is folded in Z/99 and Z/198 (spatial motifs are exponentiated), and
intersected with the actual global residue.  The resulting one/two-digit
center candidates are pushed through Mahler's *two-sided* 3D+epsilon,
then /2, transition.  The binary signed/XOR witness uses the shared Fermat
Boolean counter algebra on authenticated operands; it does not use the
Fermat-specific 3^(2^t) pivot or claim that an unknown input word repeats.

All power/repetition in this module is *spatial*: it never authorizes future
odd-event repetitions.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import is_runtime_instance
from number_compiler.arithmetic.fields.walsh import WalshH5
from number_compiler.sequences.antihydra.mahler_low_border_carry import (
    MahlerBorderCarryMap,
)
from number_compiler.sequences.power_numbers.three_dyadic_boolean_counter import (
    BinaryCounterFoldAction,
)

_MAX_DECIMAL_WIDTH = 4096
_MAX_REPEAT = 1 << 32
_MAX_POINTED_SOURCE_WIDTH = 256
_MAX_DECIMAL_SOURCE = 10**_MAX_POINTED_SOURCE_WIDTH


def _decimal_value(digits: str) -> int:
    value: int = 0
    for digit in digits:
        value = value * 10 + ord(digit) - ord("0")
    return value


def _geometric_sum(base: int, count: int, modulus: int) -> int:
    """1+b+...+b^(count-1) modulo modulus, using O(log count) products."""
    total, power, block_sum, block_power = 0, 1, 1, base % modulus
    while count:
        if count & 1:
            total = (total + power * block_sum) % modulus
            power = power * block_power % modulus
        count >>= 1
        if count:
            block_sum = block_sum * (1 + block_power) % modulus
            block_power = block_power * block_power % modulus
    return total


@dataclass(frozen=True, slots=True)
class MahlerExteriorMotif:
    """LSD-indexed spatial span: MSD-first motif repeated *within* a word."""

    start: int
    motif: str
    repetitions: int = 1

    def __post_init__(self) -> None:
        if type(self.start) is not int or self.start < 0:
            raise ValueError("exterior start must be a nonnegative digit position")
        if (
            not is_runtime_instance(self.motif, str)
            or not self.motif
            or not self.motif.isascii()
            or not self.motif.isdecimal()
            or len(self.motif) > _MAX_DECIMAL_WIDTH
        ):
            raise ValueError("exterior motif requires ASCII decimal digits")
        if (
            type(self.repetitions) is not int
            or not 1 <= self.repetitions <= _MAX_REPEAT
            or self.width > _MAX_DECIMAL_WIDTH
        ):
            raise BlockContextBudgetExceeded("exterior motif exceeds digit budget")

    @property
    def width(self) -> int:
        return len(self.motif) * self.repetitions

    def residue(self, modulus: int) -> int:
        if type(modulus) is not int or modulus < 2:
            raise ValueError("positive modular ring requested")
        d = len(self.motif)
        motif_value = _decimal_value(self.motif)
        geom = _geometric_sum(pow(10, d, modulus), self.repetitions, modulus)
        return (pow(10, self.start, modulus) * motif_value * geom) % modulus

    def _exact_digits(self) -> int:
        # Source verification is deliberately exact and bounded, and uses
        # exponentiation instead of expanding the literal repeated text.
        motif_width: int = len(self.motif)
        radix: int = 10**motif_width
        repeated_places: int = (radix**self.repetitions - 1) // (radix - 1)
        exact_digits: int = _decimal_value(self.motif) * repeated_places
        return exact_digits

    def validate_against(self, source: int) -> None:
        if (source // 10**self.start) % 10**self.width != self._exact_digits():
            raise ValueError("exterior motif is not authenticated by source digits")


def _decimal_width(source: int) -> int:
    if type(source) is not int or source < 1:
        raise ValueError("Mahler center requires a positive pointed source")
    # Check the shared pointed-source budget before converting an untrusted
    # integer to text. This also refuses values beyond Python's int-to-string
    # conversion limit without invoking that conversion.
    if source >= _MAX_DECIMAL_SOURCE:
        raise BlockContextBudgetExceeded(
            "Mahler center source exceeds the 256-digit budget"
        )
    return len(str(source))


def _signed_bit_changes(
    before: int, after: int, width: int
) -> tuple[tuple[int, int], ...]:
    return tuple(
        (i, ((after >> i) & 1) - ((before >> i) & 1))
        for i in range(width)
        if ((before ^ after) >> i) & 1
    )


@dataclass(frozen=True, slots=True)
class MahlerCenterCandidateAction:
    """One residue-compatible middle block with its exact bilateral carries."""

    center: int
    next_fixed_center: int
    lower_carry_in: int
    upper_tripling_carry_out: int
    upper_division_inlet: int
    next_mod99: int
    next_mod198: int
    center_xor_mask: int
    signed_center_changes: tuple[tuple[int, int], ...]
    tripling_counter: BinaryCounterFoldAction

    def packet(self) -> dict[str, object]:
        carry, signed_fold, h5 = self.tripling_counter.apply(0)
        return {
            "center": self.center,
            "next_fixed_position_center": self.next_fixed_center,
            "lower_tripling_carry": self.lower_carry_in,
            "upper_tripling_carry": self.upper_tripling_carry_out,
            "upper_division_inlet": self.upper_division_inlet,
            "next_mod99": self.next_mod99,
            "next_mod198": self.next_mod198,
            "xor_mask": self.center_xor_mask,
            "signed_bit_changes": self.signed_center_changes,
            "signed_value_change": sum(
                sign << bit for bit, sign in self.signed_center_changes
            ),
            "tripling_two_carry_contexts": self.tripling_counter.next_carries,
            "tripling_signed_fold": signed_fold,
            "tripling_outgoing_binary_carry": carry,
            "tripling_walsh_h5": (h5.phi2, h5.phi3_a, h5.phi3_b),
            "scope": "fixed LSD-indexed center window; re-center on width birth",
        }


@dataclass(frozen=True, slots=True)
class MahlerCenterExteriorJoin:
    """Pointed outer-residue ring joined to conditional interior Moore outputs."""

    width: int
    center_start: int
    center_places: int
    exterior: tuple[MahlerExteriorMotif, ...]
    spatial_carry_maps: tuple[MahlerBorderCarryMap, ...]
    outer99: int
    outer198: int
    source99: int
    source198: int
    source396: int
    source_mod6: int
    candidates: tuple[MahlerCenterCandidateAction, ...]
    source_admitted_centers: tuple[int, ...]
    pointed_center: int
    pointed_next_center: int
    authenticated_source: int
    low_border_carry_map: MahlerBorderCarryMap

    @classmethod
    def from_source(
        cls,
        source: int,
        *,
        center_places: int | None = None,
        center_start: int | None = None,
        exterior: tuple[MahlerExteriorMotif, ...] | None = None,
    ) -> MahlerCenterExteriorJoin:
        """Join complete outer spatial cover, cyclotomic residues and carries."""
        width = _decimal_width(source)
        if center_places is None:
            center_places = 1 if width & 1 else 2
        if type(center_places) is not int or center_places not in (1, 2):
            raise ValueError("center requires a one/two digit source block")
        if center_start is None:
            if (width - center_places) % 2 or width - center_places < 2:
                raise ValueError(
                    "center needs a one/two digit midpoint with both exteriors"
                )
            s = (width - center_places) // 2
        else:
            # This fixed two-digit window supports odd widths and width births;
            # it is source-positioned, not described as a canonical midpoint.
            if (
                type(center_start) is not int
                or center_start < 1
                or center_start + center_places >= width
            ):
                raise ValueError("fixed center window requires both exterior borders")
            s = center_start
        k = center_places
        low_mod = 10**s
        block_mod = 10**k
        lower = source % low_mod
        upper = source // (low_mod * block_mod)
        actual = (source // low_mod) % block_mod
        if exterior is None:
            # Default pointed evidence: exactly two complete border blocks.
            exterior = (
                MahlerExteriorMotif(0, str(lower).zfill(s)),
                MahlerExteriorMotif(s + k, str(upper)),
            )
        if type(exterior) is not tuple or not all(
            type(segment) is MahlerExteriorMotif for segment in exterior
        ):
            raise TypeError("center exterior needs typed spatial motif spans")
        ordered = tuple(sorted(exterior, key=lambda segment: segment.start))
        cursor = 0
        for item in ordered:
            if cursor == s:
                cursor += k
            if item.start != cursor:
                raise ValueError("incomplete, overlapping, or center-covering exterior")
            if item.start < s < item.start + item.width:
                raise ValueError("exterior motif crosses the center")
            if item.start < s + k < item.start + item.width:
                raise ValueError("exterior motif crosses the center")
            cursor = item.start + item.width
            item.validate_against(source)
        if cursor != width:
            raise ValueError("exterior motif sequence does not cover both borders")
        low_spans = tuple(part for part in ordered if part.start < s)
        if not low_spans or sum(part.width for part in low_spans) != s:
            raise ValueError("low exterior does not completely reach the center")
        span_maps = tuple(
            MahlerBorderCarryMap.from_block(10, lower, s)
            if len(low_spans) == 1 and part is low_spans[0] and part.repetitions == 1
            else MahlerBorderCarryMap.from_spatial_motif(
                10, part.motif, part.repetitions
            )
            for part in ordered
        )
        low_indices = tuple(
            index for index, part in enumerate(ordered) if part.start < s
        )
        if len(low_indices) == 1:
            low_carry_map = span_maps[low_indices[0]]
        else:
            low_carry_map = MahlerBorderCarryMap.identity(10)
            for index in low_indices:
                low_carry_map = low_carry_map.then(span_maps[index])
        if low_carry_map.digits != s:
            raise ArithmeticError("low-border carry map does not reach the center")
        outside99 = sum(segment.residue(99) for segment in ordered) % 99
        outside198 = sum(segment.residue(198) for segment in ordered) % 198
        rho99, rho198 = source % 99, source % 198
        # 10 has multiplicative order two modulo 99, but it is not a unit
        # modulo 198. Do not attempt an inverse of ten modulo 198.
        center_residue = (rho99 - outside99) * pow(pow(10, s, 99), -1, 99) % 99
        all_centers = tuple(
            c
            for c in range(block_mod)
            if c % 99 == center_residue
            and (outside198 + pow(10, s, 198) * c - rho198) % 198 == 0
        )
        if not all_centers or actual not in all_centers:
            raise ArithmeticError("outer/inner residue join lost the pointed center")
        admitted = list(all_centers)

        eps = lower & 1
        low_carry = low_carry_map.outgoing(eps)
        literal_carry, low_raw = divmod(3 * lower + eps, low_mod)
        if low_carry != literal_carry:
            raise ArithmeticError("spatial low-border map changed source carry")
        width_bits = (3 * (block_mod - 1) + 2).bit_length()
        actions: list[MahlerCenterCandidateAction] = []
        for c in all_centers:
            center_raw = 3 * c + low_carry
            high_carry, center_raw = divmod(center_raw, block_mod)
            upper_raw = 3 * upper + high_carry
            inlet = upper_raw & 1
            next_center = center_raw // 2 + (block_mod // 2) * inlet
            next_lower = low_raw // 2 + (low_mod // 2) * (center_raw & 1)
            next_upper = upper_raw // 2
            next_value = (
                next_lower + low_mod * next_center + low_mod * block_mod * next_upper
            )
            before_value = lower + low_mod * c + low_mod * block_mod * upper
            if next_value != (3 * before_value + eps) // 2:
                raise ArithmeticError("center conditional carry action lost source")
            if (outside99 + pow(10, s, 99) * c) % 99 != before_value % 99 or (
                outside198 + pow(10, s, 198) * c
            ) % 198 != before_value % 198:
                raise ArithmeticError("center conditional source lost outer residue")
            bit_changes = _signed_bit_changes(c, next_center, width_bits)
            if sum(sign << bit for bit, sign in bit_changes) != next_center - c:
                raise ArithmeticError("signed XOR bit change does not match center")
            counter = BinaryCounterFoldAction.from_words(
                c, 2 * c + low_carry, width_bits, width_bits
            )
            output_carry, delta, _ = counter.apply(0)
            if output_carry or delta != (2 * c + low_carry) % counter.modulus:
                raise ArithmeticError("shared two-carry action lost tripling update")
            actions.append(
                MahlerCenterCandidateAction(
                    c,
                    next_center,
                    low_carry,
                    high_carry,
                    inlet,
                    next_value % 99,
                    next_value % 198,
                    c ^ next_center,
                    bit_changes,
                    counter,
                )
            )
        pointed_next = (3 * source + (source & 1)) // 2
        pointed_center_after = (pointed_next // low_mod) % block_mod
        if (
            next(a for a in actions if a.center == actual).next_fixed_center
            != pointed_center_after
        ):
            raise ArithmeticError("pointed center differs from conditional ring output")
        # The next mod-99 clock requires 2*99 source precision, next mod-198
        # needs 2*198. That additional source bit is deliberately retained.
        if ((3 * (source % 198) + eps) // 2) % 99 != pointed_next % 99:
            raise ArithmeticError("mod-99 temporal clock lost dyadic inlet")
        if ((3 * (source % 396) + eps) // 2) % 198 != pointed_next % 198:
            raise ArithmeticError("mod-198 temporal clock lost dyadic inlet")
        return cls(
            width,
            s,
            k,
            ordered,
            span_maps,
            outside99,
            outside198,
            rho99,
            rho198,
            source % 396,
            source % 6,
            tuple(actions),
            tuple(admitted),
            actual,
            pointed_center_after,
            source,
            low_carry_map,
        )

    @property
    def one_step_signature_classes(self) -> int:
        # This is a *conditional one-step output* grouping, not a globally closed
        # temporal Moore class for arbitrary future sources.
        return len(
            {
                (
                    a.next_fixed_center,
                    a.upper_division_inlet,
                    a.upper_tripling_carry_out,
                    a.center_xor_mask,
                )
                for a in self.candidates
                if a.center in self.source_admitted_centers
            }
        )

    def packet(self) -> dict[str, object]:
        return {
            "width": self.width,
            "center_start_from_lsd": self.center_start,
            "center_places": self.center_places,
            "source_mod99": self.source99,
            "source_mod198": self.source198,
            "source_mod396": self.source396,
            "source_mod6": self.source_mod6,
            "exterior_mod99": self.outer99,
            "exterior_mod198": self.outer198,
            "source_checked_spatial_motifs": tuple(
                (s.start, s.motif, s.repetitions) for s in self.exterior
            ),
            "center_candidates": tuple(c.center for c in self.candidates),
            "source_admitted_centers": self.source_admitted_centers,
            "pointed_center": self.pointed_center,
            "pointed_next_fixed_center": self.pointed_next_center,
            "conditional_one_step_output_classes": self.one_step_signature_classes,
            "center_actions": tuple(c.packet() for c in self.candidates),
            "low_border_carry_ports": self.low_border_carry_map.responses,
            "low_border_carry_spatial_depth": self.low_border_carry_map.digits,
            "next_clock_requires": (
                "source mod 198 for mod 99",
                "source mod 396 for mod 198",
            ),
            "scope": (
                "complete exact spatial exterior + source-certified temporal border; "
                "conditional fixed-position center actions; no guessed repeated "
                "middle driver or new width-center period"
            ),
        }


_EXTERIOR_EVIDENCE_ISSUER = object()


def _exact(value: object) -> tuple[type[object], object]:
    return type(value), value


def _join_snapshot(
    join: MahlerCenterExteriorJoin, *, identities: bool = True
) -> tuple[object, ...]:
    """Type-tag every nested scalar so bool/int equality cannot forge a join."""

    def object_id(value: object) -> int | None:
        return id(value) if identities else None

    scalar_names = (
        "width",
        "center_start",
        "center_places",
        "outer99",
        "outer198",
        "source99",
        "source198",
        "source396",
        "source_mod6",
        "pointed_center",
        "pointed_next_center",
        "authenticated_source",
    )
    scalars = tuple(_exact(getattr(join, name)) for name in scalar_names)
    if any(tag is not int for tag, _ in scalars):
        raise TypeError("Mahler join scalar fields require exact integers")
    if type(join.exterior) is not tuple or type(join.candidates) is not tuple:
        raise TypeError("Mahler join requires exact exterior/candidate tuples")
    exterior: list[object] = []
    for span in join.exterior:
        if type(span) is not MahlerExteriorMotif:
            raise TypeError("Mahler join contains an untyped exterior motif")
        if (
            type(span.start) is not int
            or type(span.motif) is not str
            or type(span.repetitions) is not int
        ):
            raise TypeError("Mahler motif fields require exact scalar types")
        exterior.append(
            (
                object_id(span),
                _exact(span.start),
                _exact(span.motif),
                _exact(span.repetitions),
            )
        )
    candidates: list[object] = []
    candidate_scalar_names = (
        "center",
        "next_fixed_center",
        "lower_carry_in",
        "upper_tripling_carry_out",
        "upper_division_inlet",
        "next_mod99",
        "next_mod198",
        "center_xor_mask",
    )
    for candidate in join.candidates:
        if type(candidate) is not MahlerCenterCandidateAction:
            raise TypeError("Mahler join contains an untyped center candidate")
        candidate_scalars = tuple(
            _exact(getattr(candidate, name)) for name in candidate_scalar_names
        )
        if any(tag is not int for tag, _ in candidate_scalars):
            raise TypeError("Mahler candidate fields require exact integers")
        changes = candidate.signed_center_changes
        if type(changes) is not tuple or any(
            type(pair) is not tuple
            or len(pair) != 2
            or type(pair[0]) is not int
            or type(pair[1]) is not int
            for pair in changes
        ):
            raise TypeError("signed center changes require exact integer pairs")
        counter = candidate.tripling_counter
        if type(counter) is not BinaryCounterFoldAction:
            raise TypeError("Mahler candidate counter has the wrong action type")
        if any(
            type(value) is not int for value in (counter.fermat_width, counter.length)
        ):
            raise TypeError("Mahler counter dimensions require exact integers")
        counter_tuples = (counter.next_carries, counter.deltas)
        if any(
            type(values) is not tuple
            or len(values) != 2
            or any(type(value) is not int for value in values)
            for values in counter_tuples
        ):
            raise TypeError("Mahler counter rows require exact integer pairs")
        if type(counter.harmonics) is not tuple or len(counter.harmonics) != 2:
            raise TypeError("Mahler counter requires two H5 actions")
        harmonics: list[object] = []
        for harmonic in counter.harmonics:
            if type(harmonic) is not WalshH5:
                raise TypeError("Mahler counter contains an untyped H5 action")
            coordinates = tuple(
                _exact(getattr(harmonic, name))
                for name in ("length_mod6", "phi2", "phi3_a", "phi3_b")
            )
            if any(tag is not int for tag, _ in coordinates):
                raise TypeError("Mahler H5 coordinates require exact integers")
            harmonics.append((object_id(harmonic), coordinates))
        candidates.append(
            (
                object_id(candidate),
                candidate_scalars,
                object_id(changes),
                tuple(
                    (object_id(pair), _exact(pair[0]), _exact(pair[1]))
                    for pair in changes
                ),
                object_id(counter),
                _exact(counter.fermat_width),
                _exact(counter.length),
                object_id(counter.next_carries),
                tuple(_exact(value) for value in counter.next_carries),
                object_id(counter.deltas),
                tuple(_exact(value) for value in counter.deltas),
                object_id(counter.harmonics),
                tuple(harmonics),
            )
        )
    admitted = join.source_admitted_centers
    if type(admitted) is not tuple or any(type(value) is not int for value in admitted):
        raise TypeError("admitted center fiber requires exact integer tuple")
    action = join.low_border_carry_map
    if type(action) is not MahlerBorderCarryMap:
        raise TypeError("Mahler join contains an untyped low-border action")
    if (
        any(
            type(value) is not int
            for value in (action.radix, action.multiplier, action.digits)
        )
        or type(action.responses) is not tuple
        or any(type(value) is not int for value in action.responses)
    ):
        raise TypeError("low-border carry action requires exact integer fields")
    if type(join.spatial_carry_maps) is not tuple or len(
        join.spatial_carry_maps
    ) != len(join.exterior):
        raise TypeError("Mahler join requires one spatial carry map per motif")
    spatial_maps: list[object] = []
    for carry_map in join.spatial_carry_maps:
        if type(carry_map) is not MahlerBorderCarryMap:
            raise TypeError("Mahler join contains an untyped spatial carry map")
        if (
            any(
                type(value) is not int
                for value in (carry_map.radix, carry_map.multiplier, carry_map.digits)
            )
            or type(carry_map.responses) is not tuple
            or any(type(value) is not int for value in carry_map.responses)
        ):
            raise TypeError("spatial carry map requires exact integer fields")
        spatial_maps.append(
            (
                object_id(carry_map),
                _exact(carry_map.radix),
                _exact(carry_map.multiplier),
                _exact(carry_map.digits),
                object_id(carry_map.responses),
                tuple(_exact(value) for value in carry_map.responses),
            )
        )
    return (
        object_id(join),
        scalars,
        object_id(join.exterior),
        tuple(exterior),
        object_id(join.spatial_carry_maps),
        tuple(spatial_maps),
        _exact(join.outer99),
        _exact(join.outer198),
        _exact(join.source99),
        _exact(join.source198),
        _exact(join.source396),
        _exact(join.source_mod6),
        object_id(join.candidates),
        tuple(candidates),
        object_id(admitted),
        tuple(_exact(value) for value in admitted),
        _exact(join.pointed_center),
        _exact(join.pointed_next_center),
        _exact(join.authenticated_source),
        object_id(action),
        _exact(action.radix),
        _exact(action.multiplier),
        _exact(action.digits),
        object_id(action.responses),
        tuple(_exact(value) for value in action.responses),
    )


@dataclass(frozen=True, slots=True, init=False)
class MahlerCenterExteriorEvidence:
    """Locally verified join plus one carry action per spatial motif."""

    join: MahlerCenterExteriorJoin
    span_carry_maps: tuple[MahlerBorderCarryMap, ...]
    _issuer: object
    _snapshot: tuple[object, ...]

    @classmethod
    def _issue(cls, join: MahlerCenterExteriorJoin) -> MahlerCenterExteriorEvidence:
        maps = join.spatial_carry_maps
        result = object.__new__(cls)
        object.__setattr__(result, "join", join)
        object.__setattr__(result, "span_carry_maps", maps)
        object.__setattr__(result, "_issuer", _EXTERIOR_EVIDENCE_ISSUER)
        map_snapshot = tuple(
            (
                id(action),
                _exact(action.radix),
                _exact(action.multiplier),
                _exact(action.digits),
                id(action.responses),
                tuple(_exact(value) for value in action.responses),
            )
            for action in maps
        )
        object.__setattr__(
            result, "_snapshot", (id(result), _join_snapshot(join), map_snapshot)
        )
        return result

    @classmethod
    def from_source(
        cls,
        source: int,
        *,
        center_places: int = 2,
        center_start: int | None = None,
        exterior: tuple[MahlerExteriorMotif, ...] | None = None,
    ) -> MahlerCenterExteriorEvidence:
        join = MahlerCenterExteriorJoin.from_source(
            source,
            center_places=center_places,
            center_start=center_start,
            exterior=exterior,
        )
        return cls._issue(join)

    @classmethod
    def from_join(cls, value: object) -> MahlerCenterExteriorEvidence:
        if type(value) is cls:
            value.require_issued()
            return value
        if type(value) is not MahlerCenterExteriorJoin:
            raise TypeError("Mahler exterior evidence requires a source join")
        original = _join_snapshot(value, identities=False)
        rebuilt = MahlerCenterExteriorJoin.from_source(
            value.authenticated_source,
            center_places=value.center_places,
            center_start=value.center_start,
            exterior=value.exterior,
        )
        if original != _join_snapshot(rebuilt, identities=False):
            raise ValueError("Mahler exterior join changed since source issuance")
        return cls._issue(rebuilt)

    def require_issued(self) -> None:
        if self._issuer is not _EXTERIOR_EVIDENCE_ISSUER:
            raise ValueError("Mahler exterior evidence is not source-issued")
        map_snapshot = tuple(
            (
                id(action),
                _exact(action.radix),
                _exact(action.multiplier),
                _exact(action.digits),
                id(action.responses),
                tuple(_exact(value) for value in action.responses),
            )
            for action in self.span_carry_maps
        )
        if self._snapshot != (
            id(self),
            _join_snapshot(self.join),
            map_snapshot,
        ):
            raise ValueError("Mahler exterior evidence changed after issuance")
