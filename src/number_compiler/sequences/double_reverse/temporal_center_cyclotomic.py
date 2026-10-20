"""NC17 joint cyclotomic, spatial-bank, and central-seam certificates.

The global mod-99/198 quotient never licenses an interior word by itself.
This module only consumes *source-issued* bank output packets whose paired
spatial coverage leaves precisely one unknown central digit or digit pair.
The exterior is folded modulo 99 and 198 in O(sum of motif lengths), without
expanding CONCAT/REPEAT repetitions.  A four-step conditional center action
can then be restricted by both global and spatial source certificates.

Every period statement here concerns a finite physical-time witness.  In
particular, no finite mod-99 orbit is an all-depth center driver theorem.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from typing import TypeAlias

from ._temporal_bank_authority import (
    SourceAuthorizedRecord,
    SourceRecordAuthority,
    issue_source_record,
    require_source_arena,
    validate_source_record,
)
from .source_bound_bank import PointedBankSource
from .temporal_bank_output_morphism import (
    CertifiedSpatialBankMorphism,
    ExactPointedBankWindow,
)
from .temporal_center_selector import (
    CenterDriver,
    CenterInputMoore,
    CenterReturn,
    center_input_moore,
    center_return,
)
from .temporal_hashlife import growth_ports
from .temporal_hashlife_types import UncertifiedPointedStencilError
from .temporal_residue_quotient import (
    PHYSICAL_GROWTH_CYCLES,
    CertifiedResidueTemporalAction,
    certified_residue_action,
    decimal_residues_from_slp,
)

BankWitness: TypeAlias = CertifiedSpatialBankMorphism | ExactPointedBankWindow


@lru_cache(maxsize=1)
def band_moore() -> CenterInputMoore:
    """Reuse the exact all-40-input band quotient across demanded blocks."""
    return center_input_moore("band")


def cyclotomic_four_block_order(residue99: int, residue198: int) -> int | None:
    """Exact scalar-return order under the certified four-physical-step clock.

    Every admitted 4-letter growth word has two births and an *odd* skew.
    Hence the 4-step multipliers are 61 modulo 99 and 160 modulo 198.
    Odd mod-198 sources have a transient before entering the even image, so
    their initial lifted class has no positive-period return to itself.
    This is never automatically a period of the center or full integer.
    """
    if (
        type(residue99) is not int
        or not 0 <= residue99 < 99
        or type(residue198) is not int
        or not 0 <= residue198 < 198
        or residue198 % 99 != residue99
    ):
        raise ValueError("invalid cyclotomic source residues")
    if residue198 % 2:
        return None
    for k in (1, 2, 3, 5, 6, 10, 15, 30):
        if (
            residue99 * pow(61, k, 99) % 99 == residue99
            and residue198 * pow(160, k, 198) % 198 == residue198
        ):
            return k
    raise AssertionError("even mod-198 source escaped the 30-block scalar orbit")


@dataclass(frozen=True, slots=True)
class CertifiedCyclotomicCenter(SourceAuthorizedRecord):
    """Pointed output center inferred from a *complete* certified exterior.

    This is the fiber product of the full scalar residue action and an SLP-
    or cone-proved paired exterior.  Two central digits can retain both 00
    and 99.  The center is never read to decide an ambiguity.
    """

    physical_prefix: int
    f_steps: int
    phase_out: int
    width_out: int
    global_mod99: int
    global_mod198: int
    exterior_mod99: int
    exterior_mod198: int
    center_mod99: int
    candidates: tuple[tuple[int, ...], ...]
    band_moore_classes: tuple[int, ...]
    witnessed_spans: tuple[tuple[int, int], ...]

    @property
    def global_four_block_order(self) -> int | None:
        self.validate_source_authority()
        return cyclotomic_four_block_order(self.global_mod99, self.global_mod198)

    @property
    def center_width(self) -> int:
        return 1 if self.width_out % 2 else 2

    @property
    def center_position(self) -> int:
        return (self.width_out - self.center_width) // 2

    @property
    def forced_center(self) -> tuple[int, ...] | None:
        self.validate_source_authority()
        return self.candidates[0] if len(self.candidates) == 1 else None

    def validate_source_authority(self) -> SourceRecordAuthority:
        return validate_source_record(self)


@dataclass(frozen=True, slots=True)
class CertifiedCyclotomicCenterReturn(SourceAuthorizedRecord):
    """Four physical steps filtered by two source-certified center fibers."""

    first: CertifiedCyclotomicCenter
    last: CertifiedCyclotomicCenter
    admissible: tuple[CenterReturn, ...]
    globally_expected_mod99: int
    globally_expected_mod198: int
    all_depth_period_claim: bool = False

    @property
    def drivers(self) -> tuple[CenterDriver, ...]:
        self.validate_source_authority()
        return tuple(dict.fromkeys(result.driver for result in self.admissible))

    def validate_source_authority(self) -> SourceRecordAuthority:
        authority = validate_source_record(self)
        self.first.validate_source_authority()
        self.last.validate_source_authority()
        return authority


@dataclass(frozen=True, slots=True)
class CertifiedCyclotomicCenterDriver(SourceAuthorizedRecord):
    """One physically witnessed four-tick driver, not a periodic-driver proof.

    All digits are extracted from small *pointed* source cones.  No full
    endpoint SLP, interior scan or 2304-tick driver loop is constructed.
    """

    physical_prefix: int
    f_steps_start: int
    width_start: int
    initial_pair: tuple[int, int]
    odd_centers: tuple[int, int, int]
    driver: CenterDriver
    next_pair: tuple[int, int]
    source_mod99: int
    target_mod99: int
    source_mod198: int
    target_mod198: int
    band_moore_before: int
    band_moore_after: int
    all_depth_period_claim: bool = False

    @property
    def global_four_block_order(self) -> int | None:
        self.validate_source_authority()
        return cyclotomic_four_block_order(self.source_mod99, self.source_mod198)

    def validate_source_authority(self) -> SourceRecordAuthority:
        return validate_source_record(self)


def certified_cyclotomic_center_driver(
    source: PointedBankSource, *, start_f_steps: int | None = None
) -> CertifiedCyclotomicCenterDriver:
    """Join four-step border clock, true carry inlets and center Moore IDs.

    By default the block is the last four physical steps of the requested
    source-certified F^d horizon.  The conditional center map is used only
    on its admissible even/odd/odd/odd/even clock sector.
    """
    source.validate(require_issued_cursor=source.f_steps > 0)
    start = source.f_steps - 2 if start_f_steps is None else start_f_steps
    if type(start) is not int or start < 0 or start + 2 > source.f_steps:
        raise ValueError(
            "four-step center block exceeds its source-authenticated horizon"
        )
    start_phase = (source.phase + 2 * start) % 4
    start_width = source.width_in + sum(growth_ports(source.phase, start))
    if start_width % 2 or PHYSICAL_GROWTH_CYCLES[start_phase] != (1, 0, 0, 1):
        raise ValueError("center driver requires an even/odd/odd/odd/even width clock")
    center_index = start_width // 2
    cache: dict[tuple[int, int], int] = {}

    def even_digit(f: int, at: int) -> int:
        key = (2 * f, at)
        if key in cache:
            return cache[key]
        w = source.width_in + sum(growth_ports(source.phase, f))
        if not 0 <= at < w:
            raise IndexError(at)
        # Center-driver digits arrive in small clusters on each even slice.
        # Share one bounded causal interval across nearby queries.
        begin = max(0, min(at, w // 2 - 5))
        end = min(w, max(at + 1, w // 2 + 6))
        if end - begin > 18:
            begin, end = at, at + 1
        values = source.engine.pointed_window(
            source.root, f, source.phase, begin, end - begin
        )
        for offset, value in enumerate(values):
            cache[(2 * f, begin + offset)] = value
        return cache[key]

    def digit(t: int, at: int) -> int:
        key = (t, at)
        if key in cache:
            return cache[key]
        f, odd = divmod(t, 2)
        if not odd:
            return even_digit(f, at)
        width = source.width_in + sum(growth_ports(source.phase, f))
        phase_now = (source.phase + 2 * f) % 4
        growth = PHYSICAL_GROWTH_CYCLES[phase_now][0]
        if not 0 <= at < width + growth:
            raise IndexError(at)
        if growth and at == 0:
            value = 1
        else:
            input_index = width - 1 - (at - growth)
            carry = int(input_index > 0 and even_digit(f, input_index - 1) >= 5)
            value = (2 * even_digit(f, input_index) + carry) % 10
        cache[key] = value
        return value

    initial = (
        digit(2 * start, center_index - 1),
        digit(2 * start, center_index),
    )
    odd = tuple(digit(2 * start + j, center_index) for j in (1, 2, 3))
    if len(odd) != 3:
        raise AssertionError("cyclotomic center driver needs three odd centers")
    odd_centers = (odd[0], odd[1], odd[2])
    driver = CenterDriver(
        int(digit(2 * start + 1, center_index - 1) >= 5),
        int(digit(2 * start + 2, center_index - 1) >= 5),
        int(digit(2 * start + 3, center_index - 1) >= 5),
        digit(2 * start + 3, center_index + 1) % 5,
    )
    final = (
        digit(2 * start + 4, center_index),
        digit(2 * start + 4, center_index + 1),
    )
    output = center_return(initial, driver)
    if output.odd != odd or output.next_pair != final:
        raise AssertionError("pointed center digits disagree with the four-step monoid")

    residue99, residue198 = decimal_residues_from_slp(
        source.arena,
        source.root,
        ledger=source.ledger,
        scratch_owner=source.scratch_owner,
    )
    before = certified_residue_action(
        phase=source.phase,
        width=source.width_in,
        duration=2 * start,
        source_mod99=residue99,
        source_mod198=residue198,
    )
    after = certified_residue_action(
        phase=source.phase,
        width=source.width_in,
        duration=2 * (start + 2),
        source_mod99=residue99,
        source_mod198=residue198,
    )
    monodromy = certified_residue_action(
        phase=start_phase,
        width=start_width,
        duration=4,
        source_mod99=before.target_mod99,
        source_mod198=before.target_mod198,
    )
    if (
        monodromy.width_out != start_width + 2
        or monodromy.target_mod99 != after.target_mod99
        or monodromy.target_mod198 != after.target_mod198
    ):
        raise AssertionError("cyclotomic residue action failed temporal composition")
    moore = band_moore()
    record = CertifiedCyclotomicCenterDriver(
        source.physical_prefix,
        start,
        start_width,
        initial,
        odd_centers,
        driver,
        final,
        before.target_mod99,
        after.target_mod99,
        before.target_mod198,
        after.target_mod198,
        moore.class_for(initial),
        moore.class_for(final),
    )
    return issue_source_record(
        record, source.arena, source.root, source_generation=source.physical_prefix
    )


@dataclass(frozen=True, slots=True)
class CertifiedCyclotomicCenterProgram(SourceAuthorizedRecord):
    """Finite source-verified composition of joint four-generation relations.

    ``relation`` is 100 bitsets, each encoding all possible terminal ordered
    center pairs for one entry pair.  Every composition joins actual adjacent
    certified blocks; there is no automatic cyclic repetition.
    """

    first: CertifiedCyclotomicCenter
    last: CertifiedCyclotomicCenter
    four_step_blocks: int
    relation: tuple[int, ...]
    global_start_mod99: int
    global_finish_mod99: int
    global_start_mod198: int
    global_finish_mod198: int
    all_depth_period_claim: bool = False

    @property
    def necessary_global_return_blocks(self) -> int | None:
        """Divisibility requirement for any *joint* four-block return."""
        self.validate_source_authority()
        return cyclotomic_four_block_order(
            self.global_start_mod99, self.global_start_mod198
        )

    def validate_source_authority(self) -> SourceRecordAuthority:
        authority = validate_source_record(self)
        self.first.validate_source_authority()
        self.last.validate_source_authority()
        return authority

    def then(
        self, later: CertifiedCyclotomicCenterProgram
    ) -> CertifiedCyclotomicCenterProgram:
        fa = self.validate_source_authority()
        la = later.validate_source_authority()
        if (
            fa.arena is not la.arena
            or fa.root != la.root
            or fa.source_generation != la.source_generation
            or self.last.f_steps != later.first.f_steps
            or self.last != later.first
            or self.global_finish_mod99 != later.global_start_mod99
            or self.global_finish_mod198 != later.global_start_mod198
        ):
            raise ValueError("joint temporal word lacks source-certified adjacency")
        # Compose relations without expanding possible center-driver paths.
        composed: list[int] = []
        for mask in self.relation:
            output = 0
            while mask:
                low_bit = mask & -mask
                position = low_bit.bit_length() - 1
                output |= later.relation[position]
                mask ^= low_bit
            composed.append(output)
        record = CertifiedCyclotomicCenterProgram(
            self.first,
            later.last,
            self.four_step_blocks + later.four_step_blocks,
            tuple(composed),
            self.global_start_mod99,
            later.global_finish_mod99,
            self.global_start_mod198,
            later.global_finish_mod198,
        )
        return issue_source_record(
            record,
            require_source_arena(fa),
            fa.root,
            source_generation=fa.source_generation,
        )

    def power(self, repeats: int) -> CertifiedCyclotomicCenterProgram:
        """Do not mistake one witnessed driver word for a repeated source word."""
        self.validate_source_authority()
        if type(repeats) is not int or repeats < 1:
            raise ValueError("source-bound program requires a positive repeat count")
        if repeats == 1:
            return self
        raise UncertifiedPointedStencilError(
            "no all-depth source proof licenses repeating the center driver"
        )


def certified_cyclotomic_center_program(
    block: CertifiedCyclotomicCenterReturn,
) -> CertifiedCyclotomicCenterProgram:
    """Lift a guarded center return into the composable relation monoid."""
    authority = block.validate_source_authority()
    rows = [0] * 100
    for result in block.admissible:
        left = 10 * result.initial[0] + result.initial[1]
        right = 10 * result.next_pair[0] + result.next_pair[1]
        rows[left] |= 1 << right
    return issue_source_record(
        CertifiedCyclotomicCenterProgram(
            block.first,
            block.last,
            1,
            tuple(rows),
            block.first.global_mod99,
            block.last.global_mod99,
            block.first.global_mod198,
            block.last.global_mod198,
        ),
        require_source_arena(authority),
        authority.root,
        source_generation=authority.source_generation,
    )


def _pair_residue(
    width: int, position: int, digits: tuple[int, int], modulus: int
) -> int:
    # Decimal source/target SLPs are MSD-first.  These are the *actual*
    # positional exponents, not 10**position in left-to-right order.
    left, right = digits
    return (
        left * pow(10, width - 1 - position, modulus)
        + right * pow(10, position, modulus)
    ) % modulus


def spatial_bank_residue(bank: CertifiedSpatialBankMorphism, modulus: int) -> int:
    """Geometric/spatial motif fold, constant work in `bank.repeats`."""
    motif = bank.motif
    p = len(motif)
    start = bank.final_pair_start
    width = bank.width_out

    def motif_value(offset: int) -> int:
        return (
            sum(
                _pair_residue(width, offset + j, frame.digits, modulus)
                for j, frame in enumerate(motif)
            )
            % modulus
        )

    repeats = bank.repeats
    total = 0
    if repeats:
        total = motif_value(start)
        later = repeats - 1
        if later:
            # At all exterior positions, left powers are >= 10**2 and right
            # powers are >= 10**1 except pair zero (the *first* copy).
            # Mod 99 and 198 the positional weights are 2-periodic there.
            first_later = motif_value(start + p)
            if p % 2 == 0:
                total += later * first_later
            else:
                total += ((later + 1) // 2) * first_later
                if later >= 2:
                    total += (later // 2) * motif_value(start + 2 * p)
    suffix_start = start + repeats * p
    total += sum(
        _pair_residue(width, suffix_start + j, frame.digits, modulus)
        for j, frame in enumerate(bank.suffix)
    )
    return total % modulus


def _window_residue(window: ExactPointedBankWindow, modulus: int) -> int:
    return (
        sum(
            _pair_residue(
                window.width_out, window.final_pair_start + i, frame.digits, modulus
            )
            for i, frame in enumerate(window.frames)
        )
        % modulus
    )


def _bank_fields(
    bank: BankWitness,
) -> tuple[int, int, int, int, int, int, CertifiedResidueTemporalAction]:
    if type(bank) is CertifiedSpatialBankMorphism:
        return (
            bank.final_pair_start,
            bank.pair_count,
            bank.physical_prefix,
            bank.f_steps,
            bank.phase_in,
            bank.width_out,
            bank.residue_action,
        )
    if type(bank) is ExactPointedBankWindow:
        return (
            bank.final_pair_start,
            bank.pair_count,
            bank.physical_prefix,
            bank.f_steps,
            bank.phase_in,
            bank.width_out,
            bank.residue_action,
        )
    raise TypeError("center join needs certified spatial bank or exact windows")


def _source_identity(source: PointedBankSource, record: SourceAuthorizedRecord) -> None:
    authority = validate_source_record(record)
    if (
        authority.arena is not source.arena
        or authority.root != source.root
        or authority.source_generation != source.physical_prefix
    ):
        raise ValueError("center join received a bank from another source cursor")


def certified_cyclotomic_center(
    source: PointedBankSource, witnesses: tuple[BankWitness, ...]
) -> CertifiedCyclotomicCenter:
    """Join source mod-99/198 action to completely covered exterior pairs.

    Missing even *one* pair refuses.  The source owner must supply the bank
    witnesses; no scalar residue is accepted as a free user-supplied guess.
    Both 00/99 possibilities are retained when the quotient cannot split them.
    """
    source.validate(require_issued_cursor=source.f_steps > 0)
    if not witnesses or type(witnesses) is not tuple:
        raise ValueError("center quotient needs a complete typed exterior cover")
    width = source.width_out
    center_width = 2 if width % 2 == 0 else 1
    exterior_count = (width - center_width) // 2
    if exterior_count == 0:
        raise ValueError("center join needs at least one exterior pair witness")
    offset = 0
    outer99 = 0
    outer198 = 0
    expected_residue: CertifiedResidueTemporalAction | None = None
    spans: list[tuple[int, int]] = []
    for witness in witnesses:
        start, count, prefix, steps, phase, output_width, action = _bank_fields(witness)
        _source_identity(source, witness)
        _source_identity(source, action)
        action.validate_source_authority()
        if (
            prefix != source.physical_prefix
            or steps != source.f_steps
            or phase != source.phase
            or output_width != width
            or action.width_out != width
            or action.width_in != source.width_in
            or action.duration != 2 * steps
            or action.phase != phase
        ):
            raise ValueError("center exterior witness has incompatible source/time")
        if start != offset or count < 1 or offset + count > exterior_count:
            raise ValueError("center exterior is missing, overlapping or over-covered")
        if expected_residue is None:
            expected_residue = action
        elif (
            action.target_mod99 != expected_residue.target_mod99
            or action.target_mod198 != expected_residue.target_mod198
            or action.source_mod99 != expected_residue.source_mod99
            or action.source_mod198 != expected_residue.source_mod198
        ):
            raise ValueError("center exterior witnesses disagree on global residues")
        if type(witness) is CertifiedSpatialBankMorphism:
            outer99 += spatial_bank_residue(witness, 99)
            outer198 += spatial_bank_residue(witness, 198)
        elif type(witness) is ExactPointedBankWindow:
            outer99 += _window_residue(witness, 99)
            outer198 += _window_residue(witness, 198)
        else:
            raise TypeError("center join needs certified spatial bank or exact windows")
        spans.append((start, count))
        offset += count
    if offset != exterior_count or expected_residue is None:
        raise ValueError("incomplete exterior: cannot infer the middle digit")
    outer99 %= 99
    outer198 %= 198
    residue_center = (
        pow(10, exterior_count, 99) * (expected_residue.target_mod99 - outer99)
    ) % 99
    upper = 10**center_width
    options = tuple(
        tuple(int(c) for c in f"{value:0{center_width}d}")
        for value in range(upper)
        if value % 99 == residue_center
        and (outer198 + pow(10, exterior_count, 198) * value) % 198
        == expected_residue.target_mod198
    )
    if not options:
        raise AssertionError("source's cyclotomic center has no compatible digits")
    if center_width == 2:
        moore = band_moore()
        classes = tuple(moore.class_for((x[0], x[1])) for x in options)
    else:
        classes = ()
    record = CertifiedCyclotomicCenter(
        source.physical_prefix,
        source.f_steps,
        (source.phase + 2 * source.f_steps) % 4,
        width,
        expected_residue.target_mod99,
        expected_residue.target_mod198,
        outer99,
        outer198,
        residue_center,
        options,
        classes,
        tuple(spans),
    )
    return issue_source_record(
        record, source.arena, source.root, source_generation=source.physical_prefix
    )


def certified_cyclotomic_center_four_return(
    first: CertifiedCyclotomicCenter,
    last: CertifiedCyclotomicCenter,
    *,
    driver_witness: CertifiedCyclotomicCenterDriver | None = None,
) -> CertifiedCyclotomicCenterReturn:
    """Filter *all* 40 center letters through two source-authorized fibers.

    Does not assert a repeating letter or an eventual cycle.  The 4-tick
    center formula is valid only in the even/odd/odd/odd/even width sector.
    """
    fa = first.validate_source_authority()
    la = last.validate_source_authority()
    if (
        fa.arena is not la.arena
        or fa.root != la.root
        or fa.source_generation != la.source_generation
        or first.physical_prefix != last.physical_prefix
        or last.f_steps != first.f_steps + 2
        or first.center_width != 2
        or last.center_width != 2
        or PHYSICAL_GROWTH_CYCLES[first.phase_out] != (1, 0, 0, 1)
    ):
        raise ValueError("four-step center return requires one aligned source cylinder")
    action = certified_residue_action(
        phase=first.phase_out,
        width=first.width_out,
        duration=4,
        source_mod99=first.global_mod99,
        source_mod198=first.global_mod198,
    )
    if (
        action.width_out != last.width_out
        or action.target_mod99 != last.global_mod99
        or action.target_mod198 != last.global_mod198
    ):
        raise ValueError("outer cyclotomic clock contradicts the center return")
    if driver_witness is not None:
        da = driver_witness.validate_source_authority()
        if (
            da.arena is not fa.arena
            or da.root != fa.root
            or da.source_generation != fa.source_generation
            or driver_witness.physical_prefix != first.physical_prefix
            or driver_witness.f_steps_start != first.f_steps
            or driver_witness.width_start != first.width_out
            or driver_witness.source_mod99 != first.global_mod99
            or driver_witness.target_mod99 != last.global_mod99
            or driver_witness.source_mod198 != first.global_mod198
            or driver_witness.target_mod198 != last.global_mod198
        ):
            raise ValueError(
                "center driver is not certified on this joint source interval"
            )
    possible: list[CenterReturn] = []
    final = set(last.candidates)
    for pair in first.candidates:
        for a in (0, 1):
            for b in (0, 1):
                for c in (0, 1):
                    for r in range(5):
                        candidate = center_return(
                            (pair[0], pair[1]), CenterDriver(a, b, c, r)
                        )
                        if candidate.next_pair in final and (
                            driver_witness is None
                            or candidate.driver == driver_witness.driver
                            and candidate.initial == driver_witness.initial_pair
                            and candidate.next_pair == driver_witness.next_pair
                        ):
                            possible.append(candidate)
    if not possible:
        raise AssertionError("center driver/cyclotomic fiber product is empty")
    return issue_source_record(
        CertifiedCyclotomicCenterReturn(
            first, last, tuple(possible), action.target_mod99, action.target_mod198
        ),
        require_source_arena(fa),
        fa.root,
        source_generation=first.physical_prefix,
    )


__all__ = [
    "CertifiedCyclotomicCenter",
    "CertifiedCyclotomicCenterDriver",
    "CertifiedCyclotomicCenterProgram",
    "CertifiedCyclotomicCenterReturn",
    "certified_cyclotomic_center",
    "certified_cyclotomic_center_driver",
    "certified_cyclotomic_center_four_return",
    "certified_cyclotomic_center_program",
    "cyclotomic_four_block_order",
]
