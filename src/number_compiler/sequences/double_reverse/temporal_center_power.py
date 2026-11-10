"""Finite source-authenticated center affine and mod-11 projections."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from ._temporal_bank_authority import (
    SourceAuthorizedRecord,
    SourceRecordAuthority,
    issue_source_record,
    require_source_arena,
    validate_source_record,
)
from .temporal_center_selector import CenterForcingPower
from .temporal_hashlife import PHYSICAL_GROWTH_CYCLES, growth_ports
from .temporal_residue_quotient import (
    certified_residue_action,
    decimal_residues_from_slp,
)

if TYPE_CHECKING:
    from .source_bound_bank import PointedBankSource


def centered_half_combination_mod11(
    width: int,
    center: tuple[int, ...],
    global_mod99: int,
) -> tuple[str, int]:
    """Project overlapping centered halves from one global clock.

    For a word of width 2h, the residue is a-b = (-1)^h X (mod 11).
    For width 2h+1, the overlap contributes the center digit c and
    a+b = c + (-1)^h X (mod 11). Neither half is materialized.
    """
    if (
        type(width) is not int
        or width < 2
        or type(global_mod99) is not int
        or not 0 <= global_mod99 < 99
        or type(center) is not tuple
        or len(center) != (1 if width % 2 else 2)
        or any(type(d) is not int or d not in range(10) for d in center)
    ):
        raise ValueError("centered-half clock needs actual width, center and mod-99")
    value = (global_mod99 if (width // 2) % 2 == 0 else -global_mod99) % 11
    if width % 2:
        return "sum", (value + center[0]) % 11
    return "difference", value


@dataclass(frozen=True, slots=True)
class CertifiedCyclotomicCenterPower(SourceAuthorizedRecord):
    """Pointed endpoint projection of k ACTUAL consecutive four-step blocks.

    The forcing aggregate is derived without building or replaying a driver
    word: its mod-5 and parity harmonics telescope under the center stencil.
    Pointed Hashlife authenticates both actual endpoints. This certifies a
    finite interval only, not a freely repeatable driver or all-future period.
    """

    physical_prefix: int
    start_f_steps: int
    four_step_blocks: int
    start_width: int
    final_width: int
    initial_pair: tuple[int, ...]
    final_pair: tuple[int, ...]
    forcing: CenterForcingPower
    source_mod99: int
    final_mod99: int
    source_mod198: int
    final_mod198: int

    def validate_source_authority(self) -> SourceRecordAuthority:
        return validate_source_record(self)

    @property
    def center_pair_returns(self) -> bool:
        self.validate_source_authority()
        return self.initial_pair == self.final_pair

    @property
    def centered_half_clock_mod11(self) -> dict[str, object]:
        """Exact mod-11 half harmonic, projected without expanding either half.

        Even-width half DIFFERENCE transports homogeneously by 16^k.
        Odd-width overlapping half SUM has only a center-derived innovation.
        This is a globally valid congruence, not a local-carry-period proof.
        """
        self.validate_source_authority()
        mode, before = centered_half_combination_mod11(
            self.start_width,
            self.initial_pair,
            self.source_mod99,
        )
        end_mode, after = centered_half_combination_mod11(
            self.final_width,
            self.final_pair,
            self.final_mod99,
        )
        if end_mode != mode:
            raise AssertionError("powered half alignment changed width parity")
        multiplier = pow(16, self.four_step_blocks, 11)
        innovation = (after - multiplier * before) % 11
        if mode == "difference" and innovation:
            raise AssertionError(
                "even centered-half clock lost its exact 16^k transport"
            )
        return {
            "mode": mode,
            "source_mod11": before,
            "target_mod11": after,
            "multiplier_mod11": multiplier,
            "center_forcing_mod11": innovation,
        }

    def then(
        self, later: CertifiedCyclotomicCenterPower
    ) -> CertifiedCyclotomicCenterPower:
        a = self.validate_source_authority()
        b = later.validate_source_authority()
        if (
            a.arena is not b.arena
            or a.root != b.root
            or a.source_generation != b.source_generation
            or self.physical_prefix != later.physical_prefix
            or self.start_f_steps + 2 * self.four_step_blocks != later.start_f_steps
            or self.final_width != later.start_width
            or self.final_pair != later.initial_pair
            or self.final_mod99 != later.source_mod99
            or self.final_mod198 != later.source_mod198
        ):
            raise ValueError(
                "powered center cocycle needs exact source/time/clock seam"
            )
        forcing = self.forcing.then(later.forcing)
        record = CertifiedCyclotomicCenterPower(
            self.physical_prefix,
            self.start_f_steps,
            self.four_step_blocks + later.four_step_blocks,
            self.start_width,
            later.final_width,
            self.initial_pair,
            later.final_pair,
            forcing,
            self.source_mod99,
            later.final_mod99,
            self.source_mod198,
            later.final_mod198,
        )
        return issue_source_record(
            record,
            require_source_arena(a),
            a.root,
            source_generation=a.source_generation,
        )


def certified_cyclotomic_center_power(
    source: PointedBankSource,
    *,
    start_f_steps: int = 0,
    four_step_blocks: int = 1,
) -> CertifiedCyclotomicCenterPower:
    """Evaluate a finite center harmonic from authenticated source endpoints.

    Does not scan k center drivers or postulate periodic forcing. The
    ``center_return`` identity proves that their sum modulo five telescopes
    to (last_right-first_right) modulo five, while the final forcing parity
    equals the final right-center parity. The existing owner authenticates
    the finite source roots and exact mod-99/198 action. This avoids a driver
    word; it makes no claim about the cost of pointed source traversal.
    """
    source.validate(require_issued_cursor=source.f_steps > 0)
    if (
        type(start_f_steps) is not int
        or start_f_steps < 0
        or type(four_step_blocks) is not int
        or four_step_blocks < 1
    ):
        raise ValueError(
            "powered center requires nonnegative start and positive block count"
        )
    finish = start_f_steps + 2 * four_step_blocks
    if finish > source.f_steps:
        raise ValueError("center forcing horizon exceeds the issued source cursor")
    phase = (source.phase + 2 * start_f_steps) % 4
    start_width = source.width_in + sum(growth_ports(source.phase, start_f_steps))
    if PHYSICAL_GROWTH_CYCLES[phase] != (1, 0, 0, 1):
        raise ValueError("center forcing needs certified 1,0,0,1 width clock")
    center_width = 2 if start_width % 2 == 0 else 1
    end_width = source.width_in + sum(growth_ports(source.phase, finish))
    if end_width - start_width != 2 * four_step_blocks:
        raise AssertionError("powered center phase lost its growth displacement")
    initial = source.engine.pointed_window(
        source.root,
        start_f_steps,
        source.phase,
        (start_width - center_width) // 2,
        center_width,
    )
    final = source.engine.pointed_window(
        source.root,
        finish,
        source.phase,
        (end_width - center_width) // 2,
        center_width,
    )
    if any(type(d) is not int or d not in range(10) for d in (*initial, *final)):
        raise AssertionError("powered source did not produce center decimal digits")
    forcing = CenterForcingPower.from_endpoints(
        initial[-1], final[-1], four_step_blocks
    )
    if forcing.harmonic_return != forcing.right_returns:
        raise AssertionError(
            "source-issued center violates the harmonic return identity"
        )
    if four_step_blocks == 1 and center_width == 2:
        # The existing pointed driver owns all three center-facing carries
        # and the final F5 seam. Do not issue a second carry observer.
        from .temporal_center_cyclotomic import (
            certified_cyclotomic_center_driver,
        )

        driver = certified_cyclotomic_center_driver(source, start_f_steps=start_f_steps)
        if (
            driver.initial_pair != initial
            or driver.next_pair != final
            or driver.right_center_forcing != forcing
        ):
            raise AssertionError("powered center disagrees with physical carry ports")
    elif four_step_blocks == 1:
        # Odd-width center: two SOURCE-pointed even rows recover the same
        # diagonal carry field. The intermediate odd row is a deterministic
        # local 2*reverse digit action, not a separately issued inlet tape.
        h = start_width // 2
        left0, center0, right0 = source.engine.pointed_window(
            source.root,
            start_f_steps,
            source.phase,
            h - 1,
            3,
        )
        left2, center2, right2 = source.engine.pointed_window(
            source.root,
            start_f_steps + 1,
            source.phase,
            h - 1,
            3,
        )
        if center0 != initial[0]:
            raise AssertionError("odd pointed source center changed coordinates")
        first_center = (2 * right0 + int(center0 >= 5)) % 10
        first_other = (2 * center0 + int(left0 >= 5)) % 10
        if center2 != (2 * first_other + int(first_center >= 5)) % 10:
            raise AssertionError(
                "odd center source violates the exact two-sided stencil"
            )
        third_center = (2 * right2 + int(center2 >= 5)) % 10
        actual_forcing = (
            8 * int(left0 >= 5)
            + 4 * int(first_center >= 5)
            + 2 * int(left2 >= 5)
            + int(third_center >= 5)
        )
        if (
            final[0] != (16 * center0 + actual_forcing) % 10
            or forcing.weighted_mod10 != actual_forcing % 10
        ):
            raise AssertionError("odd-width center forcing lost its diagonal ports")
    residue99, residue198 = decimal_residues_from_slp(
        source.arena,
        source.root,
        ledger=source.ledger,
        scratch_owner=source.scratch_owner,
    )
    before = certified_residue_action(
        phase=source.phase,
        width=source.width_in,
        duration=2 * start_f_steps,
        source_mod99=residue99,
        source_mod198=residue198,
    )
    after = certified_residue_action(
        phase=source.phase,
        width=source.width_in,
        duration=2 * finish,
        source_mod99=residue99,
        source_mod198=residue198,
    )
    if before.width_out != start_width or after.width_out != end_width:
        raise AssertionError("center growth clock disagrees with powered global clock")
    # A cheap, independently derived half-residue compatibility guard. Its
    # signed even-width half difference is autonomous modulo 11; odd-width
    # half sum is forced solely by the already-pointed center endpoints.
    mode_before, comb_before = centered_half_combination_mod11(
        start_width,
        initial,
        before.target_mod99,
    )
    mode_after, comb_after = centered_half_combination_mod11(
        end_width,
        final,
        after.target_mod99,
    )
    if mode_before != mode_after or (
        mode_before == "difference"
        and comb_after != pow(16, four_step_blocks, 11) * comb_before % 11
    ):
        raise AssertionError("center/global clock failed joined mod-11 half harmonic")
    return issue_source_record(
        CertifiedCyclotomicCenterPower(
            source.physical_prefix,
            start_f_steps,
            four_step_blocks,
            start_width,
            end_width,
            initial,
            final,
            forcing,
            before.target_mod99,
            after.target_mod99,
            before.target_mod198,
            after.target_mod198,
        ),
        source.arena,
        source.root,
        source_generation=source.physical_prefix,
    )


__all__ = [
    "CertifiedCyclotomicCenterPower",
    "CenterForcingPower",
    "certified_cyclotomic_center_power",
    "centered_half_combination_mod11",
]
