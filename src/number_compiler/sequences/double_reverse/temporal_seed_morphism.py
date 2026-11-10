"""Exact all-digit temporal morphisms on one authenticated 2rev10 seed orbit.

The full-word SLP action is primary.  It is transported together with the
outer modulo-99/198 cyclotomic action, the *punctured* exterior SLP residue,
and pointed center/carry outputs.  Temporal squaring advances the actual
intermediate source root, not a presumed repeat of the first driver's word.

A pointed action cannot be promoted to a source-independent word morphism or
an indefinitely repeating center selector.  In particular, no 1000 period
word is assumed here.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .power import DoubleReverseTerm

from number_compiler.arithmetic.automata.decimal_mod70_word import (
    DecimalMod70WordSummary,
)
from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.pascal_word_moments import (
    PascalWordMoments,
)
from number_compiler.arithmetic.automata.slp_interval import (
    fold_slp_dag,
    fold_slp_interval,
)
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.fields.morphism_core import AffineCocycle
from number_compiler.arithmetic.polynomials.digit_cyclotomic import (
    crt_mod70_from_residues,
)
from number_compiler.resources.ledger import ResourceLedger

from ._temporal_bank_authority import (
    SourceAuthorizedRecord,
    SourceRecordAuthority,
    issue_source_record,
    require_source_arena,
    validate_source_record,
)
from .source_bound_bank import PointedBankSource
from .temporal_center_cyclotomic import (
    band_moore,
    certified_cyclotomic_center_driver,
    cyclotomic_four_block_order,
)
from .temporal_center_selector import CenterDriver, center_return
from .temporal_hashlife import growth_ports
from .temporal_hashlife_types import UncertifiedPointedStencilError
from .temporal_residue_quotient import (
    CertifiedResidueTemporalAction,
    SLPResidues,
    certified_residue_action,
)


@dataclass(frozen=True, slots=True)
class SeedWordFiber:
    """Exact pointed center and independent punctured-exterior SLP folds.

    ``root`` names the complete (possibly compressed) decimal word.  The
    punctured exterior is reduced from *two SLP intervals*, not obtained by
    subtracting the center from a claimed global residue.  Its center may be
    demanded with two indexed SLP reads; no entire word is materialized.
    """

    root: int
    width: int
    center: tuple[int, ...]
    center_band_moore: int | None
    residue99: int
    residue198: int
    exterior99: int
    exterior198: int
    pascal_order: int | None = None
    pascal_levels: tuple[int, ...] = ()
    pascal_bands: tuple[tuple[int, PascalWordMoments], ...] = ()
    mod70: DecimalMod70WordSummary | None = None
    mod70_bands: tuple[tuple[int, DecimalMod70WordSummary], ...] = ()

    @property
    def center_width(self) -> int:
        return len(self.center)

    def __post_init__(self) -> None:
        if (
            type(self.pascal_levels) is not tuple
            or type(self.pascal_bands) is not tuple
        ):
            raise ValueError("Pascal projection metadata must be immutable tuples")
        if not self.pascal_levels:
            if self.pascal_order is not None or self.pascal_bands:
                raise ValueError("empty Pascal projection has unexpected metadata")
        else:
            if (
                type(self.pascal_order) is not int
                or not 0 <= self.pascal_order <= 16
                or any(
                    type(level) is not int or not 1 <= level <= 16
                    for level in self.pascal_levels
                )
                or tuple(sorted(set(self.pascal_levels))) != self.pascal_levels
                or len(self.pascal_bands) != len(self.pascal_levels)
            ):
                raise ValueError("Pascal projection order and levels are invalid")
            for (level, moments), requested in zip(
                self.pascal_bands, self.pascal_levels, strict=True
            ):
                begin, end = _centered_band_cut(self.width, requested)
                if (
                    type(level) is not int
                    or level != requested
                    or type(moments) is not PascalWordMoments
                    or moments.length != end - begin
                    or moments.order != self.pascal_order
                    or moments.modulus != 11
                ):
                    raise ValueError("Pascal band does not match its source projection")
        if type(self.mod70_bands) is not tuple:
            raise TypeError("mod-70 band summaries must be immutable tuples")
        if self.mod70 is None:
            if self.mod70_bands:
                raise ValueError("mod-70 bands lack their demanded whole-word fold")
        else:
            if (
                type(self.mod70) is not DecimalMod70WordSummary
                or self.mod70.length != self.width
            ):
                raise ValueError("mod-70 word summary does not match its source width")
            if len(self.mod70_bands) != len(self.pascal_levels):
                raise ValueError("mod-70 band summaries do not match demanded levels")
            for (level, summary), requested in zip(
                self.mod70_bands, self.pascal_levels, strict=True
            ):
                begin, end = _centered_band_cut(self.width, requested)
                if (
                    type(level) is not int
                    or level != requested
                    or type(summary) is not DecimalMod70WordSummary
                    or summary.length != end - begin
                ):
                    raise ValueError("mod-70 band does not match its source interval")


@dataclass(frozen=True, slots=True)
class _WordFiberSummary:
    """One SLP-node value shared by residue and explicitly demanded channels."""

    residues: SLPResidues
    pascal: PascalWordMoments | None
    mod70: DecimalMod70WordSummary | None

    @classmethod
    def empty(
        cls, pascal_order: int | None, *, mod70_projection: bool
    ) -> _WordFiberSummary:
        pascal = (
            None
            if pascal_order is None
            else PascalWordMoments.empty(pascal_order, modulus=11)
        )
        mod70 = DecimalMod70WordSummary.identity() if mod70_projection else None
        return cls(SLPResidues(0, 0, 0), pascal, mod70)

    @classmethod
    def symbol(
        cls, digit: int, pascal_order: int | None, *, mod70_projection: bool
    ) -> _WordFiberSummary:
        pascal = (
            None
            if pascal_order is None
            else PascalWordMoments.symbol(
                digit,
                int(digit >= 5),
                order=pascal_order,
                modulus=11,
            )
        )
        mod70 = DecimalMod70WordSummary.digit(digit) if mod70_projection else None
        return cls(SLPResidues(1, digit % 99, digit % 198), pascal, mod70)

    def then(self, later: _WordFiberSummary) -> _WordFiberSummary:
        if type(later) is not _WordFiberSummary:
            raise TypeError("word-fiber SLP values have incompatible sorts")
        if (self.pascal is None) != (later.pascal is None):
            raise ValueError("word-fiber SLP values use different Pascal demands")
        if (self.mod70 is None) != (later.mod70 is None):
            raise ValueError("word-fiber SLP values use different mod-70 demands")
        pascal = (
            None
            if self.pascal is None
            else self.pascal.then(_require_pascal(later.pascal))
        )
        mod70 = (
            None if self.mod70 is None else self.mod70.then(_require_mod70(later.mod70))
        )
        return _WordFiberSummary(self.residues.then(later.residues), pascal, mod70)

    def power(self, count: int) -> _WordFiberSummary:
        if type(count) is not int or count < 0:
            raise ValueError("word-fiber SLP repeat count must be nonnegative")
        return _WordFiberSummary(
            self.residues.power(count),
            None if self.pascal is None else self.pascal.power(count),
            None if self.mod70 is None else self.mod70.power(count),
        )


def _centered_band_cut(width: int, level: int) -> tuple[int, int]:
    """MSB-first interval for one nested dyadic center band."""
    if type(width) is not int or width < 1:
        raise ValueError("centered Pascal band needs a positive exact width")
    if type(level) is not int or not 1 <= level <= 16:
        raise ValueError("centered Pascal band level is outside its admitted range")
    scale = 1 << level
    left = width * (scale - 1) // (2 * scale)
    return left, width - left


def _validate_pascal_request(levels: tuple[int, ...], order: int) -> None:
    if (
        type(levels) is not tuple
        or any(type(level) is not int or not 1 <= level <= 16 for level in levels)
        or tuple(sorted(set(levels))) != levels
        or type(order) is not int
        or not 0 <= order <= 16
    ):
        raise ValueError("source Pascal levels/order are outside their admitted range")


def _require_pascal(
    value: PascalWordMoments | None,
) -> PascalWordMoments:
    if type(value) is not PascalWordMoments:
        raise AssertionError("source SLP summary omitted its demanded Pascal moments")
    return value


def _require_mod70(value: DecimalMod70WordSummary | None) -> DecimalMod70WordSummary:
    if type(value) is not DecimalMod70WordSummary:
        raise AssertionError("source SLP summary omitted its demanded mod-70 word")
    return value


def double_reverse_two_tick_mod70_action(
    word: DecimalMod70WordSummary,
) -> AffineCocycle[int]:
    """Return the finite carry law for a canonical nonzero-units word.

    This arithmetic helper does not authenticate the supplied summary or
    authorize a temporal repetition. The issued-source adapter below obtains
    its input from the actual source SLP fold.
    """
    if type(word) is not DecimalMod70WordSummary or word.length == 0:
        raise ValueError("T-squared mod-70 action needs a nonempty source word")
    if word.suffix_digits[-1] == 0:
        raise ValueError("T-squared mod-70 action requires nonzero source units")
    if word.prefix_digits[0] == 0:
        raise ValueError("T-squared mod-70 action requires a canonical source")
    growth = int(word.suffix_digits[-1] >= 5)
    if growth:
        carry_mask_mod70 = crt_mod70_from_residues(word.threshold_mask_mod7, 1)
        multiplier = 40
    else:
        quotient_mod7 = 5 * word.threshold_mask_mod7 % 7
        quotient_units = (
            int(word.suffix_digits[-2] >= 5) if len(word.suffix_digits) >= 2 else 0
        )
        carry_mask_mod70 = crt_mod70_from_residues(quotient_mod7, quotient_units)
        multiplier = 4
    return AffineCocycle(multiplier, (-198 * carry_mask_mod70) % 70)


def word_fiber_from_root(
    arena: LedgerSLPArena,
    ledger: ResourceLedger,
    scratch_owner: int,
    root: int,
    *,
    pascal_levels: tuple[int, ...] = (),
    pascal_order: int = 1,
    mod70_projection: bool = False,
) -> SeedWordFiber:
    """Independent all-digit fiber fold for either powered or exact-fallback roots.

    Unlike a period certificate, an exact finite word root requires no
    border-phase assumption. It still retains the complete SLP and never
    guesses its center from modulo 99 alone.
    """
    if type(root) is not int:
        raise TypeError("word-fiber root must be an exact integer node index")
    if not 0 <= root < len(arena.nodes):
        raise ValueError("word-fiber root is outside the source SLP arena")
    _validate_pascal_request(pascal_levels, pascal_order)
    if type(mod70_projection) is not bool:
        raise TypeError("mod-70 word projection demand must be Boolean")
    width = arena.nodes[root].length
    center_width = 1 if width % 2 else 2
    s = (width - center_width) // 2
    center = tuple(symbol_at(arena, root, s + j) for j in range(center_width))
    summary_identity = _WordFiberSummary.empty(
        pascal_order if pascal_levels else None,
        mod70_projection=mod70_projection,
    )
    # One DAG fold serves the two independent exterior interval reads and the
    # complete-word check.  REPEAT is folded by binary monoid powering.
    bound = len(arena.nodes) + 1
    interval_count = len(pascal_levels) + 2
    pascal_cells = (
        2 * (pascal_order + 1) * (bound + interval_count) if pascal_levels else 0
    )
    mod70_cells = 20 * (bound + interval_count) if mod70_projection else 0
    with ledger.reservation(
        scratch_owner,
        entries=4 * bound
        + interval_count * int(bool(pascal_levels))
        + (2 * bound + interval_count if mod70_projection else 0),
        nodes=12 * bound + pascal_cells + mod70_cells,
    ):
        summaries = fold_slp_dag(
            arena,
            root,
            empty_value=summary_identity,
            terminal_value=lambda d: _WordFiberSummary.symbol(
                d,
                pascal_order if pascal_levels else None,
                mod70_projection=mod70_projection,
            ),
            concatenate=_WordFiberSummary.then,
            repeat=_WordFiberSummary.power,
        )

        def interval(
            begin: int,
            end: int,
            values: dict[int, _WordFiberSummary],
        ) -> _WordFiberSummary:
            return fold_slp_interval(
                arena,
                root,
                begin,
                end,
                identity=summary_identity,
                length=lambda node: arena.nodes[node].length,
                full_value=lambda node, _reverse: values[node],
                compose=_WordFiberSummary.then,
                repeat=_WordFiberSummary.power,
            )

        band_values: list[tuple[int, PascalWordMoments]] = []
        mod70_band_values: list[tuple[int, DecimalMod70WordSummary]] = []
        try:
            left = interval(0, s, summaries)
            right = interval(s + center_width, width, summaries)
            full = summaries[root].residues
            full_mod70 = summaries[root].mod70
            for level in pascal_levels:
                begin, end = _centered_band_cut(width, level)
                band_value = interval(begin, end, summaries)
                if pascal_levels:
                    band_values.append((level, _require_pascal(band_value.pascal)))
                if mod70_projection:
                    mod70_band_values.append((level, _require_mod70(band_value.mod70)))
            pascal_bands = tuple(band_values)
            mod70_bands = tuple(mod70_band_values)
        finally:
            # A retained exception traceback must not retain the complete
            # per-node product fold after its reservation has unwound.
            summaries.clear()
            band_values.clear()
            mod70_band_values.clear()
    # This is the independent all-digit polynomial identity.  The actual
    # source-issued mod-99/198 clock is checked separately by the caller.
    center_value = 0
    for digit in center:
        center_value = 10 * center_value + digit
    exterior99 = (
        left.residues.modulo99 * pow(10, width - s, 99) + right.residues.modulo99
    ) % 99
    exterior198 = (
        left.residues.modulo198 * pow(10, width - s, 198) + right.residues.modulo198
    ) % 198
    if (exterior99 + center_value * pow(10, s, 99)) % 99 != full.modulo99 or (
        exterior198 + center_value * pow(10, s, 198)
    ) % 198 != full.modulo198:
        raise AssertionError("punctured exterior failed whole-word SLP identity")
    return SeedWordFiber(
        root,
        width,
        center,
        band_moore().class_for((center[0], center[1])) if center_width == 2 else None,
        full.modulo99,
        full.modulo198,
        exterior99,
        exterior198,
        pascal_order if pascal_levels else None,
        pascal_levels,
        pascal_bands,
        full_mod70,
        mod70_bands,
    )


def _word_fiber(
    source: PointedBankSource,
    root: int,
    *,
    pascal_levels: tuple[int, ...] = (),
    pascal_order: int = 1,
    mod70_projection: bool = False,
) -> SeedWordFiber:
    return word_fiber_from_root(
        source.arena,
        source.ledger,
        source.scratch_owner,
        root,
        pascal_levels=pascal_levels,
        pascal_order=pascal_order,
        mod70_projection=mod70_projection,
    )


@dataclass(frozen=True, slots=True)
class CertifiedSeedOrbitMorphism(SourceAuthorizedRecord):
    """Source-anchored full-word F**(2*steps) plus outer/inner ring ports.

    The action applies to *one pointed source root*, not every other word
    sharing a residue.  A center driver is published only for a separately
    certified four-physical-step block.  Wider powered blocks keep exact
    source and target SLPs rather than asserting an invented driver period.
    """

    physical_prefix: int
    source_phase: int
    source_root: int
    start_f_steps: int
    steps: int
    first: SeedWordFiber
    last: SeedWordFiber
    phase_in: int
    phase_out: int
    left_births: int
    right_births: int
    residue_action: CertifiedResidueTemporalAction
    four_step_driver: CenterDriver | None = None
    three_odd_centers: tuple[int, int, int] | None = None
    all_depth_period_claim: bool = False

    @property
    def global_four_block_order(self) -> int | None:
        """Necessary scalar order, not an inferred center/word return period."""
        self.validate_source_authority()
        return cyclotomic_four_block_order(self.first.residue99, self.first.residue198)

    @property
    def observed_joint_endpoint_return(self) -> bool:
        """Equality of requested finite observations; no future recurrence."""
        self.validate_source_authority()
        return (
            self.first.center == self.last.center
            and self.first.residue99 == self.last.residue99
            and self.first.residue198 == self.last.residue198
            and self.first.width % 2 == self.last.width % 2
        )

    @property
    def physical_interval(self) -> tuple[int, int]:
        self.validate_source_authority()
        return (
            self.physical_prefix + 2 * self.start_f_steps,
            self.physical_prefix + 2 * (self.start_f_steps + self.steps),
        )

    def validate_source_authority(self) -> SourceRecordAuthority:
        return validate_source_record(self)

    @property
    def pascal_order(self) -> int | None:
        """Demanded finite spatial moment order, if one was explicitly built."""
        self.validate_source_authority()
        return self.first.pascal_order

    @property
    def pascal_levels(self) -> tuple[int, ...]:
        """Demanded nested spatial bands; these do not assert a time period."""
        self.validate_source_authority()
        return self.first.pascal_levels

    def source_t_squared_mod70_affine(self) -> AffineCocycle[int]:
        """Return the exact one-source T² projection when its units permit it.

        This method is deliberately restricted to a morphism beginning at its
        authenticated whole source root.  It does not authorize repeating the
        affine action or applying it to an embedded spatial band.
        """
        authority = self.validate_source_authority()
        if (
            self.start_f_steps != 0
            or authority.root != self.source_root
            or self.first.root != self.source_root
        ):
            raise ValueError("T-squared projection needs the authenticated source root")
        if self.first.mod70 is None:
            raise ValueError(
                "T-squared projection was not demanded in this source fold"
            )
        return double_reverse_two_tick_mod70_action(self.first.mod70)

    def digit_at(self, msd_position: int, *, after: bool = True) -> int:
        """Demand any actual source/target digit from the powered SLP.

        This deliberately uses the exact all-digit word action. Neither a
        projected residue nor a repeating center-driver guess is used to
        fill the unqueried interior digits.
        """
        self.validate_source_authority()
        if type(after) is not bool:
            raise TypeError("word endpoint selection must be Boolean")
        word = self.last if after else self.first
        if type(msd_position) is not int or not 0 <= msd_position < word.width:
            raise IndexError(msd_position)
        arena = require_source_arena(self.validate_source_authority())
        return symbol_at(arena, word.root, msd_position)

    def _same_word_source(self, left: SeedWordFiber, right: SeedWordFiber) -> bool:
        """Compare exact word-source fields, excluding optional diagnostics."""
        return (
            left.root == right.root
            and left.width == right.width
            and left.center == right.center
            and left.center_band_moore == right.center_band_moore
            and left.residue99 == right.residue99
            and left.residue198 == right.residue198
            and left.exterior99 == right.exterior99
            and left.exterior198 == right.exterior198
        )

    def then(self, later: CertifiedSeedOrbitMorphism) -> CertifiedSeedOrbitMorphism:
        """Compose exact adjacent *root-specific* word and residue actions."""
        left = self.validate_source_authority()
        right = later.validate_source_authority()
        if (
            left.arena is not right.arena
            or left.root != right.root
            or left.source_generation != right.source_generation
            or self.source_root != later.source_root
            or self.physical_prefix != later.physical_prefix
            or self.start_f_steps + self.steps != later.start_f_steps
            or not self._same_word_source(self.last, later.first)
            or self.phase_out != later.phase_in
            or self.residue_action.target_mod99 != later.residue_action.source_mod99
            or self.residue_action.target_mod198 != later.residue_action.source_mod198
        ):
            raise ValueError("seed temporal morphisms lack exact source/root adjacency")
        # Independent source clock for the *full* block, rather than treating
        # any suffix as a repeated driver program.
        residue = certified_residue_action(
            phase=self.phase_in,
            width=self.first.width,
            duration=2 * (self.steps + later.steps),
            source_mod99=self.first.residue99,
            source_mod198=self.first.residue198,
        )
        if (
            residue.target_mod99 != later.last.residue99
            or residue.target_mod198 != later.last.residue198
            or residue.width_out != later.last.width
            or residue.growth
            != self.left_births
            + self.right_births
            + later.left_births
            + later.right_births
            or residue.skew
            != self.residue_action.skew
            + later.residue_action.skew
            + later.residue_action.duration * self.residue_action.growth
        ):
            raise AssertionError("outer cyclotomic power failed exact SLP composition")
        return issue_source_record(
            CertifiedSeedOrbitMorphism(
                self.physical_prefix,
                self.source_phase,
                self.source_root,
                self.start_f_steps,
                self.steps + later.steps,
                self.first,
                later.last,
                self.phase_in,
                later.phase_out,
                self.left_births + later.left_births,
                self.right_births + later.right_births,
                residue,
            ),
            require_source_arena(left),
            left.root,
            source_generation=left.source_generation,
        )


def certified_seed_orbit_morphism(
    source: PointedBankSource,
    *,
    steps: int,
    start_f_steps: int = 0,
    known_previous: CertifiedSeedOrbitMorphism | None = None,
    completed_term: DoubleReverseTerm | None = None,
    pascal_levels: tuple[int, ...] = (),
    pascal_order: int = 1,
    mod70_projection: bool = False,
) -> CertifiedSeedOrbitMorphism:
    """Lift an exact Hashlife word power into the joint temporal fiber.

    ``start_f_steps`` is relative to the owner-issued prefix cursor. An
    issued preceding morphism can provide the exact intermediate SLP root.
    An optional owner-authenticated complete scheduler endpoint transports
    the same deterministic source to its target without re-powering it.
    A freely supplied center, exterior fiber or root is never proof.
    """
    source.validate(require_issued_cursor=source.f_steps > 0)
    _validate_pascal_request(pascal_levels, pascal_order)
    if type(mod70_projection) is not bool:
        raise TypeError("mod-70 word projection demand must be Boolean")
    if (
        type(steps) is not int
        or steps <= 0
        or type(start_f_steps) is not int
        or start_f_steps < 0
        or start_f_steps + steps > source.f_steps
    ):
        raise UncertifiedPointedStencilError(
            "temporal word action exceeds the seed-certified future horizon"
        )
    if completed_term is not None:
        # A complete scheduler image is proof of the endpoint only for this
        # exact issued seed/source cursor. Never accept an arbitrary SLP root,
        # independently supplied residue, or matching border occurrence.
        completed_term.check_open()
        if (
            completed_term.source_arena is not source.arena
            or completed_term.temporal_engine is not source.engine
            or completed_term.source_root != source.engine.source_root
            or completed_term.generation != source.physical_prefix + 2 * steps
            or start_f_steps != 0
            or known_previous is not None
        ):
            raise ValueError("completed image cannot transport this source/phase")
    engine = source.engine
    if known_previous is not None:
        authority = known_previous.validate_source_authority()
        if (
            authority.arena is not source.arena
            or authority.root != source.root
            or authority.source_generation != source.physical_prefix
            or known_previous.start_f_steps + known_previous.steps != start_f_steps
            or known_previous.source_root != source.root
            or known_previous.source_phase != source.phase
        ):
            raise ValueError("previous temporal fiber has no source-issued lineage")
        known_first = known_previous.last
        # The preceding action is already source-authorized. Different dyadic
        # factorizations of the same SLP word can have different root IDs;
        # squaring MUST continue from the actual preceding root, not silently
        # substitute the separately published direct-power root.
        start_root = known_first.root
        phase = (source.phase + 2 * start_f_steps) % 4
        if engine.certify(
            start_root
        ) != phase or known_first.width != source.width_in + sum(
            growth_ports(source.phase, start_f_steps)
        ):
            raise ValueError("previous pointed word is incompatible with source clock")
    elif start_f_steps:
        known_first = None
        prior = engine.advance_action(source.root, start_f_steps, source.phase)
        engine.validate_action(prior)
        start_root = engine.root_of(prior.target)
        phase = prior.phase_out
    else:
        known_first = None
        start_root = source.root
        phase = source.phase
    if known_first is None or (
        known_first.pascal_levels != pascal_levels
        or known_first.pascal_order != (pascal_order if pascal_levels else None)
        or (known_first.mod70 is not None) != mod70_projection
    ):
        first = _word_fiber(
            source,
            start_root,
            pascal_levels=pascal_levels,
            pascal_order=pascal_order,
            mod70_projection=mod70_projection,
        )
    else:
        first = known_first
    if first.root != start_root or first.width != source.arena.nodes[start_root].length:
        raise ValueError("pointed input fiber is not the actual seed-orbit root")
    if completed_term is None:
        action = engine.advance_action(start_root, steps, phase)
        engine.validate_action(action)
        target_root = engine.root_of(action.target)
        phase_out = action.phase_out
        left_births, right_births = action.left_births, action.right_births
    else:
        # Transport the already scheduler-issued T**N endpoint through the
        # independently issued T**prefix cursor. Determinism of the exact
        # source action proves that its remaining T**(2*steps) suffix has the
        # same endpoint. This is source-to-class transport, NOT a guessed
        # repeated Laurent driver or an unvalidated root substitution.
        completed_target = completed_term.issued_completed_endpoint_root()
        if completed_target is None:
            raise ValueError("a complete scheduler image has not been issued")
        target_root = completed_target
        phase_out = (phase + 2 * steps) % 4
        left_births, right_births = growth_ports(phase, steps)
        if (
            engine.certify(target_root) != phase_out
            or source.arena.nodes[target_root].length
            != first.width + left_births + right_births
        ):
            raise AssertionError("scheduler word fails issued prefix transport")
    last = _word_fiber(
        source,
        target_root,
        pascal_levels=pascal_levels,
        pascal_order=pascal_order,
        mod70_projection=mod70_projection,
    )
    residue = certified_residue_action(
        phase=phase,
        width=first.width,
        duration=2 * steps,
        source_mod99=first.residue99,
        source_mod198=first.residue198,
    )
    if (
        residue.target_mod99 != last.residue99
        or residue.target_mod198 != last.residue198
        or residue.width_out != last.width
        or residue.growth != left_births + right_births
    ):
        raise AssertionError(
            "all-digit Hashlife power disagrees with outer cyclotomic ring"
        )
    driver: CenterDriver | None = None
    odd: tuple[int, int, int] | None = None
    if steps == 2 and len(first.center) == 2 and len(last.center) == 2 and phase == 0:
        witness = certified_cyclotomic_center_driver(
            source, start_f_steps=start_f_steps
        )
        if (
            witness.initial_pair != first.center
            or witness.next_pair != last.center
            or witness.source_mod99 != first.residue99
            or witness.target_mod99 != last.residue99
            or witness.source_mod198 != first.residue198
            or witness.target_mod198 != last.residue198
        ):
            raise AssertionError(
                "source-certified center driver disagrees with word power"
            )
        if center_return(witness.initial_pair, witness.driver).next_pair != last.center:
            raise AssertionError("source carry driver did not reproduce target center")
        driver, odd = witness.driver, witness.odd_centers
    return issue_source_record(
        CertifiedSeedOrbitMorphism(
            source.physical_prefix,
            source.phase,
            source.root,
            start_f_steps,
            steps,
            first,
            last,
            phase,
            phase_out,
            left_births,
            right_births,
            residue,
            driver,
            odd,
        ),
        source.arena,
        source.root,
        source_generation=source.physical_prefix,
    )


def square_seed_orbit_morphism(
    source: PointedBankSource,
    first: CertifiedSeedOrbitMorphism,
) -> CertifiedSeedOrbitMorphism:
    """Square time using a *new* source-certified successor-root word action.

    The second half is evaluated from the actual first-half endpoint SLP;
    no period, repeated carry word, or root-independent morphism is assumed.
    """
    source.validate(require_issued_cursor=True)
    owner = first.validate_source_authority()
    if (
        owner.arena is not source.arena
        or owner.root != source.root
        or owner.source_generation != source.physical_prefix
        or first.physical_prefix != source.physical_prefix
        or first.source_root != source.root
        or first.source_phase != source.phase
        or first.start_f_steps + 2 * first.steps > source.f_steps
    ):
        raise UncertifiedPointedStencilError(
            "no source-certified successor root for this temporal square"
        )
    second = certified_seed_orbit_morphism(
        source,
        start_f_steps=first.start_f_steps + first.steps,
        steps=first.steps,
        known_previous=first,
        pascal_levels=first.first.pascal_levels,
        pascal_order=(
            first.first.pascal_order if first.first.pascal_order is not None else 1
        ),
        mod70_projection=first.first.mod70 is not None,
    )
    return first.then(second)


__all__ = [
    "CertifiedSeedOrbitMorphism",
    "SeedWordFiber",
    "certified_seed_orbit_morphism",
    "double_reverse_two_tick_mod70_action",
    "square_seed_orbit_morphism",
    "word_fiber_from_root",
]
