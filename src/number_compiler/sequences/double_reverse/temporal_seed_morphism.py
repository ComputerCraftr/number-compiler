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

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_interval import (
    fold_slp_dag,
    fold_slp_interval,
)
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.resources.ledger import ResourceLedger

from ._temporal_bank_authority import (
    _SourceAuthority,
    _SourceAuthorizedRecord,
    issue_source_record,
    require_source_arena,
    validate_source_record,
)
from .source_bound_bank import PointedBankSource
from .temporal_center_cyclotomic import (
    _band_moore,
    certified_cyclotomic_center_driver,
    cyclotomic_four_block_order,
)
from .temporal_center_selector import CenterDriver, center_return
from .temporal_hashlife import growth_ports
from .temporal_hashlife_types import UncertifiedPointedStencilError
from .temporal_residue_quotient import (
    CertifiedResidueTemporalAction,
    _SLPResidues,
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

    @property
    def center_width(self) -> int:
        return len(self.center)


def word_fiber_from_root(
    arena: LedgerSLPArena,
    ledger: ResourceLedger,
    scratch_owner: int,
    root: int,
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
    width = arena.nodes[root].length
    center_width = 1 if width % 2 else 2
    s = (width - center_width) // 2
    center = tuple(symbol_at(arena, root, s + j) for j in range(center_width))
    zero = _SLPResidues(0, 0, 0)
    # One DAG fold serves the two independent exterior interval reads and the
    # complete-word check.  REPEAT is folded by binary monoid powering.
    bound = len(arena.nodes) + 1
    with ledger.reservation(scratch_owner, entries=4 * bound, nodes=12 * bound):
        summaries = fold_slp_dag(
            arena,
            root,
            empty_value=zero,
            terminal_value=lambda d: _SLPResidues(1, d % 99, d % 198),
            concatenate=lambda left, right: left.then(right),
            repeat=lambda value, count: value.power(count),
        )

        def interval(
            begin: int,
            end: int,
            values: dict[int, _SLPResidues],
        ) -> _SLPResidues:
            return fold_slp_interval(
                arena,
                root,
                begin,
                end,
                identity=zero,
                length=lambda node: arena.nodes[node].length,
                full_value=lambda node, _reverse: values[node],
                compose=lambda left, right: left.then(right),
                repeat=lambda value, count: value.power(count),
            )

        left = interval(0, s, summaries)
        right = interval(s + center_width, width, summaries)
        full = summaries[root]
        del summaries
    # This is the independent all-digit polynomial identity.  The actual
    # source-issued mod-99/198 clock is checked separately by the caller.
    center_value = 0
    for digit in center:
        center_value = 10 * center_value + digit
    exterior99 = (left.modulo99 * pow(10, width - s, 99) + right.modulo99) % 99
    exterior198 = (left.modulo198 * pow(10, width - s, 198) + right.modulo198) % 198
    if (exterior99 + center_value * pow(10, s, 99)) % 99 != full.modulo99 or (
        exterior198 + center_value * pow(10, s, 198)
    ) % 198 != full.modulo198:
        raise AssertionError("punctured exterior failed whole-word SLP identity")
    return SeedWordFiber(
        root,
        width,
        center,
        _band_moore().class_for((center[0], center[1])) if center_width == 2 else None,
        full.modulo99,
        full.modulo198,
        exterior99,
        exterior198,
    )


def _word_fiber(source: PointedBankSource, root: int) -> SeedWordFiber:
    return word_fiber_from_root(source.arena, source.ledger, source.scratch_owner, root)


@dataclass(frozen=True, slots=True)
class CertifiedSeedOrbitMorphism(_SourceAuthorizedRecord):
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

    def validate_source_authority(self) -> _SourceAuthority:
        return validate_source_record(self)

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
            or self.last != later.first
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
) -> CertifiedSeedOrbitMorphism:
    """Lift an exact Hashlife word power into the joint temporal fiber.

    ``start_f_steps`` is relative to the owner-issued prefix cursor.  An
    issued preceding morphism can provide the exact intermediate SLP root;
    a freely supplied center or exterior fiber is never accepted as proof.
    """
    source.validate(require_issued_cursor=source.f_steps > 0)
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
    first = _word_fiber(source, start_root) if known_first is None else known_first
    if first.root != start_root or first.width != source.arena.nodes[start_root].length:
        raise ValueError("pointed input fiber is not the actual seed-orbit root")
    action = engine.advance_action(start_root, steps, phase)
    engine.validate_action(action)
    target_root = engine.root_of(action.target)
    last = _word_fiber(source, target_root)
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
        or residue.growth != action.left_births + action.right_births
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
            action.phase_in,
            action.phase_out,
            action.left_births,
            action.right_births,
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
    )
    return first.then(second)


__all__ = [
    "CertifiedSeedOrbitMorphism",
    "SeedWordFiber",
    "certified_seed_orbit_morphism",
    "square_seed_orbit_morphism",
    "word_fiber_from_root",
]
