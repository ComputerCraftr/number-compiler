"""Source-independent physical-Collatz block powering.

The physical map

    C(n) = 3*n+1  (n odd)
           n/2    (n even)

is a finite two-sided digit transducer on an LSD-first binary tape:

* odd ``3*n+1`` uses a finite LSD->MSD state containing the previous input bit
  and one carry bit;
* even ``n/2`` is a one-cell structural right-context lookup;
* the first input bit selects the phase and that phase is propagated in the
  left boundary state;
* blank padding is a third alphabet symbol and is never part of semantic digit
  content.

The atom and its compatibility power descriptor are source-independent.
Term observations use the admitted physical source-image constructor, whose
balanced low-residue leaves still perform source-dependent branch discovery.
Descriptor construction alone is not evidence of a cheap observed endpoint.
"""

from __future__ import annotations

from collections.abc import Iterator, MutableMapping
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import (
    BlockEffect,
)
from number_compiler.arithmetic.contracts.block_power_types import BlockPower
from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
    source_reads_only,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ExactSource,
)
from number_compiler.arithmetic.fields.affine_width import nonnegative_affine_width
from number_compiler.arithmetic.fields.radix import (
    digits_lsd,
    pair_field_descriptor_bits,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.projection.source_audit import (
    RadixProjectionAuditSource,
    RadixProjectionSourceAuditor,
)
from number_compiler.resources.ledger import ResourceLedger, ResourceScope
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.output_stream_metrics import (
    initialize_output_stream_metrics,
    measured_output_stream,
)
from number_compiler.sequences.collatz.physical_block_effect import (
    CollatzPhysicalBlockEffect,
)
from number_compiler.sequences.collatz.radix_source_api import (
    ExteriorRadixCoordinate as _ExteriorRadixCoordinate,
)
from number_compiler.sequences.collatz.radix_source_api import (
    admitted_radix_digit as _admitted_radix_digit_impl,
)
from number_compiler.sequences.collatz.radix_source_api import (
    observe_radix_symbol,
    source_radix_application,
)

if TYPE_CHECKING:
    from number_compiler.projection.lazy_radix import RadixProjection
    from number_compiler.resources.collatz_power_metrics import (
        CollatzPhysicalBlockMetrics,
    )
    from number_compiler.resources.hashlife_behavior_metrics import (
        HashLifeBehaviorMetrics,
    )
    from number_compiler.sequences.collatz.clock_observers import SArithmeticClock
    from number_compiler.sequences.collatz.diagonal_carry_action import (
        CollatzDiagonalSeam,
    )
    from number_compiler.sequences.collatz.joint_temporal_action import (
        CollatzAccumulatorObservation,
    )
    from number_compiler.sequences.collatz.physical_images import (
        CollatzPhysicalImageWorkspace,
        CollatzTermAuditSnapshot,
    )
    from number_compiler.sequences.collatz.tape_width import CollatzTapeWidthSummary
    from number_compiler.sequences.collatz.temporal_source_morphism import (
        CertifiedCollatzRootMorphism,
    )
    from number_compiler.sequences.collatz.weighted_right_congruence import (
        CollatzDoubleWeight,
    )


class PoweredCollatzTerm(RadixProjectionSourceAuditor):
    """Exact physical Collatz nth state using only the powered block fast path."""

    @property
    def resource_ledger(self) -> ResourceLedger:
        """Read the resource owner, including for closed-state inspection."""
        return self._ledger

    seed_digits: tuple[int, ...]

    __slots__ = (
        "__weakref__",
        "_active_width",
        "_compiler",
        "_effect",
        "_innovation_tape_demanded",
        "_innovation_tape_modulus",
        "_joint_cocycle_demanded",
        "_ledger",
        "_max_cache_entries",
        "_max_context_nodes",
        "_microblocks",
        "_point_program",
        "_power",
        "_radix_projections",
        "_shared_cache",
        "_source_construction",
        "_width_bound",
        "_width_spine_demanded",
        "_workspace",
        "_workspace_binding",
        "compose_operations",
        "seed",
        "seed_digits",
        "steps",
        "syntax_depth_bound",
    )

    def __init__(
        self,
        seed: int,
        steps: int,
        *,
        max_context_nodes: int | None = None,
        max_cache_entries: int | None = None,
        shared_cache: bool = True,
    ) -> None:
        if type(shared_cache) is not bool:
            raise TypeError("shared cache flag must be Boolean")
        self._shared_cache = shared_cache
        seed = require_integer(seed, "seed", 1)
        steps = require_integer(steps, "steps", 0)
        self._ledger = ResourceLedger(max_context_nodes, max_cache_entries)
        initialize_output_stream_metrics(self._ledger, "collatz_output_stream")
        for suffix in (
            "requests",
            "emitted_digits",
            "operand_bits",
            "failures",
        ):
            self._ledger.bump(f"collatz_radix_conversion_{suffix}", 0)
        self._ledger.bump(_shared_keys.TEMPORAL_POINT_REQUESTS, 0)
        self._ledger.bump(_shared_keys.TEMPORAL_LENGTH_REQUESTS, 0)
        self.seed = seed
        self.steps = steps
        self.seed_digits: tuple[int, ...] = tuple(map(int, digits_lsd(seed, 2)))
        pairs, remainder = divmod(steps, 2)
        pair_growth = (19 * pairs + 31) // 32
        bound = (
            min(
                len(self.seed_digits) + pairs,
                (seed + 2).bit_length() + pair_growth,
            )
            + 2 * remainder
            + 2
        )
        self._width_bound = (seed, steps, bound)
        self._ledger.bump(_collatz_keys.COLLATZ_WIDTH_BOUND_CONSTRUCTIONS)
        self._ledger.bump(
            _collatz_keys.COLLATZ_WIDTH_BOUND_OPERAND_BITS, seed.bit_length() + 2
        )
        self._source_construction = OriginalSourceConstruction(
            ExactSource(self.seed_digits, 2, blank=2, extent=bound, alphabet_size=2),
        )
        self._ledger.register_execution_root(self)
        from number_compiler.sequences.collatz.tile_family_hooks import (
            collatz_runtime_tile_hooks,
        )

        self._compiler = LazyCompiler(
            self._ledger,
            family_hooks=collatz_runtime_tile_hooks(),
        )
        self._max_context_nodes = max_context_nodes
        self._max_cache_entries = max_cache_entries
        self._workspace: CollatzPhysicalImageWorkspace | None = None
        self._workspace_binding: (
            tuple[object, object, object, bool, bool, bool, int | None] | None
        ) = None
        self._width_spine_demanded = False
        self._joint_cocycle_demanded = False
        self._innovation_tape_demanded = False
        self._innovation_tape_modulus: int | None = None
        radix_owner = self._ledger.register(
            "radix-applications", "application_index", ResourceScope.INDEX_OWNED
        )
        self._radix_projections: MutableMapping[int, RadixProjection] = (
            self._ledger.make_dict(radix_owner)
        )
        self._active_width: int | None = None
        from number_compiler.projection.microblock_cache import MicroblockCache

        self._microblocks = MicroblockCache(
            self._ledger,
            self._compiler.token,
            self._compiler.resolve,
        )
        self._power: BlockPower | None = None
        self._point_program: ActionProgramID | None = None
        self._effect: BlockEffect | None = None
        self.compose_operations = 0
        self.syntax_depth_bound = 0

    def audit_snapshot(self) -> CollatzTermAuditSnapshot:
        from number_compiler.sequences.collatz.physical_images import (
            CollatzTermAuditSnapshot,
        )

        return CollatzTermAuditSnapshot(
            self._ledger,
            self._workspace,
            self._microblocks.audit_snapshot(),
        )

    def radix_projection_audit_source(
        self, ledger: ResourceLedger
    ) -> RadixProjectionAuditSource | None:
        if type(self) is not PoweredCollatzTerm or self._ledger is not ledger:
            return None
        return RadixProjectionAuditSource(
            self,
            self._source_construction.source,
            self.steps,
            self.seed_digits,
            self._radix_projections,
        )

    @property
    def shared_cache(self) -> bool:
        """Cache-sharing policy admitted for this exact powered term."""
        return self._shared_cache

    @property
    def max_context_nodes(self) -> int | None:
        """Caller node limit bound to this term's resource ledger."""
        return self._max_context_nodes

    @property
    def max_cache_entries(self) -> int | None:
        """Caller cache-entry limit bound to this term's resource ledger."""
        return self._max_cache_entries

    @property
    def original_source_construction(self) -> OriginalSourceConstruction:
        """Return the immutable authority for the caller-supplied source."""
        self._source_construction.validate_source()
        return self._source_construction

    def radix_application(self, radix: int, width: int) -> RadixProjection:
        """Get or create this term's accounted source-bound radix application."""
        return source_radix_application(
            radix, width, self._ledger, self._radix_projections, self._microblocks
        )

    @property
    def published_width_summary(self) -> CollatzTapeWidthSummary | None:
        return None if self._workspace is None else self._workspace.tape_width_summary

    def _compile_compatibility_descriptor(self) -> None:
        """Demand the public block descriptor without using it as an executor."""
        if self.steps == 0 or self._power is not None:
            return
        from number_compiler.sequences.collatz.compilation import (
            compile_collatz_physical_power,
        )

        power = compile_collatz_physical_power(self._compiler, self.steps)
        if power.root is None:
            raise AssertionError("positive Collatz exponent without powered effect")
        self._power = power
        self._effect = power.root
        self.compose_operations = power.compose_operations
        self.syntax_depth_bound = power.syntax_depth

    @property
    def power(self) -> BlockPower | None:
        self._compile_compatibility_descriptor()
        return self._power

    @property
    def effect(self) -> BlockEffect | None:
        self._compile_compatibility_descriptor()
        return self._effect

    @property
    def maximum_width(self) -> int:
        # For every two physical ticks, ``y + 2 <= 3 * (x + 2) / 2`` whether
        # the first tick is odd or even.  Also ``(3/2)**32 < 2**19``.  The
        # resulting rational exponent bound is exact integer metadata: it
        # avoids both materializing ``3**pairs`` and allocating the much looser
        # half-step padding that used to dominate cold point observations.
        # Compute the source-sized addition once at admission, not once per
        # emitted point. Preserve the original source/action binding on reuse.
        seed, steps, bound = self._width_bound
        if (
            self.seed != seed
            or self.steps != steps
            or bound != self._source_construction.source.extent
        ):
            raise ValueError("Collatz width bound belongs to another source/action")
        return bound

    @property
    def operator_nodes(self) -> int:
        # Compilation already froze this structural count in ``BlockPower``.
        # Re-walking the live effect here can populate canonical composition
        # interners after a metrics snapshot, making reporting mutate the very
        # counters it reports.
        return 0 if self._power is None else int(self._power.operator_nodes)

    def source_image(self) -> CollatzPhysicalImageWorkspace:
        from number_compiler.sequences.collatz.physical_images import (
            COLLATZ_PHYSICAL_LAW,
            CollatzPhysicalImageWorkspace,
        )

        workspace = self._workspace
        if workspace is None:
            workspace = CollatzPhysicalImageWorkspace(
                self._ledger,
                self.seed,
                self.steps,
                retain_chronology=False,
                shared_cache=self._shared_cache,
                include_width_spine=self._width_spine_demanded,
                include_joint_cocycle=self._joint_cocycle_demanded,
                include_innovation_tape=self._innovation_tape_demanded,
                innovation_modulus=self._innovation_tape_modulus,
            )
            self._workspace_binding = (
                workspace.root_source,
                workspace.root_action,
                workspace.root_payload,
                *workspace.demand_configuration,
            )
            self._workspace = workspace
        if (
            type(workspace) is not CollatzPhysicalImageWorkspace
            or workspace.ledger is not self._ledger
            or workspace.seed != self.seed
            or workspace.steps != self.steps
            or workspace.law != COLLATZ_PHYSICAL_LAW
            or workspace.retain_chronological_support()
            or workspace.demand_configuration
            != (
                self._width_spine_demanded,
                self._joint_cocycle_demanded,
                self._innovation_tape_demanded,
                self._innovation_tape_modulus,
            )
        ):
            raise ValueError("Collatz source image belongs to another term")
        workspace.validate_source(workspace.root_source)
        workspace.validate_action(workspace.root_action)
        image = workspace.image_node(workspace.root_payload)
        if (
            self._workspace_binding
            != (
                workspace.root_source,
                workspace.root_action,
                workspace.root_payload,
                *workspace.demand_configuration,
            )
            or image.source != workspace.root_source
            or image.action != workspace.root_action
            or image.summary.width != self.steps
        ):
            raise ValueError("Collatz image belongs to another source/action")
        return workspace

    def _source_numerator(self) -> tuple[int, int]:
        """Demand the terminal affine expression, without retaining an endpoint."""
        transfer = self.source_image().saturated_summary().transfer
        numerator = transfer.upper * self.seed + transfer.offset
        self._ledger.bump(
            _collatz_keys.COLLATZ_IMAGE_PROJECTION_OPERAND_BITS,
            transfer.upper.bit_length()
            + self.seed.bit_length()
            + abs(transfer.offset).bit_length(),
        )
        if numerator < 0 or numerator % transfer.lower:
            raise ArithmeticError(
                "Collatz source image has an invalid terminal divisor"
            )
        return numerator, transfer.lower

    def radix_digit(self, radix: int, position: int) -> int:
        """Pull a bounded radix digit through the admitted affine transfer."""
        radix = require_integer(radix, "radix", 2)
        position = require_integer(position, "digit coordinate", 0)
        self._ledger.bump(_shared_keys.TEMPORAL_POINT_REQUESTS)
        self._ledger.bump(_shared_keys.COLLATZ_IMAGE_RADIX_DEMANDS)
        try:
            return self.admitted_radix_digit(radix, position)
        except _ExteriorRadixCoordinate:
            # The low-level modular view zero-pads exterior coordinates.
            return 0

    def admitted_radix_digit(self, radix: int, position: int) -> int:
        """Extract an active digit without constructing the affine numerator."""
        return _admitted_radix_digit_impl(
            radix,
            position,
            self.seed,
            self.resource_ledger,
            self.source_image,
        )

    @source_reads_only
    def _point_symbol(self, position: int) -> int:
        """Observe a binary cell, preserving the kernel's explicit blank symbol."""
        return self.point_radix_symbol(2, position)

    @source_reads_only
    def point_radix_symbol(self, radix: int, position: int) -> int:
        """Observe a whole binary limb once; ``radix`` denotes exterior blank.

        The shared affine threshold supplies the Archimedean guard. This
        batches demanded bits without claiming a new shifted-Q constructor.
        """
        return observe_radix_symbol(
            radix,
            position,
            self.steps,
            self.seed_digits,
            self.resource_ledger,
            self._microblocks,
            lambda: self.maximum_width,
            self.source_image,
            self.source_image_program,
            self.admitted_radix_digit,
        )

    def source_image_program(self) -> ActionProgramID:
        """Name cached digits without compiling a compatibility power DAG."""
        if self.steps <= 0:
            raise ValueError("source-image program requires a positive Collatz term")
        program = self._point_program
        if program is None:
            atom = self._compiler.atom(CollatzPhysicalBlockEffect())
            program = self._compiler.reference(atom)
            self._point_program = program
        return program

    @source_reads_only
    def digit(self, position: int) -> int:
        value = self._point_symbol(position)
        if value == 2:
            raise IndexError(position)
        self._ledger.bump(_shared_keys.TEMPORAL_POINT_REQUESTS)
        return value

    @source_reads_only
    def width(self) -> int:
        self._ledger.bump(_shared_keys.TEMPORAL_LENGTH_REQUESTS)
        _ = self.maximum_width  # Validate the original source/action binding.
        if self.steps == 0:
            return len(self.seed_digits)
        found = self._active_width
        if found is None:
            workspace = self.source_image()
            tape_width = workspace.tape_width_summary
            if tape_width is not None:
                # The workspace validates this sealed root-source/action port
                # after source_image has checked the term binding. Its blank
                # displacement is the exact endpoint-width change, so no
                # affine coefficient or endpoint is needed for this demand.
                found = tape_width.source_width + tape_width.blank.delta
            else:
                image = workspace.image_node(workspace.root_payload)
                transfer = image.summary.transfer
                if (
                    transfer.lower <= 0
                    or transfer.lower.bit_count() != 1
                    or transfer.upper < 0
                    or transfer.offset < 0
                ):
                    raise ArithmeticError(
                        "Collatz source image lost its nonnegative dyadic width law"
                    )
                denominator_exponent = transfer.lower.bit_length() - 1
                numerator_width = nonnegative_affine_width(
                    self.seed,
                    0,
                    transfer.upper,
                    transfer.offset,
                    self._ledger,
                )
                # Exact singleton cycle/run publications can have a constant
                # transfer (upper=0, lower=1); its width is still a projection
                # of the admitted source image. More generally use the
                # denominator actually sealed in that image, rather than
                # allocating 2**steps or treating physical time as an exponent.
                found = numerator_width - denominator_exponent
            if found <= 0:
                raise ArithmeticError("positive Collatz image has no active bits")
            self._active_width = found
        else:
            self.source_image()  # Cached extent is not live image authority.
        return found

    @property
    def estimated_bit_length(self) -> int:
        return self.width()

    def prepare_width_spine(self) -> None:
        """Request exact intermediate widths before the source image is built."""
        if self._workspace is None:
            self._width_spine_demanded = True

    def prepare_joint_cocycle(self) -> None:
        """Request the source-plus-normalized-successor action before imaging."""
        if self._workspace is not None:
            if not self._joint_cocycle_demanded:
                raise ValueError(
                    "joint Collatz demand must precede source-image construction"
                )
            return
        self._joint_cocycle_demanded = True

    def double_accumulators(self) -> CollatzDoubleWeight:
        """Return both exact physical-operation totals from the powered fields."""
        if not self._joint_cocycle_demanded:
            raise ValueError(
                "prepare the joint cocycle before requesting double totals"
            )
        if self.steps == 0:
            from number_compiler.sequences.collatz.weighted_right_congruence import (
                CollatzDoubleWeight,
            )

            return CollatzDoubleWeight(0, 0, self.seed, self.seed)
        action = self.source_image().joint_action
        if action is None:
            raise ValueError("joint cocycle was not published with this source image")
        return action.double_accumulators()

    def diagonal_carry_seam(self) -> CollatzDiagonalSeam:
        """Return the exact joint root action as a lazy bounded spatial seam.

        This is an observation of the already admitted source action. It does
        not select parity, compile another action, or retain a portable cache
        handle. Every call rechecks this term's source-image owner and demand.
        """
        if not self._joint_cocycle_demanded:
            raise ValueError(
                "prepare the joint cocycle before requesting a diagonal seam"
            )
        from number_compiler.hashlife.execution.dyadic_return_runs import (
            RunArithmeticWorkspace,
        )
        from number_compiler.sequences.collatz.diagonal_carry_action import (
            CollatzDiagonalSeam,
        )

        workspace = self.source_image()
        scratch = RunArithmeticWorkspace.for_ledger(self._ledger, "collatz_physical")
        with scratch.scope():
            scratch.require_bits(
                8
                * (
                    self.seed.bit_length()
                    + 4 * self.steps.bit_length()
                    + self.steps
                    + 128
                )
            )
            return CollatzDiagonalSeam.from_issued_joint(workspace)

    def accumulator(self, modulus: int) -> CollatzAccumulatorObservation:
        """Return source plus normalized successors modulo ``modulus``."""
        modulus = require_integer(modulus, "accumulator modulus", 2)
        if not self._joint_cocycle_demanded:
            raise ValueError("prepare the joint cocycle before requesting it")
        from number_compiler.sequences.collatz.joint_temporal_action import (
            CollatzAccumulatorObservation,
        )

        if self.steps == 0:
            return CollatzAccumulatorObservation(
                modulus, self.seed % modulus, True, 0, 0, 0
            )
        action = self.source_image().joint_action
        if action is None:
            raise ValueError("joint cocycle was not published with this source image")
        return action.accumulator_observation(modulus)

    def prepare_innovation_tape(
        self, *, complete_word: bool = False, modulus: int | None = None
    ) -> None:
        """Demand a boundary witness or the complete signed finite-prefix tape."""
        if type(complete_word) is not bool:
            raise TypeError("complete innovation demand must be Boolean")
        if complete_word:
            modulus = require_integer(modulus, "innovation modulus", 3, 4096)
            if modulus % 2 == 0:
                raise ValueError("innovation modulus must be odd")
        elif modulus is not None:
            raise ValueError("an innovation modulus requires complete-word demand")
        if self._workspace is not None:
            if not self._innovation_tape_demanded:
                raise ValueError(
                    "innovation demand must precede source-image construction"
                )
            if complete_word and self._innovation_tape_modulus is None:
                raise ValueError(
                    "complete innovation tape cannot be added after image construction"
                )
            if modulus is not None and modulus != self._innovation_tape_modulus:
                raise ValueError(
                    "innovation tape modulus differs from its source image"
                )
            return
        if (
            self._innovation_tape_modulus is not None
            and (not complete_word or modulus != self._innovation_tape_modulus)
            and (complete_word or modulus is not None)
        ):
            # A later boundary-only request cannot downgrade the admitted
            # full tape, and a full tape cannot silently change its modulus.
            raise ValueError("innovation tape demand conflicts with prior authority")
        self._innovation_tape_demanded = True
        if complete_word:
            self._innovation_tape_modulus = modulus

    def true_root_morphism(self) -> CertifiedCollatzRootMorphism:
        """Demand the source-bound root carrier from the admitted run result.

        This uses the exact quotient already produced for a joint/innovation
        observation. It cannot be requested on the ordinary term/digit path,
        and it never compiles a second physical run.
        """
        if not self._joint_cocycle_demanded:
            raise ValueError(
                "prepare the joint-cocycle detail before requesting the root morphism"
            )
        if self.steps == 0:
            raise ValueError("zero-span Collatz queries have no positive root morphism")
        return self.source_image().true_root_morphism

    def observe_boundary_macro(
        self,
        *,
        modulus: int | None = None,
        position_spectrum_requests: tuple[tuple[int, int], ...] = (),
        odd_position_moore_requests: tuple[tuple[int, int], ...] = (),
        position_moore_walsh64: bool = False,
    ) -> dict[str, object]:
        """Observe the first admitted macro and any explicitly requested ports.

        Position spectra and odd-radix Moore machines are optional rich
        observations. Ordinary term, digit and metrics requests never invoke
        them. Their futures are conditional on repeating this exact admitted
        parity word; they do not predict the next Collatz selector.
        """
        from number_compiler.sequences.collatz.boundary_observation import (
            observe_empty_source_innovation_tape,
            observe_guarded_boundary,
            validate_position_requests,
        )

        validate_position_requests(
            position_spectrum_requests,
            odd_position_moore_requests,
            position_moore_walsh64,
        )

        if not self._innovation_tape_demanded:
            raise ValueError("prepare the innovation demand before requesting it")
        if modulus is not None:
            modulus = require_integer(modulus, "innovation modulus", 3, 4096)
            if modulus % 2 == 0:
                raise ValueError("innovation modulus must be odd")
        prepared_modulus = self._innovation_tape_modulus
        if prepared_modulus is not None and modulus not in (None, prepared_modulus):
            raise ValueError("requested innovation modulus differs from prepared tape")
        selected_modulus = prepared_modulus if prepared_modulus is not None else modulus
        workspace = None if self.steps == 0 else self.source_image()
        witness = None if workspace is None else workspace.first_boundary_macro
        global_tape = None
        if prepared_modulus is not None:
            if workspace is not None:
                global_tape = workspace.innovation_observation
            else:
                global_tape = observe_empty_source_innovation_tape(
                    self.seed, prepared_modulus, self._ledger
                )
        return observe_guarded_boundary(
            self.seed,
            witness,
            selected_modulus,
            self._ledger,
            global_tape,
            position_spectrum_requests=position_spectrum_requests,
            odd_position_moore_requests=odd_position_moore_requests,
            position_moore_walsh64=position_moore_walsh64,
        )

    @source_reads_only
    def s_arithmetic_clock(self) -> SArithmeticClock:
        """Derive the slope places from this physical, source-bound application.

        This queries the existing bound interface and reuses a completed result
        when present. It does not build an accelerated itinerary or treat a
        clock readout as an action identity.
        """
        from number_compiler.sequences.collatz.clock_observers import SArithmeticClock

        if self.steps == 0:
            return SArithmeticClock(0, 0)
        # The clock observer is the explicit width-spine consumer. Request it
        # only before the source image is first built; an already published
        # ordinary image is reused with its optional summary absent.
        self.prepare_width_spine()
        odd = self.source_image().odd_steps()
        if not 0 <= odd <= self.steps:
            raise ValueError("bound Collatz result has an invalid physical clock")
        return SArithmeticClock(odd, self.steps - odd)

    def iter_digits(self) -> Iterator[int]:
        def source() -> Iterator[int]:
            if self.steps == 0:
                yield from self.seed_digits
                return
            numerator, divisor = self._source_numerator()
            yield from digits_lsd(numerator // divisor, 2)

        return measured_output_stream(self._ledger, "collatz_output_stream", source)

    def digits(self) -> tuple[int, ...]:
        return tuple(map(int, self.iter_digits()))

    def materialize(self, *, max_bits: int) -> int:
        max_bits = require_integer(max_bits, "output bit cap", 0)
        if self.steps == 0:
            if self.seed.bit_length() > max_bits:
                raise ValueError((self.seed.bit_length(), max_bits))
            return self.seed
        numerator, divisor = self._source_numerator()
        width = max(1, numerator.bit_length() - (divisor.bit_length() - 1))
        if width > max_bits:
            raise ValueError((width, max_bits))
        return numerator // divisor

    def behavior_metrics(self) -> HashLifeBehaviorMetrics:
        """Return the seed/function/application HashLife description split.

        This metric does not materialize the output word.  For positive powers it
        reports the compact source-independent jump function separately from the
        seed-specific source-image description created by point queries.
        """
        from number_compiler.sequences.collatz.behavior_metrics import (
            collatz_behavior_metrics,
        )

        return collatz_behavior_metrics(self)

    def metrics(self) -> CollatzPhysicalBlockMetrics:
        from number_compiler.sequences.collatz.metrics_projection import (
            project_collatz_term_metrics,
        )

        return project_collatz_term_metrics(
            self._ledger,
            seed=self.seed,
            steps=self.steps,
            operator_nodes=self.operator_nodes,
            compose_operations=self.compose_operations,
            syntax_depth_bound=self.syntax_depth_bound,
            descriptor_bits=pair_field_descriptor_bits(self.seed, self.steps),
        )


__all__ = [
    "CollatzPhysicalBlockEffect",
    "PoweredCollatzTerm",
]
