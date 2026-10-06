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
from typing import TYPE_CHECKING, Any

from number_compiler.arithmetic.contracts.block_effect import (
    _OPERATOR_IDS,
    BlockEffect,
    BoundarySide,
    BoundaryState,
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
    bit_width,
    digits_lsd,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.output_stream_metrics import (
    initialize_output_stream_metrics,
    measured_output_stream,
)

if TYPE_CHECKING:
    from number_compiler.projection.lazy_radix import RadixProjection
    from number_compiler.resources.collatz_power_metrics import (
        CollatzPhysicalBlockMetrics,
    )
    from number_compiler.resources.metric_records import HashLifeBehaviorMetrics
    from number_compiler.sequences.collatz.clock_observers import SArithmeticClock
    from number_compiler.sequences.collatz.physical_images import (
        CollatzPhysicalImageWorkspace,
    )


# Left boundary states.  START means no active source digit has been consumed.
_START = 0
_EVEN = 1


class _ExteriorRadixCoordinate(IndexError):
    """Exact affine threshold says a scalar coordinate is outside the value."""


# Odd states encode (previous_bit, carry) in states 2..5.
def _odd_state(previous: int, carry: int) -> int:
    previous = require_integer(previous, "previous Collatz bit", 0, 1)
    carry = require_integer(carry, "Collatz carry", 0, 1)
    if previous not in (0, 1) or carry not in (0, 1):
        raise ValueError((previous, carry))
    return 2 + (previous << 1) + carry


def _odd_parts(state: int) -> tuple[int, int]:
    state = require_integer(state, "Collatz odd state", 2, 5)
    if not 2 <= state <= 5:
        raise ValueError(state)
    value = state - 2
    return (value >> 1) & 1, value & 1


class CollatzPhysicalBlockEffect:
    """One exact physical Collatz step on a padded LSD-first binary tape."""

    __slots__ = (
        "_sealed",
        "base",
        "blank",
        "blank_left_tail",
        "blank_right_tail",
        "eager_boundary_quotient",
        "exponent",
        "node_id",
        "stable_blank_output",
        "supports_predecessor_trace",
    )

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("kernel definitions are immutable")
        object.__setattr__(self, name, value)

    def __delattr__(self, name: str) -> None:
        raise AttributeError("immutable definition attributes cannot be deleted")

    def __init__(self) -> None:
        self.base = 2
        self.blank = 2
        self.exponent = 1
        self.node_id = next(_OPERATOR_IDS)
        # An odd multiplication settles after at most two blank cells; an even
        # shift needs only the immediately higher source symbol.
        self.blank_left_tail = 2
        self.blank_right_tail = 1
        self.stable_blank_output = True
        self.supports_predecessor_trace = False
        # The complete atom carrier is only 6 left states x 3 right states.
        # This opt-in lets composed powers retain exact extensional normalized
        # action tables instead of falling back to provenance words.
        self.eager_boundary_quotient = True
        self._sealed = True

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz-physical-block", 1)

    def initial(self, side: BoundarySide) -> int:
        if type(side) is not BoundarySide:
            raise TypeError("Collatz boundary side must be an exact enum value")
        return _START if side is BoundarySide.LEFT else self.blank

    def boundary_universe(
        self,
        side: BoundarySide,
        *,
        max_states: int | None = None,
    ) -> tuple[int, ...] | None:
        if type(side) is not BoundarySide:
            raise TypeError("Collatz boundary side must be an exact enum value")
        states = tuple(range(6)) if side is BoundarySide.LEFT else (0, 1, self.blank)
        if max_states is not None:
            max_states = require_integer(max_states, "maximum boundary states", 0)
        if max_states is not None and len(states) > max_states:
            return None
        return states

    def advance(self, side: BoundarySide, state: BoundaryState, symbol: int) -> int:
        if type(side) is not BoundarySide:
            raise TypeError("Collatz boundary side must be an exact enum value")
        state = require_integer(state, "Collatz boundary state")
        symbol = require_integer(symbol, "Collatz source symbol")
        if symbol not in (0, 1, self.blank):
            raise ValueError(symbol)
        if side is BoundarySide.RIGHT:
            # After scanning a suffix from high to low, the right state is the
            # symbol immediately above the current position.
            return symbol

        if state == _START:
            if symbol == self.blank:
                return _START
            if symbol == 0:
                return _EVEN
            # x0=1 selects odd mode.  At the first cell, 1 + 0 + 0 + 1 = 2,
            # so the carry after the cell is one and previous input is one.
            return _odd_state(1, 1)
        if state == _EVEN:
            return _EVEN
        previous, carry = _odd_parts(state)
        current = 0 if symbol == self.blank else symbol
        total = current + previous + carry
        return _odd_state(current, total >> 1)

    def emit(self, left: BoundaryState, symbol: int, right: BoundaryState) -> int:
        left = require_integer(left, "Collatz left boundary")
        symbol = require_integer(symbol, "Collatz source symbol")
        right = require_integer(right, "Collatz right boundary")
        if symbol not in (0, 1, self.blank) or right not in (0, 1, self.blank):
            raise ValueError((symbol, right))

        consumes_right, local = self.output_consumer(left, symbol)
        return right if consumes_right else local

    def output_consumer(self, left: int, symbol: int) -> tuple[bool, int]:
        """Return the geometry-selected right view and left-local output.

        ``True`` means the even shift consumes the adjacent higher symbol.
        The other branch is already an exact output of the odd carry state.
        """
        left = require_integer(left, "Collatz left boundary")
        symbol = require_integer(symbol, "Collatz source symbol")
        if symbol not in (0, 1, self.blank):
            raise ValueError(symbol)

        # The first digit itself chooses the global Collatz branch.
        if left == _START:
            if symbol == self.blank:
                return False, self.blank
            if symbol == 0:
                return True, 0
            # Odd first cell includes +1.
            return False, (symbol + 1) & 1

        if left == _EVEN:
            # Binary division by two: output_i = input_(i+1).  A blank next
            # symbol means this and every higher output position is blank.
            return True, 0

        previous, carry = _odd_parts(left)
        current = 0 if symbol == self.blank else symbol
        total = current + previous + carry
        if symbol == self.blank and total == 0:
            return False, self.blank
        return False, total & 1

    def predecessor(self, side: BoundarySide, state: BoundaryState) -> None:
        return None

    def operator_nodes(self) -> int:
        return 1

    def runtime_stats(self) -> dict[str, int]:
        return {
            "operator_nodes": 1,
            "retained_execution_nodes": 0,
            "canonical_program_word_roots": 0,
            "left_boundary_residuals": 0,
            "right_boundary_residuals": 0,
            "residual_cache_hits": 0,
            "residual_cache_misses": 0,
            "output_cache_hits": 0,
            "output_cache_misses": 0,
            "output_cache_slots": 0,
            "output_cache_occupied": 0,
            "left_transition_entries": 0,
            "right_transition_entries": 0,
            "finite_kernel_left_states": 0,
            "finite_kernel_right_states": 0,
            "finite_kernel_storage_bytes": 0,
            "leaf_effect_transition_cache_entries": 0,
            "leaf_effect_output_cache_entries": 0,
            "leaf_effect_cache_entries": 0,
        }


def power_collatz_physical_effect(
    steps: int,
    *,
    max_context_nodes: int | None = None,
    max_cache_entries: int | None = None,
) -> BlockPower:
    """Compile ``physical_collatz**steps`` by source-independent squaring."""
    steps = require_integer(steps, "Collatz physical steps", 0)
    compiler = LazyCompiler(ResourceLedger(max_context_nodes, max_cache_entries))
    from number_compiler.sequences.collatz.compilation import (
        compile_collatz_physical_power,
    )

    return compile_collatz_physical_power(compiler, steps)


class PoweredCollatzTerm:
    """Exact physical Collatz nth state using only the powered block fast path."""

    __slots__ = (
        "__weakref__",
        "_active_width",
        "_compiler",
        "_effect",
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
        self._ledger.bump("temporal_point_requests", 0)
        self._ledger.bump("temporal_length_requests", 0)
        self.seed = seed
        self.steps = steps
        self.seed_digits = tuple(map(int, digits_lsd(seed, 2)))
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
        self._ledger.bump("collatz_width_bound_constructions")
        self._ledger.bump("collatz_width_bound_operand_bits", seed.bit_length() + 2)
        self._source_construction = OriginalSourceConstruction(
            ExactSource(self.seed_digits, 2, blank=2, extent=bound, alphabet_size=2),
        )
        self._ledger.register_execution_root(self)
        self._compiler = LazyCompiler(self._ledger)
        self._max_context_nodes = max_context_nodes
        self._max_cache_entries = max_cache_entries
        self._workspace: CollatzPhysicalImageWorkspace | None = None
        self._workspace_binding: tuple[object, object, object, bool] | None = None
        self._width_spine_demanded = False
        radix_owner = self._ledger.register(
            "radix-applications", "application_index", "INDEX_OWNED"
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

    @property
    def descriptor_bits(self) -> int:
        return bit_width(self.seed) + bit_width(self.steps) + 2

    def _source_image(self) -> CollatzPhysicalImageWorkspace:
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
            )
            self._workspace_binding = (
                workspace.root_source,
                workspace.root_action,
                workspace.root_payload,
                workspace._include_width_spine,
            )
            self._workspace = workspace
        if (
            type(workspace) is not CollatzPhysicalImageWorkspace
            or workspace.ledger is not self._ledger
            or workspace.seed != self.seed
            or workspace.steps != self.steps
            or workspace.law != COLLATZ_PHYSICAL_LAW
            or workspace.retain_chronological_support()
            or workspace._include_width_spine != self._width_spine_demanded
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
                workspace._include_width_spine,
            )
            or image.source != workspace.root_source
            or image.action != workspace.root_action
            or image.summary.width != self.steps
        ):
            raise ValueError("Collatz image belongs to another source/action")
        return workspace

    def _source_numerator(self) -> tuple[int, int]:
        """Demand the terminal affine expression, without retaining an endpoint."""
        transfer = self._source_image().saturated_summary().transfer
        numerator = transfer.upper * self.seed + transfer.offset
        self._ledger.bump(
            "collatz_image_projection_operand_bits",
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
        self._ledger.bump("temporal_point_requests")
        self._ledger.bump("collatz_image_radix_demands")
        try:
            return self._admitted_radix_digit(radix, position)
        except _ExteriorRadixCoordinate:
            # The low-level modular view zero-pads exterior coordinates.
            return 0

    def _admitted_radix_digit(self, radix: int, position: int) -> int:
        """Extract an active digit without constructing the affine numerator."""
        if radix == 2:
            from number_compiler.hashlife.execution.dyadic_return_observers import (
                binary_cell,
            )

            symbol = binary_cell(self._source_image(), position)
            if symbol == 2:
                raise _ExteriorRadixCoordinate(position)
            return symbol
        transfer = self._source_image().saturated_summary().transfer
        numerator_bits = (
            max(
                transfer.upper.bit_length() + self.seed.bit_length(),
                abs(transfer.offset).bit_length(),
            )
            + 1
        )
        scaled_place_bits = (
            transfer.lower.bit_length() - 1 + position * (radix.bit_length() - 1)
        )
        if scaled_place_bits >= numerator_bits:
            self._ledger.bump("collatz_radix_exterior_shortcuts")
            if position == 0:
                return 0
            raise _ExteriorRadixCoordinate(position)
        place = int(radix**position)
        threshold = transfer.lower * place
        # For N=u*seed+o, N<T iff o<T and
        # (u=0 or seed <= floor((T-o-1)/u)).
        exterior = transfer.offset < threshold and (
            transfer.upper == 0
            or self.seed <= (threshold - transfer.offset - 1) // transfer.upper
        )
        if exterior:
            self._ledger.bump("collatz_radix_exterior_shortcuts")
            if position == 0:
                return 0
            raise _ExteriorRadixCoordinate(position)
        modulus = threshold * radix
        residue = (
            (transfer.upper % modulus) * (self.seed % modulus)
            + transfer.offset % modulus
        ) % modulus
        self._ledger.bump("collatz_image_projection_operand_bits", modulus.bit_length())
        return residue // threshold

    @source_reads_only
    def _point_symbol(self, position: int) -> int:
        """Observe a binary cell, preserving the kernel's explicit blank symbol."""
        return self._point_radix_symbol(2, position)

    @source_reads_only
    def _point_radix_symbol(self, radix: int, position: int) -> int:
        """Observe a whole binary limb once; ``radix`` denotes exterior blank.

        The shared affine threshold supplies the Archimedean guard. This
        batches demanded bits without claiming a new shifted-Q constructor.
        """
        radix = require_integer(radix, "binary limb radix", 2, 1 << 63)
        if radix & (radix - 1):
            raise ValueError("binary limb radix must be a power of two")
        position = require_integer(position, "digit coordinate")
        limb_bits = radix.bit_length() - 1
        start = position * limb_bits
        if position < 0 or start >= self.maximum_width:
            raise IndexError(position)
        if self.steps == 0:
            if start >= len(self.seed_digits):
                return radix
            value = 0
            for offset in range(min(limb_bits, len(self.seed_digits) - start)):
                value = self._ledger.observe_arithmetic(
                    value | (self.seed_digits[start + offset] << offset)
                )
                self._ledger.bump("collatz_original_limb_source_reads")
            return value
        from number_compiler.projection.microblock_cache import (
            ExactMicroblock,
            MicroblockKey,
        )

        self._ledger.bump("direct_powered_point_queries")
        workspace = self._source_image()
        key = MicroblockKey(
            self._source_image_program(),
            radix,
            0,
            position,
            "output",
            source_scope=workspace.owner,
        )
        cached = self._microblocks.get(key)
        if cached is not None:
            # Source/action/image authority was checked before the cache lookup.
            if not 0 <= cached.encoded <= radix:
                raise ValueError("cached Collatz point belongs to another alphabet")
            return cached.encoded
        try:
            symbol = self._admitted_radix_digit(radix, position)
        except _ExteriorRadixCoordinate:
            symbol = radix
        else:
            self._ledger.bump("collatz_image_radix_demands")
            if not 0 <= symbol < radix:
                raise AssertionError("source image produced an invalid limb")
        self._microblocks.put(key, ExactMicroblock(symbol, limb_bits + 1))
        return symbol

    def _source_image_program(self) -> ActionProgramID:
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
        self._ledger.bump("temporal_point_requests")
        return value

    @source_reads_only
    def width(self) -> int:
        self._ledger.bump("temporal_length_requests")
        _ = self.maximum_width  # Validate the original source/action binding.
        if self.steps == 0:
            return len(self.seed_digits)
        found = self._active_width
        if found is None:
            workspace = self._source_image()
            tape_width = workspace.tape_width_summary
            if tape_width is not None:
                # The workspace validates this sealed root-source/action port
                # after _source_image has checked the term binding. Its blank
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
            self._source_image()  # Cached extent is not live image authority.
        return found

    @property
    def estimated_bit_length(self) -> int:
        return self.width()

    def prepare_width_spine(self) -> None:
        """Request exact intermediate widths before the source image is built."""
        if self._workspace is None:
            self._width_spine_demanded = True

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
        odd = self._source_image().odd_steps()
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
        from number_compiler.resources.dyadic_behavior_metrics import (
            collatz_behavior_metrics,
        )

        return collatz_behavior_metrics(self)

    def metrics(self) -> CollatzPhysicalBlockMetrics:
        from number_compiler.resources.collatz_power_metrics import (
            CollatzPhysicalBlockMetrics,
        )
        from number_compiler.resources.metric_collection import (
            collect_unindexed_metrics,
        )
        from number_compiler.resources.powered_metrics import project_powered_metrics

        point = collect_unindexed_metrics(self._ledger)
        return project_powered_metrics(
            CollatzPhysicalBlockMetrics,
            point,
            seed=self.seed,
            steps=self.steps,
            operator_nodes=self.operator_nodes,
            compose_operations=self.compose_operations,
            syntax_depth_bound=self.syntax_depth_bound,
            descriptor_bits=self.descriptor_bits,
            # The source-image point path is intentionally index-free.  Export
            # its explicit query counter directly instead of relying on the
            # legacy HashLife index alias.
            direct_powered_point_queries=self._ledger.counters.get(
                "direct_powered_point_queries", 0
            ),
            collatz_physical_factored_output_compilations=point.resource_work_counters.get(
                "collatz_physical_factored_output_compilations", 0
            ),
            collatz_physical_joint_output_tables_elided=point.resource_work_counters.get(
                "collatz_physical_joint_output_tables_elided", 0
            ),
        )


__all__ = [
    "CollatzPhysicalBlockEffect",
    "CollatzPhysicalBlockMetrics",
    "PoweredCollatzTerm",
    "power_collatz_physical_effect",
]


def __getattr__(name: str) -> Any:
    from number_compiler.api.lazy_exports import resolve_export

    return resolve_export(
        name,
        {
            "CollatzPhysicalBlockMetrics": "number_compiler.resources.collatz_power_metrics"
        },
        globals(),
    )
