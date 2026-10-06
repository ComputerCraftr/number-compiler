"""Production source-bound Collatz temporal quotient by maximal 0/1 runs.

The normalized Collatz map is

    H0(x) = x/2
    H1(x) = (3*x+1)/2.

At a normalized boundary the next maximal run length is available without a
parity itinerary::

    zero run length = v2(x)       when x is even
    one run length  = v2(x + 1)   when x is odd.

Both runs have closed affine powers. Mixed residuals use a ledger-owned finite
D8 source-section transducer; long homogeneous runs keep their closed powers.
Cold D8 discovery is bounded and explicitly accounted. This contractor never
constructs a global parity word or physical branch tree. The
scheduler retains balanced source-cylinder construction for wide mixed sources;
this run helper is not a complete all-source root quotient. The pinned
``1 -> 4 -> 2 -> 1`` cycle is a powered motif.

The optional anonymous F5 audit counts actions in the 20-element affine group
without materializing a branch tree. This finite projection does not prove
equivalence of exact integer source trajectories.  Exact source selection remains deterministic; the root
algebra is a coefficient/fiber normalization, not a replacement for source
authentication.
"""

from __future__ import annotations

from collections.abc import Sequence
from contextlib import nullcontext
from dataclasses import dataclass
from typing import overload

from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.arithmetic.fields.morphism_core import AffineCocycle, binary_power
from number_compiler.arithmetic.fields.root_semifield import RootSemifieldElement
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.tape_width import (
    CollatzWidthSpineAccumulator,
    charge_width_repeat,
)
from number_compiler.sequences.collatz.temporal_dyadic import (
    D8CylinderFrame,
    D8TemporalTable,
)
from number_compiler.sequences.collatz.temporal_run_result import (
    CollatzTemporalRunQuotient,
)

_F5 = 5
_ROOT_CERTIFICATE_DEPTH = 8
_MAX_CYLINDER_BATCH_SYMBOLS = 64
_MIN_CYLINDER_SOURCE_BITS = 131_072


def _bounded_run_length(residue: int) -> int:
    """Enough low-bit precision to choose between D8 and a homogeneous run."""
    if residue & 1:
        return v2_positive(residue + 1)
    return 8 if residue == 0 else v2_positive(residue)


@dataclass(frozen=True, slots=True, order=True)
class CollatzF5AffineAction:
    """Affine map ``x -> scale*x + offset`` on F5."""

    scale: int
    offset: int

    def __post_init__(self) -> None:
        if type(self.scale) is not int or type(self.offset) is not int:
            raise TypeError("F5 affine action needs exact integers")
        if not 1 <= self.scale < _F5 or not 0 <= self.offset < _F5:
            raise ValueError("F5 affine action lies outside AGL(1,5)")

    @classmethod
    def identity(cls) -> CollatzF5AffineAction:
        return cls(1, 0)

    def apply(self, value: int) -> int:
        if type(value) is not int:
            raise TypeError("F5 action input must be an exact integer")
        return AffineCocycle(self.scale, self.offset).apply(
            value,
            multiply=lambda a, b: a * b % _F5,
            add=lambda a, b: (a + b) % _F5,
        )

    def then(self, after: CollatzF5AffineAction) -> CollatzF5AffineAction:
        if type(after) is not CollatzF5AffineAction:
            raise TypeError("F5 affine actions compose with their own type")
        composed = AffineCocycle(self.scale, self.offset).then(
            AffineCocycle(after.scale, after.offset),
            multiply=lambda a, b: a * b % _F5,
            add=lambda a, b: (a + b) % _F5,
        )
        return CollatzF5AffineAction(composed.multiplier, composed.addend)

    def power(self, exponent: int) -> CollatzF5AffineAction:
        return binary_power(
            self,
            exponent,
            identity=CollatzF5AffineAction.identity(),
            compose=CollatzF5AffineAction.then,
        ).value


HENSEL_ZERO_F5 = CollatzF5AffineAction(3, 0)
HENSEL_ONE_F5 = CollatzF5AffineAction(4, 3)
ODD_HALF_F5 = CollatzF5AffineAction(3, 1)


class _F5AffineAlphabet(Sequence[CollatzF5AffineAction]):
    """Fixed AGL(1,5) coordinates, constructed only when explicitly read."""

    def __len__(self) -> int:
        return 20

    @overload
    def __getitem__(self, index: int) -> CollatzF5AffineAction: ...

    @overload
    def __getitem__(self, index: slice) -> tuple[CollatzF5AffineAction, ...]: ...

    def __getitem__(
        self,
        index: int | slice,
    ) -> CollatzF5AffineAction | tuple[CollatzF5AffineAction, ...]:
        if isinstance(index, slice):
            return tuple(
                CollatzF5AffineAction(i // _F5 + 1, i % _F5)
                for i in range(*index.indices(len(self)))
            )
        if index < 0:
            index += len(self)
        if not 0 <= index < len(self):
            raise IndexError(index)
        scale, offset = divmod(index, _F5)
        return CollatzF5AffineAction(scale + 1, offset)


F5_AFFINE_ALPHABET = _F5AffineAlphabet()


def _f5_index(action: CollatzF5AffineAction) -> int:
    if type(action) is not CollatzF5AffineAction:
        raise TypeError("temporal fiber requires an F5 affine action")
    action.__post_init__()
    return (action.scale - 1) * _F5 + action.offset


@dataclass(frozen=True, slots=True)
class CollatzAnonymousF5Fiber:
    """Anonymous multiplicities over the finite temporal F5 action group."""

    counts: tuple[int, ...]

    def __post_init__(self) -> None:
        if len(self.counts) != len(F5_AFFINE_ALPHABET):
            raise ValueError("temporal F5 fiber has the wrong basis size")
        if any(type(count) is not int or count < 0 for count in self.counts):
            raise ValueError("temporal F5 multiplicities must be natural numbers")

    @classmethod
    def identity(cls) -> CollatzAnonymousF5Fiber:
        counts = [0] * len(F5_AFFINE_ALPHABET)
        counts[_f5_index(CollatzF5AffineAction.identity())] = 1
        return cls(tuple(counts))

    @classmethod
    def source_symbol_fiber(cls) -> CollatzAnonymousF5Fiber:
        counts = [0] * len(F5_AFFINE_ALPHABET)
        counts[_f5_index(HENSEL_ZERO_F5)] += 1
        counts[_f5_index(HENSEL_ONE_F5)] += 1
        return cls(tuple(counts))

    @classmethod
    def singleton(cls, action: CollatzF5AffineAction) -> CollatzAnonymousF5Fiber:
        if type(action) is not CollatzF5AffineAction:
            raise ValueError("temporal singleton fiber needs an admitted F5 action")
        counts = [0] * len(F5_AFFINE_ALPHABET)
        counts[_f5_index(action)] = 1
        return cls(tuple(counts))

    @property
    def unique_action(self) -> CollatzF5AffineAction:
        support = tuple(self.support)
        if self.cardinality != 1 or len(support) != 1:
            raise ValueError("temporal fiber is not a singleton source action")
        return support[0]

    @property
    def cardinality(self) -> int:
        return sum(self.counts)

    @property
    def root_amplitude(self) -> RootSemifieldElement:
        return RootSemifieldElement(self.cardinality)

    @property
    def support(self) -> frozenset[CollatzF5AffineAction]:
        return frozenset(
            F5_AFFINE_ALPHABET[index]
            for index, count in enumerate(self.counts)
            if count
        )

    def root_sum(self, other: CollatzAnonymousF5Fiber) -> CollatzAnonymousF5Fiber:
        if type(other) is not CollatzAnonymousF5Fiber:
            raise TypeError("temporal root sum requires another F5 fiber")
        out = CollatzAnonymousF5Fiber(
            tuple(a + b for a, b in zip(self.counts, other.counts, strict=True))
        )
        expected = self.root_amplitude.root_sum(other.root_amplitude)
        if out.root_amplitude != expected:
            raise AssertionError("root-sum fiber cardinality lost exactness")
        return out

    def root_difference(
        self, other: CollatzAnonymousF5Fiber
    ) -> CollatzAnonymousF5Fiber:
        if type(other) is not CollatzAnonymousF5Fiber:
            raise TypeError("temporal root difference requires another F5 fiber")
        if any(b > a for a, b in zip(self.counts, other.counts, strict=True)):
            raise ValueError("root difference requires a proved subfiber")
        out = CollatzAnonymousF5Fiber(
            tuple(a - b for a, b in zip(self.counts, other.counts, strict=True))
        )
        expected = self.root_amplitude.root_difference(other.root_amplitude)
        if out.root_amplitude != expected:
            raise AssertionError("root-difference fiber cardinality lost exactness")
        return out

    def multiply(self, other: CollatzAnonymousF5Fiber) -> CollatzAnonymousF5Fiber:
        if type(other) is not CollatzAnonymousF5Fiber:
            raise TypeError("temporal Cayley product requires another F5 fiber")
        counts = [0] * len(F5_AFFINE_ALPHABET)
        left_entries = tuple(
            (index, count) for index, count in enumerate(self.counts) if count
        )
        right_entries = tuple(
            (index, count) for index, count in enumerate(other.counts) if count
        )
        for left_index, left_count in left_entries:
            left = F5_AFFINE_ALPHABET[left_index]
            for right_index, right_count in right_entries:
                target = left.then(F5_AFFINE_ALPHABET[right_index])
                counts[_f5_index(target)] += left_count * right_count
        out = CollatzAnonymousF5Fiber(tuple(counts))
        expected = self.root_amplitude.multiply(other.root_amplitude)
        if out.root_amplitude != expected:
            raise AssertionError("root-product fiber cardinality lost exactness")
        return out

    def power(self, exponent: int) -> CollatzAnonymousF5Fiber:
        return binary_power(
            self,
            exponent,
            identity=CollatzAnonymousF5Fiber.identity(),
            compose=CollatzAnonymousF5Fiber.multiply,
        ).value


def _root_fiber(
    depth: int, *, ledger: ResourceLedger | None = None
) -> CollatzAnonymousF5Fiber:
    """Build the bounded anonymous temporal fiber through the root algebra."""
    if type(depth) is not int or not 0 <= depth <= _ROOT_CERTIFICATE_DEPTH:
        raise ValueError(depth)
    fiber = CollatzAnonymousF5Fiber.identity()
    symbol = CollatzAnonymousF5Fiber.source_symbol_fiber()
    for _ in range(depth):
        fiber = fiber.multiply(symbol)
        if ledger is not None:
            ledger.bump("collatz_physical_temporal_root_cayley_products")
    return fiber


@dataclass(frozen=True, slots=True)
class CollatzPoweredRootVietaProgram:
    """Lazy anonymous F5 coefficient program, with no source-port authority.

    Construction and composition retain only a symbol count. Explicit evaluation
    uses binary powering of twenty Cayley multiplicities; those integers can have
    a number of bits linear in ``symbols``. Integer coordinate power sums are
    descriptive Vieta data, not a proof about exact Collatz successors.
    """

    symbols: int

    def __post_init__(self) -> None:
        if type(self.symbols) is not int or self.symbols < 0:
            raise ValueError("powered root/Vieta program needs a natural width")

    @property
    def semantic_key(self) -> tuple[str, int]:
        return ("collatz-f5-vieta-power-v1", self.symbols)

    def then(
        self, after: CollatzPoweredRootVietaProgram
    ) -> CollatzPoweredRootVietaProgram:
        if type(after) is not CollatzPoweredRootVietaProgram:
            raise TypeError("root/Vieta composition requires another powered program")
        return CollatzPoweredRootVietaProgram(self.symbols + after.symbols)

    def square(self) -> CollatzPoweredRootVietaProgram:
        return CollatzPoweredRootVietaProgram(2 * self.symbols)

    def evaluate(self) -> CollatzAnonymousF5Fiber:
        """Materialize exact finite multiplicities only on explicit demand."""
        return CollatzAnonymousF5Fiber.source_symbol_fiber().power(self.symbols)

    def vieta_moments(self, order: int = 19) -> tuple[int, ...]:
        """Return coordinate power sums from degree zero through ``order``."""
        if type(order) is not int or order < 0:
            raise ValueError("Vieta moment order must be nonnegative")
        counts = self.evaluate().counts
        roots = tuple(5 * action.scale + action.offset for action in F5_AFFINE_ALPHABET)
        return tuple(
            sum(count * root**degree for root, count in zip(roots, counts, strict=True))
            for degree in range(order + 1)
        )


@dataclass(frozen=True, slots=True)
class CollatzRootFiberCertificate:
    """Explicit bounded support audit plus a lazy all-scale coefficient program."""

    depth: int
    support_size: int
    amplitude_square: int
    powered_program: CollatzPoweredRootVietaProgram

    @property
    def powered_symbols(self) -> int:
        return self.powered_program.symbols

    def powered_multiplicity(self, action: CollatzF5AffineAction) -> int:
        return self.powered_program.evaluate().counts[_f5_index(action)]


def root_fiber_certificate(
    normalized_symbols: int, *, ledger: ResourceLedger | None = None
) -> CollatzRootFiberCertificate:
    if type(normalized_symbols) is not int or normalized_symbols < 0:
        raise ValueError(normalized_symbols)
    if ledger is not None and type(ledger) is not ResourceLedger:
        raise TypeError("root fiber certificate requires its resource ledger")
    depth = min(normalized_symbols, _ROOT_CERTIFICATE_DEPTH)
    fiber = _root_fiber(depth, ledger=ledger)
    if normalized_symbols >= _ROOT_CERTIFICATE_DEPTH and len(fiber.support) != 20:
        raise AssertionError("temporal F5 root fiber did not saturate at depth eight")
    if ledger is not None:
        ledger.bump(
            "collatz_physical_temporal_root_semifield_amplitude_square",
            fiber.cardinality,
        )
        ledger.bump("collatz_physical_temporal_root_vieta_programs")
        ledger.bump(
            "collatz_physical_temporal_root_vieta_powered_symbols", normalized_symbols
        )
        ledger.bump(
            "collatz_physical_temporal_root_vieta_program_description_bits",
            max(1, normalized_symbols.bit_length()),
        )
    return CollatzRootFiberCertificate(
        depth,
        len(fiber.support),
        fiber.cardinality,
        CollatzPoweredRootVietaProgram(normalized_symbols),
    )


def _append_dyadic_f5(
    normalized: CollatzF5AffineAction,
    physical: CollatzF5AffineAction,
    multiplier: int,
    target_origin: int,
    residue: int,
) -> tuple[CollatzF5AffineAction, CollatzF5AffineAction]:
    # Admitted dyadic widths are multiples of four, so 2**width = 1 mod 5.
    action = CollatzF5AffineAction(
        multiplier % 5, (target_origin - multiplier * residue) % 5
    )
    return normalized.then(action), physical.then(action)


def _run_zero_f5(length: int) -> CollatzF5AffineAction:
    if type(length) is not int or length <= 0:
        raise ValueError("zero run length must be positive")
    # x -> 3*x on F5 has order four.
    return HENSEL_ZERO_F5.power(length & 3)


def _run_one_f5(length: int) -> CollatzF5AffineAction:
    if type(length) is not int or length <= 0:
        raise ValueError("one run length must be positive")
    # x -> 4*x+3 on F5 is an involution.
    return HENSEL_ONE_F5 if length & 1 else CollatzF5AffineAction.identity()


_CYCLE_F5 = HENSEL_ONE_F5.then(HENSEL_ZERO_F5)


def compile_collatz_temporal_run_quotient(
    seed: int,
    physical_ticks: int,
    *,
    ledger: ResourceLedger,
    include_f5: bool = False,
    shared_cache: bool = False,
    include_width_spine: bool = False,
) -> CollatzTemporalRunQuotient:
    """Compile the exact source-bound action without a parity itinerary.

    Work uses maximal runs, finite D8 sections and the powered known-cycle
    motif. Cold D8 table discovery costs eight bounded local symbols per row.
    No physical successor leaf, Hensel itinerary, or global parity word is
    retained or replayed. Run count can grow linearly in the requested ticks;
    integer arithmetic cost also depends on intermediate operand widths.
    """
    if type(seed) is not int or seed <= 0:
        raise ValueError("Collatz temporal quotient requires a positive seed")
    if type(physical_ticks) is not int or physical_ticks < 0:
        raise ValueError("Collatz temporal quotient requires nonnegative ticks")
    if type(ledger) is not ResourceLedger:
        raise TypeError("Collatz temporal quotient requires its resource ledger")

    if type(include_f5) is not bool:
        raise TypeError("F5 projection selection must be Boolean")
    if type(shared_cache) is not bool:
        raise TypeError("shared cache flag must be Boolean")
    if type(include_width_spine) is not bool:
        raise TypeError("width-spine demand must be Boolean")
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
    )

    macros = (
        CollatzDyadicMacros(ledger, shared_cache=True)
        if shared_cache and seed.bit_length() >= 64
        else None
    )
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    with scratch.scope(), macros if macros is not None else nullcontext():
        control_bits = max(1, physical_ticks.bit_length())
        scratch.require_bits(8 * (seed.bit_length() + 4 * control_bits + 16))
        ledger.bump("collatz_physical_temporal_run_quotient_compilations")
        current = seed
        remaining = physical_ticks
        # Deterministic source selection composes only the selected finite action.
        # Anonymous root fibers are an optional audit API, never source authority.
        normalized_f5 = CollatzF5AffineAction.identity() if include_f5 else None
        physical_f5 = CollatzF5AffineAction.identity() if include_f5 else None
        odd_ticks = division_ticks = normalized = phase = 0
        run_actions = zero_symbols = one_symbols = cycle_repetitions = 0
        width_spine = CollatzWidthSpineAccumulator(
            ledger, requested=include_width_spine
        )

        d8_table: D8TemporalTable | None = None
        lookup_enabled = macros is not None
        previous_source, previous_width, previous_ones = seed, 0, 0
        share_width = 1 << (
            min(max(8, seed.bit_length()), max(8, physical_ticks // 2)).bit_length() - 1
        )
        discovery_before = ledger.counters.get(
            "collatz_physical_temporal_d8_discovery_symbols", 0
        )

        while remaining:
            scratch.require_bits(8 * (current.bit_length() + 4 * control_bits + 16))
            if macros is not None and previous_width < normalized <= share_width:
                macros.observe(
                    previous_source,
                    normalized - previous_width,
                    one_symbols - previous_ones,
                    current,
                    anchor=seed,
                    tape_width_summary=width_spine.segment_summary(
                        previous_source.bit_length(),
                        current.bit_length(),
                        normalized - previous_width,
                        one_symbols - previous_ones,
                    ),
                )
                width_spine.reset_segment()
            previous_source, previous_width, previous_ones = (
                current,
                normalized,
                one_symbols,
            )
            if current == 1 and remaining >= 3:
                repetitions, tail = divmod(remaining, 3)
                if repetitions:
                    cycle_repetitions += repetitions
                    odd_ticks += repetitions
                    division_ticks += 2 * repetitions
                    normalized += 2 * repetitions
                    one_symbols += repetitions
                    zero_symbols += repetitions
                    run_actions += 1
                    if normalized_f5 is not None and physical_f5 is not None:
                        cycle_f5 = _CYCLE_F5.power(repetitions)
                        normalized_f5 = normalized_f5.then(cycle_f5)
                        physical_f5 = physical_f5.then(cycle_f5)
                    if width_spine.complete:
                        cycle_blank = BlankLedger(0, 0, 2)
                        charge_width_repeat(ledger, cycle_blank, repetitions)
                        width_spine.record(cycle_blank.repeat(repetitions))
                    remaining = tail
                    ledger.bump("collatz_physical_temporal_cycle_pump_requests")
                    ledger.bump(
                        "collatz_physical_temporal_cycle_pump_repetitions", repetitions
                    )
                    if not remaining:
                        break

            if (
                lookup_enabled
                and macros is not None
                and remaining >= 16
                and current.bit_length() >= 64
                and _bounded_run_length(current & 255) < 8
            ):
                # A normalized symbol costs at least one physical tick. Admit
                # the exact retained odd count before applying a cached block.
                # Endpoint >2 proves no earlier normalized cycle entry.
                limit = min(remaining, max(8, current.bit_length()))
                width = 1 << (limit.bit_length() - 1)
                scratch.require_bits(16 * (current.bit_length() + 2 * width + 32))
                if include_width_spine and width_spine.complete:
                    selected_with_width = macros.lookup_largest_with_width(
                        current, width, remaining
                    )
                    if selected_with_width is None:
                        cell = None
                        macro_width = None
                        lookup_enabled = False
                    else:
                        cell, macro_width = selected_with_width
                else:
                    cell = macros.lookup_largest(current, width, remaining)
                    macro_width = None
                    if cell is None:
                        lookup_enabled = False
                endpoint = cell.apply(current) if cell is not None else 0
                if cell is not None and endpoint > 2:
                    width = cell.width
                    # Consume at most one retained occurrence per query route;
                    # subsequent discovery may publish bounded interior joins.
                    lookup_enabled = False
                    if normalized_f5 is not None and physical_f5 is not None:
                        # Every admitted width is dyadic and >=8, hence a
                        # multiple of four: 2**width == 1 in F5. Both the
                        # centered gain and translated offset need no division.
                        normalized_f5, physical_f5 = _append_dyadic_f5(
                            normalized_f5,
                            physical_f5,
                            cell.multiplier,
                            cell.target_origin,
                            cell.residue,
                        )
                    if include_width_spine and width_spine.complete:
                        if macro_width is None:
                            width_spine.invalidate()
                        else:
                            if (
                                macro_width.source_width != current.bit_length()
                                or macro_width.normalized_symbols != width
                                or macro_width.odd_steps != cell.odd_symbols
                                or macro_width.physical_ticks
                                != width + cell.odd_symbols
                                or macro_width.target_width != endpoint.bit_length()
                            ):
                                raise ValueError(
                                    "cached Collatz width spine differs from macro"
                                )
                            width_spine.record(macro_width.blank)
                    current = endpoint
                    odd_ticks += cell.odd_symbols
                    division_ticks += width
                    normalized += width
                    one_symbols += cell.odd_symbols
                    zero_symbols += width - cell.odd_symbols
                    remaining -= width + cell.odd_symbols
                    macros.applied()
                    run_actions += 1
                    ledger.bump(
                        "collatz_physical_temporal_run_operand_bits",
                        cell.multiplier.bit_length()
                        + endpoint.bit_length()
                        + cell.residue.bit_length(),
                    )
                    continue

            low = current & 255
            available = _bounded_run_length(low)
            homogeneous_symbols = min(
                available, remaining // 2 if low & 1 else remaining
            )
            if remaining >= 8 and homogeneous_symbols < 8:
                scratch.require_bits(8 * (current.bit_length() + 4 * control_bits + 32))
                if d8_table is None:
                    d8_table = D8TemporalTable.for_ledger(ledger)
                if current.bit_length() <= _MIN_CYLINDER_SOURCE_BITS or remaining < 32:
                    # Small exact states retain the cheaper direct finite row.
                    # There is no wide high fiber for a cursor to save here.
                    ones, target_origin = d8_table.select(current)
                    if remaining >= 8 + ones:
                        multiplier = 3**ones
                        endpoint = target_origin + multiplier * (current >> 8)
                        ledger.bump(
                            "collatz_physical_temporal_run_operand_bits",
                            current.bit_length() + endpoint.bit_length() + 26,
                        )
                        ledger.bump("collatz_physical_temporal_d8_endpoint_evaluations")
                        if endpoint > 2:
                            if include_width_spine and width_spine.complete:
                                d8_frame = D8CylinderFrame(current)
                                advanced = D8CylinderFrame(
                                    current, 8, target_origin, multiplier
                                )
                                d8_width = d8_table._width_summary_for_transition(
                                    d8_frame, advanced, ones, current.bit_length()
                                )
                                width_spine.record(d8_width.blank)
                            if normalized_f5 is not None and physical_f5 is not None:
                                normalized_f5, physical_f5 = _append_dyadic_f5(
                                    normalized_f5,
                                    physical_f5,
                                    multiplier,
                                    target_origin,
                                    low,
                                )
                            current = endpoint
                            odd_ticks += ones
                            division_ticks += 8
                            normalized += 8
                            one_symbols += ones
                            zero_symbols += 8 - ones
                            remaining -= 8 + ones
                            run_actions += 1
                            ledger.bump("collatz_physical_temporal_dyadic_d8_pumps")
                            ledger.bump("collatz_physical_temporal_dyadic_symbols", 8)
                            continue
                else:
                    frame = D8CylinderFrame(current)
                    frame_width = current.bit_length()
                    ledger.bump("collatz_physical_temporal_d8_source_window_bits", 8)
                    accepted = 0
                    # This bounded cursor consumes source windows, not a sequence
                    # of full intermediate integer endpoints. After the source
                    # tail is exhausted, the ordinary exact run owner resumes.
                    while (
                        remaining >= 8
                        and frame.consumed < _MAX_CYLINDER_BATCH_SYMBOLS
                        and frame.consumed < frame.source.bit_length()
                    ):
                        frame_bits = max(
                            frame.origin.bit_length(), frame.gain.bit_length()
                        )
                        scratch.require_bits(
                            8
                            * (
                                current.bit_length()
                                + frame_bits
                                + 4 * control_bits
                                + 48
                            )
                        )
                        local = frame.local_word()
                        residue = local & 255
                        ledger.bump(
                            "collatz_physical_temporal_d8_frame_operand_bits",
                            local.bit_length() + frame.gain.bit_length(),
                        )
                        capped = _bounded_run_length(residue)
                        homogeneous = min(
                            capped, remaining // 2 if residue & 1 else remaining
                        )
                        if homogeneous >= 8:
                            break
                        advanced, ones, residue, target_origin = d8_table.transition(
                            frame
                        )
                        if remaining < 8 + ones:
                            break
                        # Normalized dynamics remain in {1, 2} after first hitting
                        # 1. Preserve the earliest physical cycle entry for the
                        # scheduler's bounded support/audit prefix by letting the
                        # existing runs reach that boundary.
                        if advanced.source.bit_length() <= advanced.consumed + 2:
                            ledger.bump(
                                "collatz_physical_temporal_d8_endpoint_evaluations"
                            )
                        if not advanced.above_cycle():
                            break
                        if include_width_spine and width_spine.complete:
                            d8_width = d8_table._width_summary_for_transition(
                                frame, advanced, ones, frame_width
                            )
                            width_spine.record(d8_width.blank)
                            frame_width = d8_width.target_width
                        if normalized_f5 is not None and physical_f5 is not None:
                            multiplier = 3**ones
                            normalized_f5, physical_f5 = _append_dyadic_f5(
                                normalized_f5,
                                physical_f5,
                                multiplier,
                                target_origin,
                                residue,
                            )
                        frame = advanced
                        accepted += 1
                        odd_ticks += ones
                        division_ticks += 8
                        normalized += 8
                        one_symbols += ones
                        zero_symbols += 8 - ones
                        remaining -= 8 + ones
                        run_actions += 1
                        ledger.bump("collatz_physical_temporal_dyadic_d8_pumps")
                        ledger.bump("collatz_physical_temporal_dyadic_symbols", 8)
                    if accepted:
                        scratch.require_bits(
                            8
                            * (
                                current.bit_length()
                                + frame.gain.bit_length()
                                + 4 * control_bits
                                + 48
                            )
                        )
                        current = frame.materialize()
                        ledger.bump(
                            "collatz_physical_temporal_d8_frame_materializations"
                        )
                        ledger.bump("collatz_physical_temporal_d8_endpoint_evaluations")
                        ledger.bump(
                            "collatz_physical_temporal_run_operand_bits",
                            frame.source.bit_length()
                            + frame.gain.bit_length()
                            + current.bit_length(),
                        )
                        continue

            if low in (0, 255):
                available = v2_positive(current + 1 if current & 1 else current)

            if current & 1 == 0:
                length = min(available, remaining)
                before_bits = current.bit_length()
                current >>= length
                if width_spine.complete:
                    after_bits = current.bit_length()
                    segment = BlankLedger(
                        after_bits - before_bits,
                        min(0, after_bits - before_bits),
                        max(0, after_bits - before_bits),
                    )
                    width_spine.record(segment)
                if normalized_f5 is not None and physical_f5 is not None:
                    f5 = _run_zero_f5(length)
                    normalized_f5 = normalized_f5.then(f5)
                    physical_f5 = physical_f5.then(f5)
                remaining -= length
                division_ticks += length
                normalized += length
                zero_symbols += length
                run_actions += 1
                ledger.bump("collatz_physical_temporal_zero_run_pumps")
                ledger.bump("collatz_physical_temporal_zero_run_symbols", length)
                ledger.bump(
                    "collatz_physical_temporal_run_operand_bits",
                    before_bits + current.bit_length() + length.bit_length(),
                )
                continue

            complete = min(available, remaining // 2)
            if complete:
                scratch.require_bits(
                    8 * (current.bit_length() + 2 * complete + 4 * control_bits + 16)
                )
                before_bits = current.bit_length()
                power3 = 3**complete
                current = power3 * ((current + 1) >> complete) - 1
                if width_spine.complete:
                    displacement = current.bit_length() - before_bits
                    # Every normalized odd boundary grows monotonically; the
                    # raw 3*x+1 cell is at most one bit above the final
                    # normalized boundary of this maximal odd run.
                    segment = BlankLedger(displacement, 0, displacement + 1)
                    width_spine.record(segment)
                if normalized_f5 is not None and physical_f5 is not None:
                    f5 = _run_one_f5(complete)
                    normalized_f5 = normalized_f5.then(f5)
                    physical_f5 = physical_f5.then(f5)
                remaining -= 2 * complete
                odd_ticks += complete
                division_ticks += complete
                normalized += complete
                one_symbols += complete
                run_actions += 1
                ledger.bump("collatz_physical_temporal_one_run_pumps")
                ledger.bump("collatz_physical_temporal_one_run_symbols", complete)
                ledger.bump(
                    "collatz_physical_temporal_run_operand_bits",
                    before_bits
                    + power3.bit_length()
                    + current.bit_length()
                    + complete.bit_length(),
                )
            if remaining:
                if complete >= available or remaining != 1 or not current & 1:
                    continue
                scratch.require_bits(8 * (current.bit_length() + 4 * control_bits + 18))
                before_bits = current.bit_length()
                ledger.bump(
                    "collatz_physical_temporal_run_operand_bits",
                    current.bit_length() + 2,
                )
                current = 3 * current + 1
                if width_spine.complete:
                    displacement = current.bit_length() - before_bits
                    segment = BlankLedger(
                        displacement,
                        min(0, displacement),
                        max(0, displacement),
                    )
                    width_spine.record(segment)
                if physical_f5 is not None:
                    physical_f5 = physical_f5.then(ODD_HALF_F5)
                odd_ticks += 1
                remaining = 0
                phase = 1
                run_actions += 1
                ledger.bump("collatz_physical_temporal_odd_half_steps")

        if macros is not None:
            if phase == 0 and previous_width < normalized <= share_width:
                macros.observe(
                    previous_source,
                    normalized - previous_width,
                    one_symbols - previous_ones,
                    current,
                    anchor=seed,
                    tape_width_summary=width_spine.segment_summary(
                        previous_source.bit_length(),
                        current.bit_length(),
                        normalized - previous_width,
                        one_symbols - previous_ones,
                    ),
                )
            macros._bump(
                "primitive_steps",
                ledger.counters.get("collatz_physical_temporal_d8_discovery_symbols", 0)
                - discovery_before,
            )
        certificate = None
        ledger.bump("collatz_physical_temporal_run_actions", run_actions)
        ledger.bump("collatz_physical_temporal_normalized_symbols", normalized)
        ledger.bump("collatz_physical_temporal_odd_ticks", odd_ticks)
        ledger.bump("collatz_physical_temporal_division_ticks", division_ticks)
        ledger.bump(
            "collatz_physical_temporal_endpoint_operand_bits", current.bit_length()
        )

        tape_width_summary = width_spine.finish(
            seed.bit_length(),
            current.bit_length(),
            physical_ticks,
            division_ticks,
            odd_ticks,
        )

        return CollatzTemporalRunQuotient(
            seed,
            physical_ticks,
            current,
            odd_ticks,
            division_ticks,
            normalized,
            phase,
            run_actions,
            zero_symbols,
            one_symbols,
            cycle_repetitions,
            normalized_f5,
            physical_f5,
            certificate,
            tape_width_summary,
        )


__all__ = [
    "F5_AFFINE_ALPHABET",
    "HENSEL_ONE_F5",
    "HENSEL_ZERO_F5",
    "ODD_HALF_F5",
    "CollatzAnonymousF5Fiber",
    "CollatzF5AffineAction",
    "CollatzPoweredRootVietaProgram",
    "CollatzRootFiberCertificate",
    "CollatzTemporalRunQuotient",
    "compile_collatz_temporal_run_quotient",
    "root_fiber_certificate",
]
