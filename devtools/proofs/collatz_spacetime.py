"""Exact Collatz endpoints and source-backed lazy carry programs.

Powered execution retains the immutable input and Mul3Add1/Shift action DAGs.
Finite three-carry range observations discover valuations without packing
source or affine-offset prefixes into integers. Explicit field-return APIs
lower the requested endpoint once; point and width adapters use lazy views.
The original forcing morphism remains available as an explicit diagnostic.
"""

from __future__ import annotations

from collections import OrderedDict
from dataclasses import dataclass

from devtools.proofs.collatz_forcing_morphism import (
    CollatzForcingMorphismArena,
    CollatzForcingOccurrence,
)
from devtools.proofs.collatz_semantic_action import CollatzBlockActionArena
from devtools.proofs.collatz_symbolic_action import CollatzSymbolicActionArena
from devtools.proofs.lazy_collatz import LazyCollatzApplication, LazyCollatzResult
from number_compiler.arithmetic.automata.action_power import ActionPowerArena
from number_compiler.arithmetic.automata.symmetry_powering import (
    BinaryLiftMetrics,
    FiniteKernel,
)
from number_compiler.arithmetic.contracts.scoped_handles import LoweringCapability
from number_compiler.arithmetic.contracts.successor_congruence import (
    SuccessorCongruenceAudit,
)
from number_compiler.arithmetic.fields.causal_domain import (
    CanonicalDomainArena,
    NormalizedDomainFrame,
    collatz_digit_codec,
)
from number_compiler.arithmetic.fields.directed_field import DirectedTileTransducerArena
from number_compiler.arithmetic.fields.dyadic_tile import (
    DyadicChunk,
    DyadicSpan,
    DyadicTile,
    append_symbol,
    first_symbol,
    iter_symbols,
    slice_span,
    source_span,
)
from number_compiler.arithmetic.fields.radix import digits_lsd, value_from_lsd_digits
from number_compiler.sequences.collatz.power import CollatzEventArena, CollatzEventNode


@dataclass(frozen=True, slots=True)
class _TileSummary:
    length: int
    all_sentinel: bool
    first_mismatch: int | None
    any_nonzero: bool
    last_nonzero: int | None


class _RadixSummaryArena:
    __slots__ = ("_cache", "sentinel")

    def __init__(self, sentinel: int = 1) -> None:
        self.sentinel = int(sentinel)
        self._cache: dict[int, _TileSummary] = {}

    def summary(self, tile: DyadicTile) -> _TileSummary:
        found = self._cache.get(tile.node_id)
        if found is not None:
            return found
        built: dict[int, _TileSummary] = {}
        stack: list[tuple[DyadicTile, bool]] = [(tile, False)]
        while stack:
            node, ready = stack.pop()
            cached = self._cache.get(node.node_id)
            if cached is not None:
                built[node.node_id] = cached
                continue
            if node.level == 0:
                if node.symbol is None:
                    raise AssertionError(node)
                symbol = int(node.symbol)
                summary = _TileSummary(
                    1,
                    symbol == self.sentinel,
                    None if symbol == self.sentinel else 0,
                    symbol != 0,
                    0 if symbol != 0 else None,
                )
                self._cache[node.node_id] = summary
                built[node.node_id] = summary
                continue
            if node.left is None or node.right is None:
                raise AssertionError(node)
            if not ready:
                stack.append((node, True))
                if (
                    node.right.node_id not in built
                    and node.right.node_id not in self._cache
                ):
                    stack.append((node.right, False))
                if (
                    node.left.node_id not in built
                    and node.left.node_id not in self._cache
                ):
                    stack.append((node.left, False))
                continue
            left = self._cache.get(node.left.node_id, built.get(node.left.node_id))
            right = self._cache.get(node.right.node_id, built.get(node.right.node_id))
            if left is None or right is None:
                raise AssertionError(node)
            first = (
                left.first_mismatch
                if left.first_mismatch is not None
                else None
                if right.first_mismatch is None
                else left.length + right.first_mismatch
            )
            last = (
                left.last_nonzero
                if right.last_nonzero is None
                else left.length + right.last_nonzero
            )
            summary = _TileSummary(
                left.length + right.length,
                left.all_sentinel and right.all_sentinel,
                first,
                left.any_nonzero or right.any_nonzero,
                last,
            )
            self._cache[node.node_id] = summary
            built[node.node_id] = summary
        return self._cache[tile.node_id]

    def first_mismatch(self, span: DyadicSpan) -> int | None:
        offset = 0
        for chunk in span.chunks:
            summary = self.summary(chunk.tile)
            if summary.first_mismatch is not None:
                return offset + summary.first_mismatch
            offset += chunk.tile.width
        return None

    def last_nonzero(self, span: DyadicSpan) -> int | None:
        offset = span.length
        for chunk in reversed(span.chunks):
            offset -= chunk.tile.width
            summary = self.summary(chunk.tile)
            if summary.last_nonzero is not None:
                return offset + summary.last_nonzero
        return None

    @property
    def retained_entries(self) -> int:
        return len(self._cache)


class _Base4ShiftRightOneArena:
    """Map base-4 digits under integer ``>> 1`` with one higher-digit halo."""

    __slots__ = ("_cache", "hits", "requests")

    def __init__(self) -> None:
        self._cache: dict[int, dict[int, DyadicTile]] = {}
        self.requests = self.hits = 0

    def map_tile(self, tile: DyadicTile, higher_digit: int) -> DyadicTile:
        higher_digit = int(higher_digit)
        if not 0 <= higher_digit < 4:
            raise ValueError(higher_digit)
        self.requests += 1
        per = self._cache.get(tile.node_id)
        if per is not None and higher_digit in per:
            self.hits += 1
            return per[higher_digit]
        built: dict[tuple[int, int], DyadicTile] = {}
        stack: list[tuple[DyadicTile, int, bool]] = [(tile, higher_digit, False)]
        while stack:
            node, halo, ready = stack.pop()
            cached = self._cache.get(node.node_id)
            if cached is not None and halo in cached:
                built[(node.node_id, halo)] = cached[halo]
                continue
            if node.level == 0:
                if node.symbol is None:
                    raise AssertionError(node)
                digit = int(node.symbol)
                out = (digit >> 1) | ((halo & 1) << 1)
                from number_compiler.arithmetic.fields.dyadic_tile import leaf

                result = leaf(out)
                self._cache.setdefault(node.node_id, {})[halo] = result
                built[(node.node_id, halo)] = result
                continue
            if node.left is None or node.right is None:
                raise AssertionError(node)
            right_halo = halo
            left_halo = first_symbol(node.right)
            if not ready:
                stack.append((node, halo, True))
                if (node.right.node_id, right_halo) not in built and (
                    self._cache.get(node.right.node_id) is None
                    or right_halo not in self._cache[node.right.node_id]
                ):
                    stack.append((node.right, right_halo, False))
                if (node.left.node_id, left_halo) not in built and (
                    self._cache.get(node.left.node_id) is None
                    or left_halo not in self._cache[node.left.node_id]
                ):
                    stack.append((node.left, left_halo, False))
                continue
            left = self._cache.get(node.left.node_id, {}).get(
                left_halo, built.get((node.left.node_id, left_halo))
            )
            right = self._cache.get(node.right.node_id, {}).get(
                right_halo, built.get((node.right.node_id, right_halo))
            )
            if left is None or right is None:
                raise AssertionError(node)
            from number_compiler.arithmetic.fields.dyadic_tile import join

            result = join(left, right)
            self._cache.setdefault(node.node_id, {})[halo] = result
            built[(node.node_id, halo)] = result
        return self._cache[tile.node_id][higher_digit]

    def map_span(self, span: DyadicSpan) -> DyadicSpan:
        higher = 0
        chunks: list[DyadicChunk] = []
        for chunk in reversed(span.chunks):
            mapped = self.map_tile(chunk.tile, higher)
            chunks.append(DyadicChunk(chunk.start, mapped))
            higher = first_symbol(chunk.tile)
        chunks.reverse()
        return DyadicSpan(span.start, span.length, tuple(chunks))

    @property
    def retained_entries(self) -> int:
        return sum(len(per) for per in self._cache.values())


def _mul3_kernel() -> FiniteKernel:
    return FiniteKernel(
        3,
        4,
        lambda carry, digit: (3 * int(digit) + int(carry)) // 4,
        state_conjugate=(2, 1, 0),
        symbol_conjugate=(3, 2, 1, 0),
        name="collatz-radix4-mul3-carry",
    )


def _mul3_emit(carry: int, digit: int) -> int:
    return (3 * int(digit) + int(carry)) % 4


@dataclass(frozen=True, slots=True)
class CollatzRadixField:
    """One positive odd canonical radix-4 field.

    Spatial extent is derived from ``span``; no duplicate scalar length is
    retained in the field identity.
    """

    span: DyadicSpan

    def __post_init__(self) -> None:
        if self.span.start != 0 or self.span.length <= 0:
            raise ValueError((self.span.start, self.span.length))
        if not (first_symbol(self.span.chunks[0].tile) & 1):
            raise ValueError("Collatz radix field must encode an odd integer")

    @classmethod
    def from_value(cls, value: int) -> CollatzRadixField:
        value = int(value)
        if value <= 0 or not (value & 1):
            raise ValueError(value)
        digits = tuple(map(int, digits_lsd(value, 4)))
        return cls(source_span(digits, blank=0, logical_length=len(digits)))

    @classmethod
    def from_digits(cls, digits: tuple[int, ...]) -> CollatzRadixField:
        digits = tuple(map(int, digits))
        if not digits or any(not 0 <= d < 4 for d in digits) or not (digits[0] & 1):
            raise ValueError(digits)
        while len(digits) > 1 and digits[-1] == 0:
            digits = digits[:-1]
        return cls(source_span(digits, blank=0, logical_length=len(digits)))

    @property
    def domain(self) -> NormalizedDomainFrame:
        return NormalizedDomainFrame.prefix(self.span.length, self.span.length)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz-radix4-field", self.span.tile_ids)

    def digits(self) -> tuple[int, ...]:
        return tuple(iter_symbols(self.span))

    def value(self) -> int:
        return value_from_lsd_digits(self.digits(), 4)


@dataclass(frozen=True, slots=True)
class CollatzPhysicalField:
    """Canonical radix-4 field for one positive physical Collatz state.

    Unlike :class:`CollatzRadixField`, this carrier admits even states.  A
    physical tick is therefore a genuinely local choice: odd fields run the
    finite ``3*x+1`` transducer and even fields perform one structural /2
    coordinate shift.  Spatial extent is derived from the canonical span.
    """

    span: DyadicSpan

    def __post_init__(self) -> None:
        if self.span.start != 0 or self.span.length <= 0:
            raise ValueError((self.span.start, self.span.length))
        if _RadixSummaryArena().last_nonzero(self.span) is None:
            raise ValueError("physical Collatz field must be positive")

    @classmethod
    def from_value(cls, value: int) -> CollatzPhysicalField:
        value = int(value)
        if value <= 0:
            raise ValueError(value)
        digits = tuple(map(int, digits_lsd(value, 4)))
        return cls(source_span(digits, blank=0, logical_length=len(digits)))

    @classmethod
    def from_span(cls, span: DyadicSpan) -> CollatzPhysicalField:
        last = _RadixSummaryArena().last_nonzero(span)
        if last is None:
            raise ValueError("physical Collatz field must be positive")
        return cls(
            slice_span(span, span.start, span.start + last + 1, rebase_to_zero=True)
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz-physical-radix4", self.span.tile_ids)

    @property
    def odd(self) -> bool:
        return bool(first_symbol(self.span.chunks[0].tile) & 1)

    def digits(self) -> tuple[int, ...]:
        return tuple(iter_symbols(self.span))

    def value(self) -> int:
        return value_from_lsd_digits(self.digits(), 4)


@dataclass(frozen=True, slots=True)
class CollatzPhysicalAdvance:
    source: CollatzPhysicalField
    target: CollatzPhysicalField
    odd_event: int


@dataclass(frozen=True, slots=True)
class CollatzCausalAdvance:
    source: CollatzRadixField
    valuation: int
    frame_depth: int
    local_shift: int
    target: CollatzRadixField

    def __post_init__(self) -> None:
        if self.valuation != 2 * self.frame_depth + self.local_shift:
            raise ValueError(self)
        if self.local_shift not in (0, 1):
            raise ValueError(self)


@dataclass(frozen=True, slots=True)
class CollatzSpacetimeMetrics:
    primitive_field_steps: int
    primitive_physical_steps: int
    physical_jump_entries: int
    binary_lift: BinaryLiftMetrics
    summary_entries: int
    shift_entries: int
    shift_hits: int
    carry_projection_entries: int
    carry_projection_hits: int
    carry_unique_actions: int
    carry_action_alias_hits: int
    carry_mirror_alias_hits: int
    carry_conjugate_alias_hits: int
    event_nodes: int
    event_compositions: int
    domain_canonical_refs: int
    domain_mirror_hits: int
    domain_conjugate_hits: int
    finite_cell_alphabet: int
    carry_direction: str = "lsd-to-msd"
    primitive_forcing_steps: int = 0
    forcing_jump_entries: int = 0
    forcing_classes: int = 0
    forcing_frame_aliases: int = 0
    forcing_source_hits: int = 0
    forcing_action_aliases: int = 0
    forcing_occurrences: int = 0
    forcing_successor_conflicts: int = 0
    forcing_exact_target_conflicts: int = 0
    macro_actions: int = 0
    macro_compositions: int = 0
    macro_applications: int = 0
    nonlinear_branch_evaluations: int = 0
    exact_endpoint_entries: int = 0
    symbolic_port_queries: int = 0
    symbolic_maximum_port_bits: int = 0
    symbolic_retained_entries: int = 0


class CollatzCausalSpacetimeEngine:
    """Exact canonical-field Collatz lift with symbolic affine actions.

    ``max_jump_entries`` bounds the explicitly requested endpoint LRU.
    Original-source lazy applications retain symbolic programs independently;
    neither accelerated nor physical powering retains intermediate fields.
    """

    __slots__ = (
        "_action_applications",
        "_action_endpoints",
        "_advances",
        "_endpoint_cache_limit",
        "_lazy_applications",
        "_physical_advances",
        "action_power",
        "codec",
        "domains",
        "event_arena",
        "forcing",
        "forcing_actions",
        "forcing_congruence",
        "mul3",
        "nonlinear_branch_evaluations",
        "primitive_field_steps",
        "primitive_forcing_steps",
        "primitive_physical_steps",
        "shift",
        "summary",
        "symbolic_actions",
    )

    def __init__(
        self,
        *,
        max_jump_entries: int = 8192,
        event_arena: CollatzEventArena | None = None,
    ) -> None:
        self.summary = _RadixSummaryArena(1)
        self.shift = _Base4ShiftRightOneArena()
        self.mul3 = DirectedTileTransducerArena(
            _mul3_kernel(),
            _mul3_emit,
            output_alphabet_size=4,
        )
        self.codec = collatz_digit_codec(4)
        # Populate the finite active digit alphabet and one inactive exterior
        # symbol so its boundedness is explicit and testable.
        from number_compiler.arithmetic.fields.causal_domain import DomainCell

        for digit in range(4):
            self.codec.intern(DomainCell(self.codec.family, True, digit))
        self.codec.intern(DomainCell(self.codec.family, False, 0))
        self.domains = CanonicalDomainArena(self.codec)
        self.event_arena = CollatzEventArena() if event_arena is None else event_arena
        if not isinstance(self.event_arena, CollatzEventArena):
            raise TypeError(type(self.event_arena))
        self.forcing_actions = CollatzBlockActionArena(self.mul3)
        self.forcing = CollatzForcingMorphismArena(self.forcing_actions)
        self.primitive_field_steps = 0
        self.primitive_physical_steps = 0
        self.primitive_forcing_steps = 0
        self.forcing_congruence = SuccessorCongruenceAudit()
        self._physical_advances: dict[tuple[object, ...], CollatzPhysicalAdvance] = {}
        self._advances: dict[tuple[object, ...], CollatzCausalAdvance] = {}
        self.symbolic_actions = CollatzSymbolicActionArena()
        self.action_power = ActionPowerArena(
            self.symbolic_actions.identity,
            self.symbolic_actions.compose,
            validate=self.symbolic_actions.validate,
            composition_cache=self.symbolic_actions.composition_cache,
        )
        self._endpoint_cache_limit = max(0, int(max_jump_entries))
        self._action_applications = 0
        self._action_endpoints: OrderedDict[
            tuple[tuple[object, ...], int], tuple[CollatzRadixField, CollatzEventNode]
        ] = OrderedDict()
        self.nonlinear_branch_evaluations = 0

        self._lazy_applications: dict[tuple[object, ...], LazyCollatzApplication] = {}

    def _observe_domain(self, span: DyadicSpan) -> None:
        for chunk in span.chunks:
            self.domains.canonical_ref(chunk.tile)

    def _mul3_plus_one(self, tail: DyadicSpan) -> DyadicSpan:
        out, carry = self.mul3.project_span(tail, 1)
        if carry:
            out = append_symbol(out, carry)
        return out

    def _trim_high_zeroes(self, span: DyadicSpan) -> DyadicSpan:
        last = self.summary.last_nonzero(span)
        if last is None:
            raise AssertionError("positive Collatz field became zero")
        trimmed = slice_span(
            span, span.start, span.start + last + 1, rebase_to_zero=True
        )
        return trimmed

    def advance_physical(self, field: CollatzPhysicalField) -> CollatzPhysicalAdvance:
        key = field.canonical_key
        found = self._physical_advances.get(key)
        if found is not None:
            return found
        self.primitive_physical_steps += 1
        if field.odd:
            raw = self._mul3_plus_one(field.span)
            target = CollatzPhysicalField.from_span(raw)
            odd_event = 1
        else:
            raw = self.shift.map_span(field.span)
            raw = self._trim_high_zeroes(raw)
            target = CollatzPhysicalField.from_span(raw)
            odd_event = 0
        advance = CollatzPhysicalAdvance(field, target, odd_event)
        self._physical_advances[key] = advance
        return advance

    def _lazy_application(self, span: DyadicSpan) -> LazyCollatzApplication:
        key: tuple[object, ...] = ("collatz-source", span.tile_ids)
        found = self._lazy_applications.get(key)
        if found is not None:
            return found
        bits = tuple(
            bit for digit in iter_symbols(span) for bit in (digit & 1, (digit >> 1) & 1)
        )
        out = LazyCollatzApplication(2, 0, bits)
        self._lazy_applications[key] = out
        return out

    @staticmethod
    def _lower_lazy(
        application: LazyCollatzApplication, result: LazyCollatzResult
    ) -> DyadicSpan:
        bits = application.materialize_bits(
            result.view, LoweringCapability(application.token)
        )
        digits = tuple(
            bits[i] + (2 * bits[i + 1] if i + 1 < len(bits) else 0)
            for i in range(0, len(bits), 2)
        )
        return source_span(digits, blank=0, logical_length=len(digits))

    def _lazy_events(self, result: LazyCollatzResult) -> CollatzEventNode:
        node = self.event_arena.identity
        for valuation in result.valuations:
            node = self.event_arena.concat(node, self.event_arena.event(valuation))
        if result.repeated_twos:
            node = self.event_arena.concat(
                node,
                self.event_arena.power(self.event_arena.event(2), result.repeated_twos),
            )
        return node

    def advance_physical_power(
        self,
        field: CollatzPhysicalField,
        steps: int,
    ) -> tuple[CollatzPhysicalField, tuple[int, int]]:
        application = self._lazy_application(field.span)
        result = application.advance_physical(int(steps))
        target = CollatzPhysicalField.from_span(self._lower_lazy(application, result))
        return target, (int(steps), result.odd_ticks)

    def _forcing_image_with_valuation(
        self,
        field: CollatzRadixField,
    ) -> tuple[CollatzForcingOccurrence, int]:
        """Return normalized occurrence plus the removable-frame cocycle weight.

        The unbounded radix-4 frame depth is deliberately not retained by the
        occurrence.  It is consumed here into the integer event weight and then
        discarded.  Equal normalized tails reached through different ``1**q``
        frames therefore share one exact occurrence and one target cache entry.
        """
        first = self.summary.first_mismatch(field.span)
        if first is None:
            q = int(field.span.length)
            occurrence = self.forcing.intern(
                field.canonical_key,
                frame_depth=q,
                tail=None,
            )
            return occurrence, 2 * q
        q = int(first)
        tail = slice_span(field.span, q, field.span.length, rebase_to_zero=True)
        occurrence = self.forcing.intern(
            field.canonical_key,
            frame_depth=q,
            tail=tail,
        )
        valuation = 2 * q + occurrence.forcing.local_shift
        if valuation <= 0:
            raise AssertionError((q, occurrence.forcing.local_shift))
        return occurrence, valuation

    def forcing_image_with_valuation(
        self,
        field: CollatzRadixField,
    ) -> tuple[CollatzForcingOccurrence, int]:
        """Public normalized-state projection plus exact valuation cocycle."""
        return self._forcing_image_with_valuation(field)

    def forcing_image(self, field: CollatzRadixField) -> CollatzForcingOccurrence:
        """Return only the bounded normalized state; frame depth is a weight."""
        return self._forcing_image_with_valuation(field)[0]

    def advance(self, field: CollatzRadixField) -> CollatzCausalAdvance:
        key = field.canonical_key
        found = self._advances.get(key)
        if found is not None:
            return found
        self.primitive_field_steps += 1
        self._observe_domain(field.span)
        first = self.summary.first_mismatch(field.span)
        if first is None:
            # Source is the exact finite fixed-point frame 11..11_4; the
            # accelerated target is 1 after removing 2*width factors of two.
            target = CollatzRadixField.from_digits((1,))
            self._observe_domain(target.span)
            advance = CollatzCausalAdvance(
                field, 2 * field.span.length, field.span.length, 0, target
            )
            self._advances[key] = advance
            return advance

        q = int(first)
        tail = slice_span(field.span, q, field.span.length, rebase_to_zero=True)
        low_digit = first_symbol(tail.chunks[0].tile)
        local_shift = int(low_digit == 3)
        if low_digit == 1 or not 0 <= low_digit < 4:
            raise AssertionError((q, low_digit))

        raw = self._mul3_plus_one(tail)
        if local_shift:
            raw = self.shift.map_span(raw)
        raw = self._trim_high_zeroes(raw)
        target = CollatzRadixField(raw)
        valuation = 2 * q + local_shift
        if valuation <= 0:
            raise AssertionError((q, local_shift))
        if not (first_symbol(target.span.chunks[0].tile) & 1):
            raise AssertionError("accelerated Collatz target must remain odd")
        self._observe_domain(target.span)
        advance = CollatzCausalAdvance(field, valuation, q, local_shift, target)
        self._advances[key] = advance
        return advance

    def advance_physical_steps_quotient(
        self,
        field: CollatzPhysicalField,
        steps: int,
    ) -> tuple[CollatzPhysicalField, CollatzEventNode, int]:
        """Explicit endpoint lowering of a lazy physical shift/event schedule."""
        application = self._lazy_application(field.span)
        result = application.advance_physical(int(steps))
        target = CollatzPhysicalField.from_span(self._lower_lazy(application, result))
        if not field.odd:
            # Preserve the legacy quotient metadata for even input fields.
            return target, self.event_arena.identity, int(steps)
        return target, self._lazy_events(result), result.partial_ticks

    def advance_event_power(
        self,
        field: CollatzRadixField,
        events: int,
    ) -> tuple[CollatzRadixField, CollatzEventNode]:
        """Explicit endpoint output, discovered through a lazy source program."""
        events = int(events)
        if events < 0:
            raise ValueError(events)
        if events == 0:
            return field, self.event_arena.identity
        key = field.canonical_key, events
        cached = self._action_endpoints.get(key)
        if cached is not None:
            self._action_endpoints.move_to_end(key)
            return cached
        application = self._lazy_application(field.span)
        result = application.advance_events(events)
        target = CollatzRadixField(self._lower_lazy(application, result))
        node = self._lazy_events(result)
        self._action_applications += 1
        if self._endpoint_cache_limit:
            self._action_endpoints[key] = (target, node)
            self._action_endpoints.move_to_end(key)
            while len(self._action_endpoints) > self._endpoint_cache_limit:
                self._action_endpoints.popitem(last=False)
        return target, node

    def advance_power(
        self,
        field: CollatzRadixField,
        events: int,
    ) -> tuple[CollatzRadixField, tuple[int, int]]:
        target, node = self.advance_event_power(field, events)
        return target, (node.effect.events, node.effect.shift)

    def advance_value(self, value: int, events: int) -> tuple[int, tuple[int, int]]:
        target, weight = self.advance_power(CollatzRadixField.from_value(value), events)
        return target.value(), weight

    def metrics(self) -> CollatzSpacetimeMetrics:
        cm = self.mul3.metrics()
        dm = self.domains.metrics()
        fm = self.forcing.metrics()
        powers = self.action_power.metrics()
        lazy = [app.metrics() for app in self._lazy_applications.values()]
        branches = sum(item["nonlinear_branch_evaluations"] for item in lazy)
        lift = BinaryLiftMetrics(
            branches,
            powers.power_requests,
            powers.power_hits,
            powers.composition_entries + powers.power_entries,
        )
        return CollatzSpacetimeMetrics(
            self.primitive_field_steps,
            self.primitive_physical_steps,
            0,
            lift,
            self.summary.retained_entries,
            self.shift.retained_entries,
            self.shift.hits,
            cm.projection_entries,
            cm.projection_hits,
            cm.unique_actions,
            cm.action_alias_hits,
            cm.mirror_alias_hits,
            cm.conjugate_alias_hits,
            self.event_arena.node_count,
            self.event_arena.composition_operations,
            int(dm["canonical_refs"]),
            int(dm["mirror_hits"]),
            int(dm["conjugate_hits"]),
            self.codec.alphabet_size,
            str(dm["carry_direction"]),
            self.primitive_forcing_steps,
            lift.jump_entries,
            fm.forcing_classes,
            fm.frame_aliases,
            fm.source_hits,
            fm.action_aliases,
            fm.normalized_occurrences,
            self.forcing_congruence.metrics().successor_conflicts,
            self.forcing_congruence.metrics().exact_target_conflicts,
            sum(item["macro_actions"] for item in lazy),
            sum(item["macro_compositions"] for item in lazy),
            self._action_applications,
            branches,
            len(self._action_endpoints),
            sum(item["symbolic_port_queries"] for item in lazy),
            max((item["symbolic_maximum_port_bits"] for item in lazy), default=0),
            # The shared composition interner is charged by forcing_jump_entries.
            sum(item["retained_entries"] for item in lazy),
        )


__all__ = [
    "CollatzCausalAdvance",
    "CollatzCausalSpacetimeEngine",
    "CollatzPhysicalAdvance",
    "CollatzPhysicalField",
    "CollatzRadixField",
    "CollatzSpacetimeMetrics",
]
