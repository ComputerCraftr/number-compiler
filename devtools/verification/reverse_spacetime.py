"""Proof-only exact reverse/add fields and carry spacetime reference steps.

The physical carry is computed exactly once, from least-significant to
most-significant position, by :class:`DirectedTileTransducerArena`.  The
right-hand carry terms required by reversal are then obtained by reflecting the
*already computed carry field*.  Reflection is therefore a coordinate/symmetry
view, never a second carry propagating from MSD toward LSD.

Absolute width and growth live in :class:`DyadicSpan` geometry.  Active pair
cells use the fixed alphabet ``0..2*(base-1)`` and are canonicalized under the
causal mirror/value-conjugacy subgroup.  The module exposes binary lifting over
canonical whole fields as a correctness/performance baseline; its metrics keep
first-use distinct-field growth visible rather than calling it a proof of
logarithmic temporal closure.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field

from devtools.verification import require_exact_oracle
from devtools.verification.carry_action_quotient import CarryActionQuotientArena
from devtools.verification.forcing_morphism import (
    ReverseAddForcingMorphismArena,
    ReverseAddForcingOccurrence,
)
from devtools.verification.lazy_reverse import LazyReverseApplication
from devtools.verification.reverse_action import (
    ReverseAddMacroActionArena,
    reconstruct_slab_span,
)
from devtools.verification.semantic_action import ReverseAddAffineActionArena
from devtools.verification.temporal_quotient import ReverseAddCarryCutState
from number_compiler.arithmetic.automata.symmetry_powering import (
    BinaryLiftEngine,
    BinaryLiftMetrics,
)
from number_compiler.arithmetic.carry.carry_symmetry import reverse_add_carry_kernel
from number_compiler.arithmetic.carry.event_memory import event_memory_horizon
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.arithmetic.contracts.successor_congruence import (
    SuccessorCongruenceAudit,
    SuccessorObservation,
)
from number_compiler.arithmetic.fields.causal_domain import (
    CanonicalDomainArena,
    NormalizedDomainFrame,
    reverse_pair_codec,
)
from number_compiler.arithmetic.fields.directed_field import DirectedTileTransducerArena
from number_compiler.arithmetic.fields.dyadic_tile import (
    DyadicChunk,
    DyadicSpan,
    append_symbol,
    concat,
    first_symbol,
    iter_symbols,
    leaf,
    prepend_symbol,
    rebase,
    source_span,
)
from number_compiler.arithmetic.fields.radix import digits_lsd, value_from_lsd_digits
from number_compiler.resources.ledger import ResourceLedger


def _validated_power_steps(actual_base: int, expected_base: int, steps: int) -> int:
    """Validate a reference field's base and return its nonnegative step count."""
    if actual_base != expected_base:
        raise ValueError((actual_base, expected_base))
    steps = int(steps)
    if steps < 0:
        raise ValueError(steps)
    return steps


def _pair_values_from_integer(value: int, base: int) -> tuple[int, ...]:
    require_exact_oracle()
    value, base = int(value), int(base)
    if value < 0 or base < 2:
        raise ValueError((value, base))
    digits = tuple(map(int, digits_lsd(value, base)))
    return tuple(digits[i] + digits[-1 - i] for i in range(len(digits)))


def _carry_emit(base: int) -> Callable[[int, int], int]:
    require_exact_oracle()
    base = int(base)

    def emit(carry: int, symbol: int) -> int:
        require_exact_oracle()
        symbol = int(symbol)
        if not 0 <= symbol <= 2 * (base - 1):
            raise ValueError(symbol)
        return int(symbol + int(carry) >= base)

    return emit


def _digit_emit(base: int) -> Callable[[int, int], int]:
    require_exact_oracle()
    base = int(base)

    def emit(carry: int, symbol: int) -> int:
        require_exact_oracle()
        symbol = int(symbol)
        if not 0 <= symbol <= 2 * (base - 1):
            raise ValueError(symbol)
        return (symbol + int(carry)) % base

    return emit


@dataclass(frozen=True, slots=True)
class ReverseAddPairField:
    """One exact symmetric pair field ``S_i=d_i+d_(d-1-i)``.

    Spatial extent belongs to the canonical dyadic span.  Do not retain a
    second scalar ``active_length`` field that can drift into temporal keys.
    """

    base: int
    span: DyadicSpan

    def __post_init__(self) -> None:
        require_exact_oracle()
        base = int(self.base)
        if base < 2 or self.span.start != 0 or self.span.length <= 0:
            raise ValueError((self.base, self.span.start, self.span.length))

    @classmethod
    def from_value(cls, value: int, *, base: int = 10) -> ReverseAddPairField:
        require_exact_oracle()
        pair = _pair_values_from_integer(value, base)
        return cls(int(base), source_span(pair, blank=0, logical_length=len(pair)))

    @classmethod
    def from_pair(cls, pair: tuple[int, ...], *, base: int = 10) -> ReverseAddPairField:
        require_exact_oracle()
        base = int(base)
        pair = tuple(map(int, pair))
        if (
            not pair
            or pair != pair[::-1]
            or any(not 0 <= value <= 2 * (base - 1) for value in pair)
        ):
            raise ValueError(pair)
        return cls(base, source_span(pair, blank=0, logical_length=len(pair)))

    @property
    def domain(self) -> NormalizedDomainFrame:
        require_exact_oracle()
        return NormalizedDomainFrame.prefix(self.span.length, self.span.length)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        require_exact_oracle()
        return ("reverse-add-pair-field", self.base, self.span.tile_ids)

    def values(self) -> tuple[int, ...]:
        require_exact_oracle()
        return tuple(iter_symbols(self.span))


@dataclass(frozen=True, slots=True)
class ReverseAddCarrySlab:
    """Exact bounded-memory temporal state for reverse/add.

    The slab contains exactly ``H=4*bit_length(2b-2)`` forward carry rows.
    It is an exact bootstrap/proof certificate, not the temporal cache identity.
    Production powering applies the event-memory morphism, then separates the
    reusable linear-phase ActionID from the exact reconstructed pair occurrence.
    Absolute row widths remain dyadic geometry in each ``DyadicSpan``.
    """

    base: int
    carries: tuple[DyadicSpan, ...]
    cut_state: ReverseAddCarryCutState = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        require_exact_oracle()
        h = event_memory_horizon(self.base)
        if len(self.carries) != h:
            raise ValueError((len(self.carries), h))
        for row in self.carries:
            if row.start != 0 or row.length < 2:
                raise ValueError((row.start, row.length))
            if first_symbol(row.chunks[0].tile) != 0:
                raise ValueError("invalid carry row")
            stack = [chunk.tile for chunk in row.chunks]
            seen: set[int] = set()
            while stack:
                node = stack.pop()
                if node.node_id in seen:
                    continue
                seen.add(node.node_id)
                if node.symbol is not None:
                    if node.symbol not in (0, 1):
                        raise ValueError("invalid carry row")
                elif node.left is not None and node.right is not None:
                    stack.extend((node.left, node.right))
        object.__setattr__(
            self,
            "cut_state",
            ReverseAddCarryCutState.from_rows(self.carries, base=self.base),
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        require_exact_oracle()
        return self.cut_state.canonical_key

    def row_values(self) -> tuple[tuple[int, ...], ...]:
        require_exact_oracle()
        return tuple(tuple(iter_symbols(row)) for row in self.carries)

    def current_pair(self) -> ReverseAddPairField:
        require_exact_oracle()
        return ReverseAddPairField(
            self.base, reconstruct_slab_span(self.carries, self.base)
        )


@dataclass(frozen=True, slots=True)
class ReverseAddCausalAdvance:
    source: ReverseAddPairField
    growth: int
    target: ReverseAddPairField

    def __post_init__(self) -> None:
        require_exact_oracle()


@dataclass(frozen=True, slots=True)
class ReverseAddSpacetimeMetrics:
    primitive_field_steps: int
    primitive_slab_steps: int
    slab_jump_entries: int
    binary_lift: BinaryLiftMetrics
    affine_apply_entries: int
    affine_action_requests: int
    affine_action_hits: int
    carry_projection_entries: int
    carry_projection_hits: int
    carry_unique_actions: int
    carry_action_alias_hits: int
    carry_mirror_alias_hits: int
    carry_conjugate_alias_hits: int
    terminal_projection_entries: int
    domain_canonical_refs: int
    domain_mirror_hits: int
    domain_conjugate_hits: int
    finite_cell_alphabet: int
    carry_direction: str = "lsd-to-msd"
    forcing_classes: int = 0
    forcing_history_aliases: int = 0
    forcing_source_hits: int = 0
    forcing_carry_behavior_classes: int = 0
    forcing_carry_behavior_aliases: int = 0
    primitive_forcing_steps: int = 0
    forcing_jump_entries: int = 0
    forcing_occurrences: int = 0
    forcing_action_aliases: int = 0
    forcing_successor_conflicts: int = 0
    forcing_exact_target_conflicts: int = 0
    macro_actions: int = 0
    macro_compositions: int = 0
    macro_applications: int = 0
    nonlinear_branch_evaluations: int = 0
    exact_endpoint_entries: int = 0
    slab_endpoint_source_entries: int = 0

    def __post_init__(self) -> None:
        require_exact_oracle()


class ReverseAddCausalSpacetimeEngine:
    """Exact canonical pair-field reverse/add engine with one-way carry scans."""

    __slots__ = (
        "_advances",
        "_endpoint_limit",
        "_forcing_endpoints",
        "_forcing_hits",
        "_forcing_requests",
        "_lift",
        "_slab_endpoints",
        "_slab_sources",
        "base",
        "carry",
        "carry_quotient",
        "codec",
        "domains",
        "forcing",
        "forcing_actions",
        "forcing_congruence",
        "macro_actions",
        "max_context_nodes",
        "primitive_field_steps",
        "primitive_forcing_steps",
        "primitive_slab_steps",
        "terminal",
    )

    def __init__(
        self,
        *,
        base: int = 10,
        max_jump_entries: int = 16384,
        max_context_nodes: int | None = None,
    ) -> None:
        require_exact_oracle()
        base = int(base)
        if base < 2:
            raise ValueError(base)
        self.base = base
        self.max_context_nodes = (
            None if max_context_nodes is None else max(0, int(max_context_nodes))
        )
        self.codec = reverse_pair_codec(base)
        self.domains = CanonicalDomainArena(self.codec)
        kernel = reverse_add_carry_kernel(base)
        self.carry = DirectedTileTransducerArena(
            kernel,
            _carry_emit(base),
            output_alphabet_size=2,
        )
        self.terminal = DirectedTileTransducerArena(
            kernel,
            _digit_emit(base),
            output_alphabet_size=base,
        )
        self.forcing_actions = ReverseAddAffineActionArena(base)
        self.forcing = ReverseAddForcingMorphismArena(base)
        self.primitive_field_steps = 0
        self.primitive_slab_steps = 0
        self.primitive_forcing_steps = 0
        self.forcing_congruence = SuccessorCongruenceAudit()
        self._advances: dict[tuple[object, ...], ReverseAddCausalAdvance] = {}

        def step(field: ReverseAddPairField) -> tuple[ReverseAddPairField, int]:
            require_exact_oracle()
            advance = self.advance(field)
            return advance.target, 1

        self._lift = BinaryLiftEngine[ReverseAddPairField, int](
            step=step,
            key=lambda field: field.canonical_key,
            identity_weight=0,
            combine_weight=lambda a, b: int(a) + int(b),
            jump_cache_limit=max_jump_entries,
        )

        self._slab_endpoints: dict[tuple[int, int], ReverseAddCarrySlab] = {}
        self._slab_sources: dict[tuple[object, ...], int] = {}

        self.carry_quotient = CarryActionQuotientArena()
        self.macro_actions = ReverseAddMacroActionArena(base)
        self._forcing_endpoints: dict[tuple[int, int], ReverseAddForcingOccurrence] = {}
        self._forcing_requests = 0
        self._forcing_hits = 0
        self._endpoint_limit = max_jump_entries

    def _check_context_budget(self) -> None:
        require_exact_oracle()
        cap = self.max_context_nodes
        if cap is None:
            return
        cm = self.carry.metrics()
        live = (
            self.forcing_actions.metrics().affine_entries
            + cm.projection_entries
            + len(self._advances)
            + int(self.domains.metrics()["canonical_refs"])
            + self.carry_quotient.retained_port_entries
            + self.macro_actions.action_count
            + self.macro_actions.composition_count
            + len(self._forcing_endpoints)
            + len(self._slab_endpoints)
            + len(self._slab_sources)
        )
        if live > cap:
            raise BlockContextBudgetExceeded(
                f"HashLife spacetime canonical field exceeded {cap} retained nodes"
            )

    def _observe_domain(self, span: DyadicSpan) -> None:
        require_exact_oracle()
        for chunk in span.chunks:
            self.domains.canonical_ref(chunk.tile)

    def _forcing_occurrence_from_pair(
        self,
        field: ReverseAddPairField,
    ) -> tuple[ReverseAddForcingOccurrence, DyadicSpan]:
        """Intern one exact pair occurrence under its extensional ActionID.

        The single carry projection is the only causal scan.  ``from_carry``
        compiles that result into a source-independent affine operator; exact
        pair data is retained only by the occurrence payload.
        """
        require_exact_oracle()
        if field.base != self.base:
            raise ValueError((field.base, self.base))
        carry_out, growth = self.carry_quotient.project_span(
            field.span, 0, base=self.base
        )
        growth = int(growth)
        if growth not in (0, 1):
            raise AssertionError(growth)
        action = self.forcing_actions.from_carry(carry_out, growth)
        occurrence = self.forcing.intern_pair_span(
            field.span,
            action=action,
        )
        return occurrence, carry_out

    def _forcing_occurrence_from_slab(
        self,
        slab: ReverseAddCarrySlab,
    ) -> tuple[ReverseAddForcingOccurrence, DyadicSpan]:
        """Apply the H-row epimorphism without retaining history as identity."""
        require_exact_oracle()
        if slab.base != self.base:
            raise ValueError((slab.base, self.base))
        pair = slab.current_pair()
        carry_out, growth = self.carry_quotient.project_span(
            pair.span, 0, base=self.base
        )
        growth = int(growth)
        if growth not in (0, 1):
            raise AssertionError(growth)
        action = self.forcing_actions.from_carry(carry_out, growth)
        occurrence = self.forcing.intern(slab.carries, action=action)
        if self.forcing.pair_span(occurrence).tile_ids != pair.span.tile_ids:
            raise AssertionError("history morphism changed exact pair payload")
        return occurrence, carry_out

    def forcing_image(
        self,
        source: ReverseAddPairField | ReverseAddCarrySlab,
    ) -> ReverseAddForcingOccurrence:
        """Return the exact occurrence under its shared semantic ActionID."""
        require_exact_oracle()
        if isinstance(source, ReverseAddCarrySlab):
            return self._forcing_occurrence_from_slab(source)[0]
        if isinstance(source, ReverseAddPairField):
            return self._forcing_occurrence_from_pair(source)[0]
        raise TypeError(type(source))

    def _advance_internal(
        self,
        field: ReverseAddPairField,
    ) -> ReverseAddCausalAdvance:
        require_exact_oracle()
        if field.base != self.base:
            raise ValueError((field.base, self.base))
        key = field.canonical_key
        found = self._advances.get(key)
        if found is not None:
            return found
        self.primitive_field_steps += 1
        self._observe_domain(field.span)

        # K_i = C_(i+1).  This is the sole physical carry propagation and is
        # always evaluated left-to-right (LSD -> MSD).
        carry_field, growth = self.carry.project_span(field.span, 0)
        growth = int(growth)
        if growth not in (0, 1):
            raise AssertionError(growth)

        # The exact nonlinear control is now interned as an affine forcing
        # action independent of the source payload.  Reflection is used only
        # inside the event compiler as a coordinate view of this same forward
        # carry row; no reverse physical carry scan exists.
        action = self.forcing_actions.from_carry(carry_field, growth)
        target_span = self.forcing_actions.apply(action, field.span)
        target = ReverseAddPairField(self.base, target_span)
        self._observe_domain(target.span)
        advance = ReverseAddCausalAdvance(field, growth, target)
        self._advances[key] = advance
        self._check_context_budget()
        return advance

    def advance(self, field: ReverseAddPairField) -> ReverseAddCausalAdvance:
        require_exact_oracle()
        return self._advance_internal(field)

    def lazy_application(
        self,
        source: ReverseAddPairField,
        steps: int,
        *,
        blank: int = 0,
        ledger: ResourceLedger | None = None,
    ) -> LazyReverseApplication:
        """Enter the source-backed point path without an H-row bootstrap.

        The supplied exact field is explicit source ingestion. All future
        observations belong to the returned per-index symbolic application.
        Existing field/slab methods remain explicit exact diagnostic APIs.
        """
        require_exact_oracle()
        if source.base != self.base:
            raise ValueError((source.base, self.base))
        if ledger is None:
            ledger = ResourceLedger(max_nodes=self.max_context_nodes)
        return LazyReverseApplication(self.base, blank, steps, source.values(), ledger)

    def bootstrap_slab(
        self, field: ReverseAddPairField
    ) -> tuple[ReverseAddCarrySlab, ReverseAddPairField]:
        """Bootstrap the exact bounded-memory carry slab in a constant H steps."""
        require_exact_oracle()
        if field.base != self.base:
            raise ValueError((field.base, self.base))
        rows: list[DyadicSpan] = []
        current = field
        for _ in range(event_memory_horizon(self.base)):
            carry_span, _growth = self.carry.project_span(current.span, 0)
            # event_memory carry rows are C_0..C_d; project_span emits K_i=C_(i+1).
            zero = DyadicSpan(0, 1, (DyadicChunk(0, leaf(0)),))
            shifted = rebase(carry_span, 1)
            full = concat(zero, shifted)
            rows.append(full)
            current = self.advance(current).target
        slab = ReverseAddCarrySlab(self.base, tuple(rows))
        # The theorem must reconstruct the exact endpoint after the H transitions.
        reconstructed = slab.current_pair()
        if reconstructed.span.tile_ids != current.span.tile_ids:
            raise AssertionError("carry slab bootstrap disagrees with exact endpoint")
        return slab, current

    def advance_slab_power(
        self,
        slab: ReverseAddCarrySlab,
        steps: int,
    ) -> tuple[ReverseAddCarrySlab, int]:
        require_exact_oracle()
        steps = _validated_power_steps(slab.base, self.base, steps)
        if not steps:
            return slab, 0
        image, _ = self._forcing_occurrence_from_slab(slab)
        # Only old rows surviving this request can affect the exact certificate.
        # The generated suffix depends on the reconstructed pair occurrence.
        horizon = event_memory_horizon(self.base)
        surviving_rows = slab.carries[min(steps, horizon) :]
        endpoint_source_key = (
            image.occurrence_id,
            tuple(row.tile_ids for row in surviving_rows),
        )
        slab_id = self._slab_sources.setdefault(
            endpoint_source_key, len(self._slab_sources)
        )
        key = slab_id, steps
        found = self._slab_endpoints.get(key)
        if found is not None:
            self._slab_endpoints.pop(key)
            self._slab_endpoints[key] = found
            return found, steps
        certificate_steps = min(steps, horizon)
        if steps > horizon:
            image, _ = self.advance_forcing_power(image, steps - horizon)
        source = self.forcing.pair_span(image)
        prefix: ActionProgramID | None = None
        rows = list(slab.carries[certificate_steps:])
        for _ in range(certificate_steps):
            self.primitive_slab_steps += 1
            if prefix is None:
                carry, growth = self.carry_quotient.project_span(
                    source, 0, base=self.base
                )
            else:
                carry, growth = self.macro_actions.carry_projection(
                    prefix,
                    source,
                    self.carry_quotient,
                    base=self.base,
                )
            rows.append(prepend_symbol(carry, 0))
            action = self.forcing_actions.from_carry(carry, growth)
            action_id = self.macro_actions.primitive(action)
            prefix = (
                action_id
                if prefix is None
                else self.macro_actions.compose(prefix, action_id)
            )
            self._check_context_budget()
        target = ReverseAddCarrySlab(self.base, tuple(rows))
        if self._endpoint_limit > 0:
            if len(self._slab_endpoints) >= self._endpoint_limit:
                self._slab_endpoints.pop(next(iter(self._slab_endpoints)))
            self._slab_endpoints[key] = target
        self._check_context_budget()
        return target, steps

    def advance_forcing_power(
        self,
        state: ReverseAddForcingOccurrence,
        steps: int,
    ) -> tuple[ReverseAddForcingOccurrence, int]:
        require_exact_oracle()
        self.forcing.validate_occurrence(state)
        steps = _validated_power_steps(state.base, self.base, steps)
        if not steps:
            return state, 0
        self._forcing_requests += 1
        key = state.occurrence_id, steps
        found = self._forcing_endpoints.get(key)
        if found is not None:
            self._forcing_hits += 1
            self._forcing_endpoints.pop(key)
            self._forcing_endpoints[key] = found
            return found, steps
        source = self.forcing.pair_span(state)
        prefix: ActionProgramID | None = None
        # Discover nonlinear controls directly from action effect summaries.  These
        # are not occurrence objects or entries in a temporal jump cache.
        # Carry-reset equivalence cannot predict the next reset itinerary.
        blocks: list[tuple[int, ActionProgramID]] = []
        for index in range(steps):
            self.primitive_forcing_steps += 1
            if not index:
                action = state.action
            else:
                if prefix is None:
                    raise AssertionError("missing action prefix")
                carry, growth = self.macro_actions.carry_projection(
                    prefix,
                    source,
                    self.carry_quotient,
                    base=self.base,
                )
                action = self.forcing_actions.from_carry(carry, growth)
            action_id = self.macro_actions.primitive(action)
            prefix = (
                action_id
                if prefix is None
                else self.macro_actions.compose(prefix, action_id)
            )
            size = 1
            while blocks and blocks[-1][0] == size:
                _, before = blocks.pop()
                action_id = self.macro_actions.compose(before, action_id)
                size *= 2
            blocks.append((size, action_id))
            self._check_context_budget()
        combined = blocks[0][1]
        for _, action_id in blocks[1:]:
            combined = self.macro_actions.compose(combined, action_id)
        endpoint = self.macro_actions.apply(combined, source)
        if prefix != combined:
            raise AssertionError("action composition is not associative")
        target, _ = self._forcing_occurrence_from_pair(
            ReverseAddPairField(self.base, endpoint)
        )
        if steps == 1:
            self.forcing_congruence.observe(
                SuccessorObservation(
                    state.forcing.canonical_key,
                    state.occurrence_key,
                    target.forcing.canonical_key,
                    target.occurrence_key,
                )
            )
        if self._endpoint_limit > 0:
            if len(self._forcing_endpoints) >= self._endpoint_limit:
                self._forcing_endpoints.pop(next(iter(self._forcing_endpoints)))
            self._forcing_endpoints[key] = target
        self._check_context_budget()
        return target, steps

    def advance_power(
        self,
        field: ReverseAddPairField,
        steps: int,
    ) -> tuple[ReverseAddPairField, int]:
        require_exact_oracle()
        if field.base != self.base:
            raise ValueError((field.base, self.base))
        target, weight = self._lift.advance(field, int(steps))
        if int(weight) != int(steps):
            raise AssertionError((steps, weight))
        return target, int(weight)

    def terminal_digits(self, field: ReverseAddPairField) -> DyadicSpan:
        require_exact_oracle()
        if field.base != self.base:
            raise ValueError((field.base, self.base))
        digits, carry = self.terminal.project_span(field.span, 0)
        if carry:
            digits = append_symbol(digits, int(carry))
        return digits

    def terminal_width(self, field: ReverseAddPairField) -> int:
        """Exact normalized digit width without projecting the digit field."""
        require_exact_oracle()
        if field.base != self.base:
            raise ValueError((field.base, self.base))
        return int(field.span.length) + int(self.terminal.advance_span(field.span, 0))

    def terminal_digit(self, field: ReverseAddPairField, position: int) -> int:
        """Exact one-digit normalization through a dyadic prefix action."""
        require_exact_oracle()
        if field.base != self.base:
            raise ValueError((field.base, self.base))
        position = int(position)
        if position < 0:
            raise IndexError(position)
        if position < field.span.length:
            value, _before, _after = self.terminal.project_symbol_at(
                field.span, position, 0
            )
            return int(value)
        if position == field.span.length:
            carry = int(self.terminal.advance_span(field.span, 0))
            if carry:
                return carry
        raise IndexError(position)

    def advance_pair_steps(
        self,
        field: ReverseAddPairField,
        steps: int,
    ) -> ReverseAddPairField:
        """Materialize an exact reference endpoint through the carry-history oracle.

        Both the small/base-2 binary lift and the H-row forcing path retain
        exact intermediate payloads. Neither is a production temporal carrier.
        """
        require_exact_oracle()
        steps = _validated_power_steps(field.base, self.base, steps)
        if steps == 0:
            return field
        if self.base < 3:
            return self.advance_power(field, steps)[0]
        horizon = event_memory_horizon(self.base)
        if steps <= horizon:
            return self.advance_power(field, steps)[0]
        slab, endpoint = self.bootstrap_slab(field)
        image, _carry = self._forcing_occurrence_from_slab(slab)
        if self.forcing.pair_span(image).tile_ids != endpoint.span.tile_ids:
            raise AssertionError("forcing morphism disagrees with bootstrap endpoint")
        image, _ = self.advance_forcing_power(image, steps - horizon)
        return ReverseAddPairField(self.base, self.forcing.pair_span(image))

    def term_field(self, seed: int, generation: int) -> ReverseAddPairField:
        """Return the pair field immediately before terminal normalization."""
        require_exact_oracle()
        generation = int(generation)
        if generation <= 0:
            raise ValueError("generation zero has no reverse/add pair terminal")
        initial = ReverseAddPairField.from_value(int(seed), base=self.base)
        return self.advance_pair_steps(initial, generation - 1)

    def term_digits(self, seed: int, generation: int) -> DyadicSpan:
        require_exact_oracle()
        generation = int(generation)
        if generation <= 0:
            value = int(seed)
            digits = tuple(map(int, digits_lsd(value, self.base)))
            return source_span(digits, blank=0, logical_length=len(digits))
        return self.terminal_digits(self.term_field(seed, generation))

    def term_value(self, seed: int, generation: int) -> int:
        require_exact_oracle()
        return value_from_lsd_digits(
            iter_symbols(self.term_digits(seed, generation)), self.base
        )

    def metrics(self) -> ReverseAddSpacetimeMetrics:
        require_exact_oracle()
        cm = self.carry.metrics()
        tm = self.terminal.metrics()
        dm = self.domains.metrics()
        fm = self.forcing.metrics()
        return ReverseAddSpacetimeMetrics(
            self.primitive_field_steps,
            self.primitive_slab_steps,
            len(self._slab_endpoints),
            BinaryLiftMetrics(
                self.primitive_forcing_steps,
                self._forcing_requests,
                self._forcing_hits,
                len(self._forcing_endpoints),
            ),
            self.forcing_actions.metrics().affine_entries,
            self.forcing_actions.metrics().requests,
            self.forcing_actions.metrics().hits,
            cm.projection_entries,
            cm.projection_hits,
            cm.unique_actions,
            cm.action_alias_hits,
            cm.mirror_alias_hits,
            cm.conjugate_alias_hits,
            tm.projection_entries,
            int(dm["canonical_refs"]),
            int(dm["mirror_hits"]),
            int(dm["conjugate_hits"]),
            self.codec.alphabet_size,
            str(dm["carry_direction"]),
            fm.forcing_classes,
            fm.history_aliases,
            fm.source_hits,
            self.carry_quotient.port_action_count,
            self.carry_quotient.port_aliases,
            self.primitive_forcing_steps,
            BinaryLiftMetrics(
                self.primitive_forcing_steps,
                self._forcing_requests,
                self._forcing_hits,
                len(self._forcing_endpoints),
            ).jump_entries,
            fm.forcing_occurrences,
            fm.action_aliases,
            self.forcing_congruence.metrics().successor_conflicts,
            self.forcing_congruence.metrics().exact_target_conflicts,
            self.macro_actions.action_count,
            self.macro_actions.composition_count,
            self.macro_actions.applications,
            self.primitive_forcing_steps,
            len(self._forcing_endpoints),
            len(self._slab_sources),
        )


__all__ = [
    "ReverseAddCarrySlab",
    "ReverseAddCausalAdvance",
    "ReverseAddCausalSpacetimeEngine",
    "ReverseAddPairField",
    "ReverseAddSpacetimeMetrics",
]
