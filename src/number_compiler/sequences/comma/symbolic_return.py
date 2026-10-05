"""Optional symbolic complete-return functions for comma continuations.

The builder is a consumer/audit boundary around the public
``SemanticFunctionArena``.  It turns each already compiled continuation into a
function of CRT clock bits.  A local row uses only the factors needed by its
period (parity, mod 3, mod 11, mod 4, or mod 7); child functions are composed
bottom-up with ``SemanticFunctionArena.ite``.  No 924-phase output vector is
created by this module.

Clock shifts are occurrence-independent transformations of the returned
function.  ``source_address`` keeps a source occurrence's rebase shift next to
the function handle instead of treating that shift as a physical successor
clock.  This module is not a production B1 cutover or an Isabelle refinement.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping, MutableMapping
from dataclasses import dataclass
from math import lcm
from types import MappingProxyType
from typing import TypeAlias, TypeVar

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
    SemanticFunctionID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.comma.boundary_chart import PERIOD
from number_compiler.sequences.comma.cyclotomic_clock import shifted_component_bit
from number_compiler.sequences.comma.return_scope_observer import (
    canonical_mdd_partition_rebase,
)
from number_compiler.sequences.comma.return_scopes import (
    B1ReturnPartitionRecord,
    ReturnColumnKey,
    continuation_return_partition,
    return_code,
    return_partition_node_cost,
    return_template_node_cost,
)
from number_compiler.sequences.comma.semantic_continuation import (
    ContinuationID,
    SemanticAction,
    SemanticContinuation,
    SourceState,
    WeightedAction,
)

RETURN_CARDINALITY = 55
LIVE_BASE = 9
_RETURN_SORT = AtomSort("comma-complete-return", RETURN_CARDINALITY)
_OutputTemplateKey: TypeAlias = tuple[ReturnColumnKey, ...]
_CLOCK_MODULI = {"r4": 4, "r3": 3, "r7": 7, "r11": 11}
_PERIOD_COMPONENTS: dict[int, tuple[tuple[str, int], ...]] = {
    1: (),
    2: (("r4", 2),),
    3: (("r3", 3),),
    6: (("r4", 2), ("r3", 3)),
    22: (("r4", 2), ("r11", 11)),
    28: (("r4", 4), ("r7", 7)),
}
_RotationValue = TypeVar("_RotationValue")
_VALID_MASK_KEY: TypeAlias = tuple[tuple[FinitePort, ...], AtomSort]


def least_cyclic_rotation(
    length: int,
    value_at: Callable[[int], _RotationValue],
    *,
    compare: Callable[[_RotationValue, _RotationValue], int],
    on_comparison: Callable[[], None] | None = None,
) -> int:
    """Return a lexicographically least cyclic start by lazy indexed reads.

    This is Booth's linear-time rotation search.  ``value_at`` is called only
    for phases reached by the comparison, so callers can expose an on-demand
    semantic function instead of materializing its full return row.
    """
    if type(length) is not int or length <= 0:
        raise ValueError("cyclic rotation requires a positive length")
    left, right, matched = 0, 1, 0
    while left < length and right < length and matched < length:
        left_value = value_at((left + matched) % length)
        right_value = value_at((right + matched) % length)
        if on_comparison is not None:
            on_comparison()
        relation = compare(left_value, right_value)
        if relation == 0:
            matched += 1
            continue
        if relation > 0:
            left = left + matched + 1
            if left <= right:
                left = right + 1
        else:
            right = right + matched + 1
            if right <= left:
                right = left + 1
        matched = 0
    return min(left, right)


def _clock_role(component: str, bit: int) -> str:
    return f"comma-clock-{component}-b{bit}"


def _clock_component(role: str) -> tuple[str, int]:
    prefix = "comma-clock-"
    if not role.startswith(prefix):
        raise ValueError("unknown comma symbolic clock role")
    component, separator, bit_text = role[len(prefix) :].rpartition("-b")
    if not separator or component not in _CLOCK_MODULI:
        raise ValueError("malformed comma symbolic clock role")
    bit = int(bit_text)
    width = (_CLOCK_MODULI[component] - 1).bit_length()
    if not 0 <= bit < width:
        raise ValueError("comma symbolic clock bit is outside its component")
    return component, bit


def _clock_bit(
    arena: SemanticFunctionArena,
    component: str,
    bit: int,
    cache: dict[str, SemanticFunctionID],
) -> SemanticFunctionID:
    role = _clock_role(component, bit)
    found = cache.get(role)
    if found is not None:
        return found
    variable = PortVariable(0, 0, role, 0)
    port = FinitePort(variable, 2)
    found = arena.variable((port,), port, output=BOOL)
    cache[role] = found
    return found


def _equal_component(
    arena: SemanticFunctionArena,
    component: str,
    modulus: int,
    value: int,
    cache: dict[str, SemanticFunctionID],
) -> SemanticFunctionID:
    false = arena.atom(FunctionSignature((), BOOL), 0)
    true = arena.atom(FunctionSignature((), BOOL), 1)
    result = true
    for bit in range((modulus - 1).bit_length()):
        signal = _clock_bit(arena, component, bit, cache)
        literal = signal if (value >> bit) & 1 else arena.ite(signal, false, true)
        result = arena.ite(literal, result, false)
    return result


def _valid_clock_mask(
    arena: SemanticFunctionArena,
    inputs: tuple[FinitePort, ...],
    cache: dict[str, SemanticFunctionID],
) -> SemanticFunctionID:
    false = arena.atom(FunctionSignature((), BOOL), 0)
    true = arena.atom(FunctionSignature((), BOOL), 1)
    components = {_clock_component(port.variable.role)[0] for port in inputs}
    result = true
    for component in sorted(components):
        modulus = _CLOCK_MODULI[component]
        if modulus & (modulus - 1) == 0:
            continue
        valid = false
        for value in range(modulus):
            valid = arena.ite(
                _equal_component(arena, component, modulus, value, cache),
                true,
                valid,
            )
        result = arena.ite(valid, result, false)
    return result


def _full_valid_clock_mask(
    arena: SemanticFunctionArena,
    inputs: tuple[FinitePort, ...],
    cache: dict[str, SemanticFunctionID],
) -> SemanticFunctionID:
    """Lift CRT validity to the full declared input signature."""
    base = _valid_clock_mask(arena, inputs, cache)
    signature = FunctionSignature(inputs, BOOL)
    true = arena.atom(signature, 1)
    false = arena.atom(signature, 0)
    return arena.ite(base, true, false)


def _normalize_clock_function(
    arena: SemanticFunctionArena,
    function: SemanticFunctionID,
    cache: dict[str, SemanticFunctionID],
    mask_cache: MutableMapping[
        _VALID_MASK_KEY, tuple[SemanticFunctionID, SemanticFunctionID]
    ],
) -> SemanticFunctionID:
    signature = arena.signature(function)
    if type(signature.output) is not AtomSort:
        raise ValueError("comma clock normalization requires an atom output")
    key = signature.inputs, signature.output
    mask = mask_cache.get(key)
    if mask is None:
        arena.ledger.bump("comma_symbolic_valid_mask_cache_misses")
        valid = _full_valid_clock_mask(arena, signature.inputs, cache)
        invalid = arena.invalid(signature)
        mask = valid, invalid
        mask_cache[key] = mask
    else:
        arena.ledger.bump("comma_symbolic_valid_mask_cache_hits")
    valid, invalid = mask
    return arena.ite(valid, function, invalid)


def decode_return(code: int) -> tuple[str, int]:
    """Decode a complete-return control atom for audit consumers."""
    if type(code) is not int or not 0 <= code < RETURN_CARDINALITY:
        raise ValueError("invalid comma complete-return code")
    return ("stop", code) if code < LIVE_BASE else ("live", code - LIVE_BASE)


def _compare_return_labels(left: tuple[str, int], right: tuple[str, int]) -> int:
    return (left > right) - (left < right)


@dataclass(frozen=True, slots=True)
class CanonicalShiftResult:
    """A translated function and inverse shift within one arena owner.

    The numeric function handle is owner-local and is not a portable semantic
    identity.  Only equality in the same ``SemanticFunctionArena`` supports
    the representative comparison.
    """

    function: SemanticFunctionID
    return_shift: int
    scanned_shifts: int
    complete: bool
    phase_reads: int = 0
    comparisons: int = 0


@dataclass(frozen=True, slots=True)
class CanonicalSourceBinding:
    """A source occurrence with separate return and physical rebase shifts."""

    function: SemanticFunctionID
    return_shift: int
    occurrence_shift: int
    complete: bool

    def __post_init__(self) -> None:
        if type(self.function) is not SemanticFunctionID:
            raise TypeError("comma return binding requires a typed function handle")
        if type(self.return_shift) is not int or not 0 <= self.return_shift < PERIOD:
            raise ValueError("comma return shift must be in 0..923")
        if type(self.occurrence_shift) is not int or self.occurrence_shift < 0:
            raise ValueError("comma occurrence shift must be a nonnegative integer")
        if type(self.complete) is not bool:
            raise TypeError("comma return completeness must be a boolean")

    @property
    def input_shift(self) -> int:
        """Shift used for this return only; successor time remains physical."""
        return (self.return_shift + self.occurrence_shift) % PERIOD


@dataclass(frozen=True, slots=True)
class CanonicalOutputTemplateBinding:
    """A phase-rebased output template with an occurrence-specific label map.

    ``function`` is an owner-local template whose atoms are column numbers.
    ``output_binding`` maps those colors back to exact source return atoms.
    The selected common template shift and the source/chart occurrence shift
    stay separate so callers can compose clock transport without putting it in
    the template identity.
    """

    function: SemanticFunctionID
    source_function: SemanticFunctionID
    return_shift: int
    occurrence_shift: int
    output_binding: tuple[int, ...]
    complete: bool

    def __post_init__(self) -> None:
        if (
            type(self.function) is not SemanticFunctionID
            or type(self.source_function) is not SemanticFunctionID
        ):
            raise TypeError("comma output template requires typed function handles")
        if type(self.return_shift) is not int or not 0 <= self.return_shift < PERIOD:
            raise ValueError("comma return shift must be in 0..923")
        if type(self.occurrence_shift) is not int or self.occurrence_shift < 0:
            raise ValueError("comma occurrence shift must be nonnegative")
        if (
            type(self.output_binding) is not tuple
            or not self.output_binding
            or any(
                type(label) is not int or not 0 <= label < RETURN_CARDINALITY
                for label in self.output_binding
            )
            or len(set(self.output_binding)) != len(self.output_binding)
        ):
            raise ValueError("comma output binding must name distinct return atoms")
        if type(self.complete) is not bool:
            raise TypeError("comma output-template completeness must be Boolean")

    @property
    def input_shift(self) -> int:
        """Combined lookup shift; physical successor time remains untouched."""
        return (self.return_shift + self.occurrence_shift) % PERIOD


@dataclass(frozen=True, slots=True)
class _OutputTemplateCore:
    function: SemanticFunctionID
    return_shift: int
    output_binding: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class SymbolicReturnView:
    """Scoped symbolic controls plus the original weighted occurrence view."""

    source_view: SemanticContinuation
    arena: SemanticFunctionArena
    functions: Mapping[ContinuationID, SemanticFunctionID]
    shift_cache: OwnedMemo[tuple[SemanticFunctionID, int], SemanticFunctionID]
    clock_shift_cache: OwnedMemo[tuple[PortVariable, int], SemanticFunctionID]
    valid_mask_cache: OwnedMemo[
        _VALID_MASK_KEY, tuple[SemanticFunctionID, SemanticFunctionID]
    ]
    output_template_cache: OwnedMemo[SemanticFunctionID, _OutputTemplateCore]
    output_template_intern: OwnedMemo[_OutputTemplateKey, SemanticFunctionID]
    return_partition_cache: OwnedMemo[ContinuationID, B1ReturnPartitionRecord]
    continuation_by_function: Mapping[SemanticFunctionID, ContinuationID]

    def function_for(self, identifier: ContinuationID) -> SemanticFunctionID:
        identifier.validate(
            self.source_view.owner,
            "comma-continuation",
            size=len(self.source_view.actions_by_id),
        )
        try:
            return self.functions[identifier]
        except KeyError as exc:
            raise KeyError("source continuation has no symbolic return") from exc

    def source_address(
        self, source: SourceState, *, delta: int = 0
    ) -> tuple[SemanticFunctionID, int]:
        """Return a symbolic function and separate occurrence clock rebase."""
        identifier, shift = self.source_view.source_address(source, delta=delta)
        return self.function_for(identifier), shift

    def canonical_source_address(
        self,
        source: SourceState,
        *,
        delta: int = 0,
        shifts: tuple[int, ...] | None = None,
    ) -> CanonicalSourceBinding:
        """Bind a source occurrence while retaining both shift meanings."""
        identifier, occurrence_shift = self.source_view.source_address(
            source, delta=delta
        )
        canonical = self.canonical_shift(identifier, shifts=shifts)
        return CanonicalSourceBinding(
            canonical.function,
            canonical.return_shift,
            occurrence_shift,
            canonical.complete,
        )

    def canonical_output_template(
        self,
        function: SemanticFunctionID,
        *,
        occurrence_shift: int = 0,
    ) -> CanonicalOutputTemplateBinding:
        """Build or retrieve a common-shift quotient of exact output columns.

        Unlike ``canonical_shift``, this forgets the labels on the Boolean
        equality columns while retaining their exact per-occurrence binding.
        The finite column transform and template construction operate on the
        existing semantic-function arena; no clock-row table is materialized.
        """
        self.arena.resolve(function)
        if type(occurrence_shift) is not int or occurrence_shift < 0:
            raise ValueError("comma occurrence shift must be nonnegative")
        core = self.output_template_cache.get(function)
        if core is None:
            self.arena.ledger.bump("comma_output_template_cache_misses")
            identifier = self.continuation_by_function.get(function)
            if identifier is None:
                raise ValueError(
                    "comma output template requires a source-owned continuation"
                )
            core = self._construct_output_template(function, identifier)
            self.output_template_cache[function] = core
        else:
            self.arena.ledger.bump("comma_output_template_cache_hits")
        return CanonicalOutputTemplateBinding(
            core.function,
            function,
            core.return_shift,
            occurrence_shift,
            core.output_binding,
            True,
        )

    def canonical_source_template(
        self, source: SourceState, *, delta: int = 0
    ) -> CanonicalOutputTemplateBinding:
        """Bind a source/chart occurrence to its canonical output template."""
        identifier, occurrence_shift = self.source_view.source_address(
            source, delta=delta
        )
        return self.canonical_output_template(
            self.function_for(identifier), occurrence_shift=occurrence_shift
        )

    def evaluate_template_binding(
        self, binding: CanonicalOutputTemplateBinding, phase: int
    ) -> tuple[str, int]:
        """Reconstruct one exact labeled return from a canonical template."""
        if type(binding) is not CanonicalOutputTemplateBinding:
            raise TypeError("comma template binding requires its exact type")
        if not binding.complete:
            raise ValueError("incomplete comma output template")
        self.arena.resolve(binding.function)
        self.arena.resolve(binding.source_function)
        core = self.output_template_cache.get(binding.source_function)
        if core is None or (
            core.function != binding.function
            or core.return_shift != binding.return_shift
            or core.output_binding != binding.output_binding
        ):
            raise ValueError("comma output template binding is stale or forged")
        if type(phase) is not int or not 0 <= phase < PERIOD:
            raise ValueError("comma phase must be in 0..923")
        template_sort = self.arena.signature(binding.function).output
        if type(template_sort) is not AtomSort or template_sort.cardinality != len(
            binding.output_binding
        ):
            raise ValueError("comma output template colors disagree with their binding")
        terminal = self.arena.evaluate(
            binding.function,
            self._clock_values(
                binding.function, (phase + binding.input_shift) % PERIOD
            ),
        )
        if (
            terminal.kind != "atom"
            or terminal.value is None
            or not 0 <= terminal.value < len(binding.output_binding)
        ):
            raise ValueError(
                "canonical comma output template returned an invalid color"
            )
        return decode_return(binding.output_binding[terminal.value])

    def _construct_output_template(
        self, function: SemanticFunctionID, identifier: ContinuationID
    ) -> _OutputTemplateCore:
        signature = self.arena.signature(function)
        if type(signature.output) is not AtomSort:
            raise ValueError("comma output template needs a finite atom channel")
        if signature.output.cardinality > RETURN_CARDINALITY:
            raise ValueError(
                "comma return atom sort exceeds the admitted output alphabet"
            )
        partition = continuation_return_partition(
            self.source_view,
            identifier,
            self.return_partition_cache,
            charge=self.arena.ledger.bump,
        )
        (
            _,
            best_forward_shift,
            _,
            _,
            geometry_key,
            template_columns,
        ) = canonical_mdd_partition_rebase(partition, charge=self.arena.ledger.bump)
        canonical_column_keys = tuple(item[0] for item in template_columns)
        labels = tuple(item[1] for item in template_columns)
        canonical_scopes = tuple(item[2] for item in template_columns)
        if not canonical_scopes:
            raise ValueError("comma output template has no admitted return labels")

        interned = self.output_template_intern.get(canonical_column_keys)
        if interned is None:
            self.arena.ledger.bump("comma_output_template_intern_misses")
            boolean_columns = tuple(
                self._scope_column(scopes) for scopes in canonical_scopes
            )
            self.arena.ledger.bump(
                "comma_output_template_relabel_columns", len(boolean_columns)
            )
            template_signature = FunctionSignature(
                self._full_clock_inputs(),
                AtomSort(
                    f"comma-output-template-{len(boolean_columns)}",
                    len(boolean_columns),
                ),
            )
            result = self.arena.atom(template_signature, 0)
            colors = tuple(
                self.arena.atom(template_signature, color)
                for color in range(1, len(boolean_columns))
            )
            for column, color in zip(boolean_columns[1:], colors, strict=True):
                result = self.arena.ite(column, color, result)
            valid = _full_valid_clock_mask(self.arena, self._full_clock_inputs(), {})
            invalid = self.arena.invalid(template_signature)
            interned = self.arena.ite(valid, result, invalid)
            self.arena.require_total(interned, valid)
            publish_interner_entry = True
        else:
            self.arena.ledger.bump("comma_output_template_intern_hits")
            publish_interner_entry = False
        template_sort = self.arena.signature(interned).output
        if type(template_sort) is not AtomSort or template_sort.cardinality != len(
            labels
        ):
            raise ValueError("comma output template colors disagree with the partition")
        reconstructed = self.arena.map_atoms(interned, signature.output, labels)
        valid_mask = _full_valid_clock_mask(self.arena, self._full_clock_inputs(), {})
        expected_signature = FunctionSignature(
            self._full_clock_inputs(), signature.output
        )
        expected = self.arena.ite(
            valid_mask,
            self.shift_function(function, best_forward_shift),
            self.arena.invalid(expected_signature),
        )
        if self.arena.signature(reconstructed) != expected_signature:
            raise ValueError("comma output template did not preserve full CRT scope")
        if reconstructed != expected:
            raise ValueError("comma output template failed exact return reconstruction")
        if canonical_column_keys != geometry_key:
            raise AssertionError("canonical comma partition key changed after rebase")
        if publish_interner_entry:
            self.output_template_intern[canonical_column_keys] = interned
        return _OutputTemplateCore(
            interned,
            (-best_forward_shift) % PERIOD,
            labels,
        )

    @staticmethod
    def _full_clock_inputs() -> tuple[FinitePort, ...]:
        roles = tuple(
            PortVariable(0, 0, _clock_role(component, bit), 0)
            for component, modulus in _CLOCK_MODULI.items()
            for bit in range((modulus - 1).bit_length())
        )
        return tuple(FinitePort(variable, 2) for variable in sorted(roles))

    def _scope_column(self, scopes: tuple[tuple[int, int], ...]) -> SemanticFunctionID:
        inputs = self._full_clock_inputs()
        signature = FunctionSignature(inputs, BOOL)
        false = self.arena.atom(signature, 0)
        true = self.arena.atom(signature, 1)
        bits: dict[str, SemanticFunctionID] = {}
        result = false
        for period, residue in scopes:
            self.arena.ledger.bump("comma_output_template_scope_predicates", 1)
            condition = true
            factors = (
                ("r4", 4 if period % 4 == 0 else 2 if period % 2 == 0 else 1),
                ("r3", 3 if period % 3 == 0 else 1),
                ("r7", 7 if period % 7 == 0 else 1),
                ("r11", 11 if period % 11 == 0 else 1),
            )
            for component, factor in factors:
                if factor == 1:
                    continue
                if component == "r4" and factor == 2:
                    component_test = _equal_component(
                        self.arena, component, factor, residue % factor, bits
                    )
                else:
                    component_test = _equal_component(
                        self.arena,
                        component,
                        _CLOCK_MODULI[component],
                        residue % factor,
                        bits,
                    )
                condition = self.arena.ite(component_test, condition, false)
            result = self.arena.ite(condition, true, result)
        return result

    def _clock_values(
        self, function: SemanticFunctionID, phase: int
    ) -> dict[PortVariable, int]:
        if type(phase) is not int or not 0 <= phase < PERIOD:
            raise ValueError("comma phase must be in 0..923")
        values: dict[PortVariable, int] = {}
        for port in self.arena.signature(function).inputs:
            component, bit = _clock_component(port.variable.role)
            values[port.variable] = (phase % _CLOCK_MODULI[component] >> bit) & 1
        return values

    def translation_period(self, function: SemanticFunctionID) -> int:
        """Return the admitted physical shift period of one function.

        The arena signature records exactly which CRT bits remain observable.
        A low r4 bit has period two, the high r4 bit period four, and the
        non-dyadic components retain their own moduli.  The result is a
        divisor of the physical 924-clock period, so reducing a shift by it
        reuses the same owner-local semantic handle without changing the
        occurrence rebase stored by a source binding.
        """
        self.arena.resolve(function)
        period = 1
        for port in self.arena.signature(function).inputs:
            component, bit = _clock_component(port.variable.role)
            component_period = (
                2
                if component == "r4" and bit == 0
                else 4
                if component == "r4"
                else _CLOCK_MODULI[component]
            )
            period = lcm(period, component_period)
        return period

    def evaluate(self, identifier: ContinuationID, phase: int) -> tuple[str, int]:
        """Evaluate one symbolic return at a physical external clock phase."""
        return self.evaluate_function(self.function_for(identifier), phase)

    def evaluate_function(
        self, function: SemanticFunctionID, phase: int
    ) -> tuple[str, int]:
        """Evaluate a translated function without introducing occurrence data."""
        terminal = self.arena.evaluate(function, self._clock_values(function, phase))
        if terminal.kind != "atom":
            raise ValueError("symbolic comma return is not a valid atom")
        return decode_return(terminal.value)

    def evaluate_binding(
        self, binding: CanonicalSourceBinding, phase: int
    ) -> tuple[str, int]:
        """Evaluate a bound occurrence without advancing its physical clock."""
        if type(binding) is not CanonicalSourceBinding:
            raise TypeError("comma canonical binding requires its exact type")
        if type(phase) is not int or not 0 <= phase < PERIOD:
            raise ValueError("comma phase must be in 0..923")
        return self.evaluate_function(
            binding.function,
            (phase + binding.occurrence_shift + binding.return_shift) % PERIOD,
        )

    def weighted_sources(
        self, identifier: ContinuationID
    ) -> tuple[tuple[SourceState, tuple[WeightedAction, ...]], ...]:
        """Expose exact source occurrence rows independently of symbolic IDs."""
        self.function_for(identifier)
        return tuple(
            (source, row)
            for source, source_id in self.source_view.source_ids.items()
            if source_id == identifier
            for row in (self.source_view.transitions[source],)
        )

    def shifted(self, identifier: ContinuationID, shift: int) -> SemanticFunctionID:
        """Translate one complete-return function by a common CRT clock shift."""
        return self.shift_function(self.function_for(identifier), shift)

    def shift_function(
        self, function: SemanticFunctionID, shift: int
    ) -> SemanticFunctionID:
        """Translate a scoped function while preserving its invalid-domain mask."""
        self.arena.resolve(function)
        if type(shift) is not int:
            raise TypeError("comma clock shift must be an exact integer")
        normalized_shift = shift % self.translation_period(function)
        shift_key = function, normalized_shift
        cached = self.shift_cache.get(shift_key)
        if cached is not None:
            self.arena.ledger.bump("comma_symbolic_return_shift_cache_hits")
            return cached
        self.arena.ledger.bump("comma_symbolic_return_shift_cache_misses")
        replacements: dict[PortVariable, SemanticFunctionID] = {}
        for port in self.arena.signature(function).inputs:
            component, _ = _clock_component(port.variable.role)
            component_shift = normalized_shift % _CLOCK_MODULI[component]
            primitive_key = port.variable, component_shift
            primitive = self.clock_shift_cache.get(primitive_key)
            if primitive is None:
                self.arena.ledger.bump("comma_symbolic_clock_shift_cache_misses")
                primitive = shifted_component_bit(
                    self.arena,
                    component,
                    _clock_component(port.variable.role)[1],
                    component_shift,
                    _CLOCK_MODULI[component],
                )
                self.clock_shift_cache[primitive_key] = primitive
            else:
                self.arena.ledger.bump("comma_symbolic_clock_shift_cache_hits")
            replacements[port.variable] = primitive
        shifted_function = self.arena.substitute(function, replacements)
        signature = self.arena.signature(shifted_function)
        if type(signature.output) is not AtomSort:
            raise ValueError("comma clock shift requires an atom output")
        mask_key = signature.inputs, signature.output
        mask = self.valid_mask_cache.get(mask_key)
        if mask is None:
            self.arena.ledger.bump("comma_symbolic_valid_mask_cache_misses")
            valid = _full_valid_clock_mask(self.arena, signature.inputs, {})
            invalid = self.arena.invalid(signature)
            mask = valid, invalid
            self.valid_mask_cache[mask_key] = mask
        else:
            self.arena.ledger.bump("comma_symbolic_valid_mask_cache_hits")
        shifted_function = self.arena.ite(mask[0], shifted_function, mask[1])
        self.shift_cache[shift_key] = shifted_function
        return shifted_function

    def canonical_shift(
        self,
        identifier: ContinuationID,
        *,
        shifts: tuple[int, ...] | None = None,
        candidate_observer: Callable[[int], None] | None = None,
    ) -> CanonicalShiftResult:
        """Choose a canonical translated handle without relabeling outputs.

        The default scans the function's admitted shift period, a divisor of
        the 924 physical clock, and uses one lazy Booth rotation search rather
        than constructing every translated function.  A supplied subset is
        marked incomplete unless it covers that whole period and uses the
        explicit candidate path.  ``shifted(k)`` is ``F(r+k)``, so the
        returned ``return_shift`` is ``-k mod 924``.  It is metadata for the
        complete-return function, never an occurrence delta or a physical
        successor-clock update.  ``candidate_observer`` is an optional
        developer-audit hook invoked immediately before each candidate is
        constructed; it has no effect on the selected handle.
        """
        function = self.function_for(identifier)
        support_period = self.translation_period(function)
        if shifts is None:
            phase_reads = 0
            comparisons = 0

            def read_phase(phase: int) -> tuple[str, int]:
                nonlocal phase_reads
                phase_reads += 1
                return self.evaluate(identifier, phase)

            def observe_comparison() -> None:
                nonlocal comparisons
                comparisons += 1

            forward_shift = least_cyclic_rotation(
                support_period,
                read_phase,
                compare=_compare_return_labels,
                on_comparison=observe_comparison,
            )
            if candidate_observer is not None:
                candidate_observer(forward_shift)
            candidate = self.shifted(identifier, forward_shift)
            return CanonicalShiftResult(
                candidate,
                (-forward_shift) % PERIOD,
                1,
                True,
                phase_reads,
                comparisons,
            )
        else:
            if not shifts:
                raise ValueError("canonical symbolic shift requires one candidate")
            if any(type(shift) is not int for shift in shifts):
                raise TypeError("canonical symbolic shifts require exact integers")
            candidates = sorted({shift % support_period for shift in shifts})
            candidate_count = len(candidates)
            complete = candidate_count == support_period
        best_function: SemanticFunctionID | None = None
        best_forward_shift = 0
        phase_reads = 0
        comparisons = 0
        for shift in candidates:
            if candidate_observer is not None:
                candidate_observer(shift)
            candidate = self.shifted(identifier, shift)
            if best_function is None:
                best_function = candidate
                best_forward_shift = shift
                continue
            for phase in range(support_period):
                left = self.evaluate_function(candidate, phase)
                right = self.evaluate_function(best_function, phase)
                phase_reads += 2
                comparisons += 1
                if left == right:
                    continue
                if left < right:
                    best_function = candidate
                    best_forward_shift = shift
                break
        if best_function is None:
            raise AssertionError("canonical symbolic shift had no candidate")
        return CanonicalShiftResult(
            best_function,
            (-best_forward_shift) % PERIOD,
            candidate_count,
            complete,
            phase_reads,
            comparisons,
        )


class _Builder:
    """Iterative symbolic builder using only public arena operations."""

    def __init__(self, source_view: SemanticContinuation, arena: SemanticFunctionArena):
        self.source_view = source_view
        self.arena = arena
        prefix = f"comma-symbolic-return-{arena.ledger.owner_count}"
        binding_owner = arena.ledger.register(prefix, "symbolic_return_binding")
        shift_owner = arena.ledger.register(prefix + "-shifts", "symbolic_return_shift")
        self.functions: LedgerDict[ContinuationID, SemanticFunctionID] = (
            arena.ledger.make_dict(binding_owner, nodes_per_entry=1)
        )
        self.binding_owner = binding_owner
        self.shift_cache: OwnedMemo[
            tuple[SemanticFunctionID, int], SemanticFunctionID
        ] = OwnedMemo(arena.ledger, shift_owner, nodes_per_entry=1)
        clock_shift_owner = arena.ledger.register(
            prefix + "-clock-shifts", "symbolic_return_clock_shift"
        )
        mask_owner = arena.ledger.register(
            prefix + "-masks", "symbolic_return_valid_mask"
        )
        self.clock_shift_cache: OwnedMemo[
            tuple[PortVariable, int], SemanticFunctionID
        ] = OwnedMemo(arena.ledger, clock_shift_owner, nodes_per_entry=1)
        self.valid_mask_cache: OwnedMemo[
            _VALID_MASK_KEY, tuple[SemanticFunctionID, SemanticFunctionID]
        ] = OwnedMemo(arena.ledger, mask_owner, nodes_per_entry=1)
        template_owner = arena.ledger.register(
            prefix + "-output-templates", "symbolic_return_output_template"
        )
        self.output_template_cache: OwnedMemo[
            SemanticFunctionID, _OutputTemplateCore
        ] = OwnedMemo(
            arena.ledger,
            template_owner,
            nodes_per_entry=RETURN_CARDINALITY + 1,
        )
        template_intern_owner = arena.ledger.register(
            prefix + "-output-template-intern", "symbolic_return_template_interner"
        )
        return_partition_owner = arena.ledger.register(
            prefix + "-return-partitions", "symbolic_return_partition"
        )
        self.output_template_intern: OwnedMemo[
            _OutputTemplateKey, SemanticFunctionID
        ] = OwnedMemo(
            arena.ledger,
            template_intern_owner,
            node_cost=return_template_node_cost,
        )
        self.return_partition_cache: OwnedMemo[
            ContinuationID, B1ReturnPartitionRecord
        ] = OwnedMemo(
            arena.ledger,
            return_partition_owner,
            node_cost=return_partition_node_cost,
        )
        self._false = arena.atom(FunctionSignature((), BOOL), 0)
        self._true = arena.atom(FunctionSignature((), BOOL), 1)
        self._zero = arena.atom(FunctionSignature((), _RETURN_SORT), 0)

    def _selector(
        self,
        period: int,
        residue: int,
        bits: dict[str, SemanticFunctionID],
    ) -> SemanticFunctionID:
        components = _PERIOD_COMPONENTS.get(period)
        if components is None:
            raise ValueError(f"unsupported comma local action period {period}")
        result = self._true
        for component, modulus in components:
            result = self.arena.ite(
                _equal_component(
                    self.arena,
                    component,
                    modulus,
                    residue % modulus,
                    bits,
                ),
                result,
                self._false,
            )
        return result

    def _action_function(
        self,
        action: SemanticAction,
        functions: Mapping[ContinuationID, SemanticFunctionID],
    ) -> SemanticFunctionID:
        if action.kind == "goto":
            if action.target is None:
                raise ValueError("symbolic Goto has no target")
            return functions[action.target]
        return self.arena.atom(FunctionSignature((), _RETURN_SORT), return_code(action))

    def build(self) -> SymbolicReturnView:
        bits: dict[str, SemanticFunctionID] = {}
        identifiers = tuple(
            sorted(self.source_view.actions_by_id, key=lambda item: item.local_id)
        )
        for identifier in identifiers:
            actions = self.source_view.actions_by_id[identifier]
            period = len(actions)
            result = self._action_function(actions[0], self.functions)
            for residue in range(1, period):
                result = self.arena.ite(
                    self._selector(period, residue, bits),
                    self._action_function(actions[residue], self.functions),
                    result,
                )
            result = _normalize_clock_function(
                self.arena, result, bits, self.valid_mask_cache
            )
            self.arena.ledger.reserve(self.binding_owner, entries=1, nodes=1)
            self.functions[identifier] = result
        continuation_by_function: dict[SemanticFunctionID, ContinuationID] = {}
        for identifier, function in self.functions.items():
            continuation_by_function.setdefault(function, identifier)
        return SymbolicReturnView(
            self.source_view,
            self.arena,
            MappingProxyType(self.functions),
            self.shift_cache,
            self.clock_shift_cache,
            self.valid_mask_cache,
            self.output_template_cache,
            self.output_template_intern,
            self.return_partition_cache,
            MappingProxyType(continuation_by_function),
        )


def build_symbolic_returns(
    source_view: SemanticContinuation,
    *,
    arena: SemanticFunctionArena | None = None,
) -> SymbolicReturnView:
    """Build complete-return functions bottom-up from an existing CID view."""
    function_arena = SemanticFunctionArena(ResourceLedger()) if arena is None else arena
    return _Builder(source_view, function_arena).build()


__all__ = [
    "RETURN_CARDINALITY",
    "CanonicalOutputTemplateBinding",
    "CanonicalShiftResult",
    "CanonicalSourceBinding",
    "SymbolicReturnView",
    "build_symbolic_returns",
    "decode_return",
    "least_cyclic_rotation",
]
