"""Bind an admitted FutureCID choice to one exact comma macro occurrence.

The semantic provider supplies only the surviving ordered N/Z slot.  This
adapter checks that slot against the source-bound literal fork produced by
the occurrence layer and carries the exact weighted child action onward.  It
does not infer a boundary state from an arbitrary literal integer.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.sequences.comma.boundary_quotient import (
    BoundaryState,
    _affine_weight_signature,
    boundary_source_index,
    boundary_state_signature,
)
from number_compiler.sequences.comma.carry_generator import BitsCharge
from number_compiler.sequences.comma.future_authority import (
    GLOBAL_RELEASE_CONTRACT_ID,
    GLOBAL_RELEASE_SESSION_ID,
    GLOBAL_RELEASE_THEOREM_ID,
    SOURCE20_FIRST_FORK_CHILDREN,
    SOURCE20_FIRST_FORK_INDEX,
    SOURCE20_FIRST_FORK_VALUE,
    SOURCE20_SELECTED_CHILD,
    SOURCE20_SELECTED_CHILD_INDEX,
    _valid_artifact_digest,
)
from number_compiler.sequences.comma.future_provider import (
    SemanticFutureProvider,
    SemanticFutureProviderLease,
    UnrankedChildSelection,
    WorkCharger,
)
from number_compiler.sequences.comma.occurrence import (
    BoundaryOccurrence,
    MacroChildOccurrence,
    OccurrencePrefixReturn,
)
from number_compiler.sequences.comma.weighted_return import WeightedBoundaryAction

FutureProvider = SemanticFutureProvider | SemanticFutureProviderLease
_SEMANTIC_MACRO_CHILD_SEAL = object()
_SOURCE20_ENTRY_SEAL = object()


def _numeric_payload_signature(
    literal_value: int,
    weighted_action: WeightedBoundaryAction,
) -> tuple[object, ...]:
    if type(weighted_action) is not WeightedBoundaryAction:
        raise ValueError("semantic macro child has malformed numeric payload")
    if (
        type(literal_value) is not int
        or type(weighted_action.exponent_delta) is not int
    ):
        raise ValueError("semantic macro child has malformed numeric payload")
    return (
        literal_value,
        boundary_state_signature(weighted_action.start),
        boundary_state_signature(weighted_action.end),
        weighted_action.exponent_delta,
        _affine_weight_signature(weighted_action.weight),
    )


def _exact_source_class(
    provider: FutureProvider,
    state: BoundaryState,
    *,
    charge_work: WorkCharger,
    class_count: int,
) -> int:
    """Reject aliased or out-of-range values at the provider lookup boundary."""
    class_id = provider.source_class(state, charge_work=charge_work)
    if (
        type(class_id) is not int
        or type(class_count) is not int
        or class_count <= 0
        or not 0 <= class_id < class_count
    ):
        raise ValueError("semantic provider returned a malformed source CID")
    return class_id


def _validate_selection_class_bindings(
    source: BoundaryState,
    ordered_children: tuple[BoundaryState, ...],
    selection: UnrankedChildSelection,
    provider: FutureProvider,
    *,
    charge_work: WorkCharger,
) -> None:
    """Bind published source/child CIDs to this exact ordered occurrence."""
    if (
        type(provider) not in (SemanticFutureProvider, SemanticFutureProviderLease)
        or type(selection) is not UnrankedChildSelection
        or type(selection.source) is not BoundaryState
        or type(selection.source_class) is not int
        or selection.source_class < 0
        or type(selection.fork_coefficient) is not int
        or not 2 <= selection.fork_coefficient <= 9
        or type(selection.ordered_child_classes) is not tuple
        or len(selection.ordered_child_classes) != 2
        or any(
            type(cid) is not int or cid < 0 for cid in selection.ordered_child_classes
        )
        or type(selection.selected_slot) is not int
        or selection.selected_slot not in (0, 1)
    ):
        raise ValueError("semantic provider returned malformed FutureCID fields")
    if (
        type(source) is not BoundaryState
        or type(ordered_children) is not tuple
        or len(ordered_children) != 2
        or any(type(child) is not BoundaryState for child in ordered_children)
    ):
        raise ValueError("semantic branch has malformed ordered boundary states")
    if boundary_source_index(selection.source) != boundary_source_index(source):
        raise ValueError("semantic provider selected a different source state")

    class_count = provider.class_count
    if type(class_count) is not int or class_count <= 0:
        raise ValueError("semantic provider returned a malformed class count")
    source_class = _exact_source_class(
        provider,
        source,
        charge_work=charge_work,
        class_count=class_count,
    )
    if selection.source_class != source_class:
        raise ValueError("semantic provider selection has another source CID")
    child_classes = tuple(
        _exact_source_class(
            provider,
            child,
            charge_work=charge_work,
            class_count=class_count,
        )
        for child in ordered_children
    )
    if selection.ordered_child_classes != child_classes:
        raise ValueError(
            "semantic provider child slots differ from the literal N/Z order"
        )
    if selection.selected_class != child_classes[selection.selected_slot]:
        raise ValueError("semantic provider selected class differs from its slot")


@dataclass(frozen=True, slots=True, init=False)
class SemanticMacroChild:
    """A source-bound surviving child with its exact literal and weighted edge."""

    source: BoundaryOccurrence
    prefix: OccurrencePrefixReturn
    selection: UnrankedChildSelection
    occurrence: MacroChildOccurrence
    literal_value: int
    weighted_action: WeightedBoundaryAction
    _selection_snapshot: tuple[object, ...] = field(
        repr=False,
        compare=False,
        hash=False,
    )
    _numeric_payload_snapshot: tuple[object, ...] = field(
        repr=False,
        compare=False,
        hash=False,
    )
    _seal: object

    def __init__(
        self,
        source: BoundaryOccurrence,
        prefix: OccurrencePrefixReturn,
        selection: UnrankedChildSelection,
        occurrence: MacroChildOccurrence,
        literal_value: int,
        weighted_action: WeightedBoundaryAction,
        *,
        _seal: object,
    ) -> None:
        if _seal is not _SEMANTIC_MACRO_CHILD_SEAL:
            raise TypeError("use the source-bound semantic branch adapter")
        object.__setattr__(self, "source", source)
        object.__setattr__(self, "prefix", prefix)
        object.__setattr__(self, "selection", selection)
        object.__setattr__(self, "occurrence", occurrence)
        object.__setattr__(self, "literal_value", literal_value)
        object.__setattr__(self, "weighted_action", weighted_action)
        object.__setattr__(
            self,
            "_selection_snapshot",
            (
                boundary_source_index(selection.source),
                selection.source_class,
                selection.fork_coefficient,
                selection.ordered_child_classes,
                selection.selected_slot,
            ),
        )
        object.__setattr__(
            self,
            "_numeric_payload_snapshot",
            _numeric_payload_signature(literal_value, weighted_action),
        )
        object.__setattr__(self, "_seal", _seal)
        self._validate()

    def _validate(self) -> None:
        if getattr(self, "_seal", None) is not _SEMANTIC_MACRO_CHILD_SEAL:
            raise ValueError("invalid semantic macro child")
        if (
            type(self.source) is not BoundaryOccurrence
            or type(self.prefix) is not OccurrencePrefixReturn
            or type(self.selection) is not UnrankedChildSelection
            or type(self.occurrence) is not MacroChildOccurrence
            or type(self.literal_value) is not int
            or type(self.weighted_action) is not WeightedBoundaryAction
        ):
            raise ValueError("invalid semantic macro child fields")
        self.source._validate()
        selected_classes = self.selection.ordered_child_classes
        if (
            type(self.selection.source) is not BoundaryState
            or type(self.selection.source_class) is not int
            or self.selection.source_class < 0
            or type(self.selection.fork_coefficient) is not int
            or not 2 <= self.selection.fork_coefficient <= 9
            or type(selected_classes) is not tuple
            or len(selected_classes) != 2
            or any(type(cid) is not int or cid < 0 for cid in selected_classes)
            or type(self.selection.selected_slot) is not int
            or self.selection.selected_slot not in (0, 1)
        ):
            raise ValueError("semantic macro child has malformed FutureCID fields")
        if getattr(self, "_selection_snapshot", None) != (
            boundary_source_index(self.selection.source),
            self.selection.source_class,
            self.selection.fork_coefficient,
            selected_classes,
            self.selection.selected_slot,
        ):
            raise ValueError("semantic macro child FutureCID snapshot changed")
        if getattr(self, "_numeric_payload_snapshot", None) != (
            _numeric_payload_signature(self.literal_value, self.weighted_action)
        ):
            raise ValueError("semantic macro child numeric payload snapshot changed")
        slot = self.selection.selected_slot
        if (
            type(slot) is not int
            or slot not in (0, 1)
            or self.prefix.source != self.source
            or boundary_state_signature(self.selection.source)
            != boundary_state_signature(self.source.state)
            or self.occurrence.prefix is not self.prefix
            or self.occurrence.kind != ("N" if slot == 0 else "Z")
            or self.selection.fork_coefficient != self.prefix.template.destination_a
            or boundary_state_signature(self.weighted_action.start)
            != boundary_state_signature(self.source.state)
            or boundary_state_signature(self.weighted_action.end)
            != boundary_state_signature(self.occurrence.target.state)
            or self.weighted_action.exponent_delta != self.prefix.width_delta
        ):
            raise ValueError("semantic macro child fields lost their source binding")

    @property
    def fork_event_offset(self) -> int:
        """Number of forced literal steps before the selected fork edge."""
        self._validate()
        return self.prefix.transition_count

    @property
    def total_transition_count(self) -> int:
        """Forced prefix steps plus the one selected-child transition."""
        self._validate()
        return self.prefix.transition_count + 1

    @property
    def target(self) -> BoundaryOccurrence:
        self._validate()
        return self.occurrence.target


@dataclass(frozen=True, slots=True, init=False)
class Source20FirstChildEntry:
    """Global-theorem binding for the exact first source-20 path edge.

    Indices are one-based: the parent is at 412,987,859 and the selected child
    is at 412,987,860.  The child's exact weighted-chart source is N, a=2,
    exponent=10.  This entry is issued only by a provider carrying the full
    global release contract for the same checked artifact.
    """

    parent_index: int
    parent_value: int
    ordered_children: tuple[int, int]
    selected_slot: int
    child_index: int
    child_value: int
    source_class: int
    artifact_sha256: str
    session_id: str
    theorem_id: str
    contract_id: str
    _occurrence: BoundaryOccurrence = field(repr=False, compare=False, hash=False)
    _snapshot: tuple[object, ...] = field(repr=False, compare=False, hash=False)
    _seal: object = field(repr=False, compare=False, hash=False)

    def __init__(
        self,
        parent_index: int,
        parent_value: int,
        ordered_children: tuple[int, int],
        selected_slot: int,
        child_index: int,
        child_value: int,
        source_class: int,
        artifact_sha256: str,
        occurrence: BoundaryOccurrence,
        *,
        _seal: object,
    ) -> None:
        if _seal is not _SOURCE20_ENTRY_SEAL:
            raise TypeError("use the checked source-20 first-child binder")
        object.__setattr__(self, "parent_index", parent_index)
        object.__setattr__(self, "parent_value", parent_value)
        object.__setattr__(self, "ordered_children", ordered_children)
        object.__setattr__(self, "selected_slot", selected_slot)
        object.__setattr__(self, "child_index", child_index)
        object.__setattr__(self, "child_value", child_value)
        object.__setattr__(self, "source_class", source_class)
        object.__setattr__(self, "artifact_sha256", artifact_sha256)
        object.__setattr__(self, "session_id", GLOBAL_RELEASE_SESSION_ID)
        object.__setattr__(self, "theorem_id", GLOBAL_RELEASE_THEOREM_ID)
        object.__setattr__(self, "contract_id", GLOBAL_RELEASE_CONTRACT_ID)
        object.__setattr__(self, "_occurrence", occurrence)
        object.__setattr__(self, "_seal", _seal)
        object.__setattr__(self, "_snapshot", self._current_snapshot())
        self._validate()

    def _current_snapshot(self) -> tuple[object, ...]:
        occurrence = self._occurrence
        state = occurrence.state if type(occurrence) is BoundaryOccurrence else None
        if type(state) is BoundaryState:
            state_signature: tuple[object, ...] = (
                state.kind,
                state.a,
                state.exponent_residue,
                occurrence.exponent,
            )
        else:
            state_signature = ()
        return (
            self.parent_index,
            self.parent_value,
            self.ordered_children,
            self.selected_slot,
            self.child_index,
            self.child_value,
            self.source_class,
            self.artifact_sha256,
            self.session_id,
            self.theorem_id,
            self.contract_id,
            state_signature,
        )

    def _validate(self) -> None:
        if getattr(self, "_seal", None) is not _SOURCE20_ENTRY_SEAL:
            raise ValueError("invalid source-20 first-child entry")
        if (
            type(self.parent_index) is not int
            or self.parent_index != SOURCE20_FIRST_FORK_INDEX
            or type(self.parent_value) is not int
            or self.parent_value != SOURCE20_FIRST_FORK_VALUE
            or type(self.ordered_children) is not tuple
            or len(self.ordered_children) != 2
            or any(type(value) is not int for value in self.ordered_children)
            or self.ordered_children != SOURCE20_FIRST_FORK_CHILDREN
            or type(self.selected_slot) is not int
            or self.selected_slot != 0
            or type(self.child_index) is not int
            or self.child_index != SOURCE20_SELECTED_CHILD_INDEX
            or type(self.child_value) is not int
            or self.child_value != SOURCE20_SELECTED_CHILD
            or type(self.source_class) is not int
            or self.source_class < 0
            or not _valid_artifact_digest(self.artifact_sha256)
            or type(self.session_id) is not str
            or self.session_id != GLOBAL_RELEASE_SESSION_ID
            or type(self.theorem_id) is not str
            or self.theorem_id != GLOBAL_RELEASE_THEOREM_ID
            or type(self.contract_id) is not str
            or self.contract_id != GLOBAL_RELEASE_CONTRACT_ID
            or type(self._occurrence) is not BoundaryOccurrence
        ):
            raise ValueError("source-20 first-child authority changed")
        self._occurrence._validate()
        if (
            boundary_state_signature(self._occurrence.state)
            != boundary_state_signature(BoundaryState("N", 2, 10))
            or self._occurrence.exponent != 10
            or getattr(self, "_snapshot", None) != self._current_snapshot()
        ):
            raise ValueError("source-20 weighted occurrence binding changed")

    def weighted_source(
        self,
        provider: FutureProvider,
        *,
        charge_work: WorkCharger,
    ) -> BoundaryOccurrence:
        """Return the child occurrence only under its original global artifact."""
        self._validate()
        if type(provider) not in (SemanticFutureProvider, SemanticFutureProviderLease):
            raise TypeError("source-20 entry needs its exact semantic provider")
        provider.require_global_release_admission()
        if provider.artifact_sha256 != self.artifact_sha256:
            raise PermissionError("source-20 entry belongs to another artifact")
        class_count = provider.class_count
        source_class = _exact_source_class(
            provider,
            self._occurrence.state,
            charge_work=charge_work,
            class_count=class_count,
        )
        if source_class != self.source_class:
            raise PermissionError("source-20 provider class binding changed")
        row = provider.class_row(source_class, charge_work=charge_work)
        if row.rank is not None or row.control.kind != "fork":
            raise PermissionError("source-20 child is not an admitted infinite source")
        return self._occurrence


def bind_source20_first_child_entry(
    *,
    parent_index: int,
    parent_value: int,
    ordered_children: tuple[int, int],
    child_index: int,
    provider: FutureProvider,
    charge_work: WorkCharger,
    charge_bits: BitsCharge | None = None,
) -> Source20FirstChildEntry:
    """Bind the proved first source-20 edge without ranking its children."""
    if (
        type(parent_index) is not int
        or type(parent_value) is not int
        or type(child_index) is not int
        or type(ordered_children) is not tuple
        or len(ordered_children) != 2
        or any(type(value) is not int for value in ordered_children)
    ):
        raise ValueError("source-20 edge needs exact indices and ordered integers")
    if (
        parent_index != SOURCE20_FIRST_FORK_INDEX
        or parent_value != SOURCE20_FIRST_FORK_VALUE
        or ordered_children != SOURCE20_FIRST_FORK_CHILDREN
        or child_index != SOURCE20_SELECTED_CHILD_INDEX
    ):
        raise ValueError("source-20 edge differs from the global first-child theorem")
    if type(provider) not in (SemanticFutureProvider, SemanticFutureProviderLease):
        raise TypeError("source-20 edge needs its exact semantic provider")
    if not callable(charge_work):
        raise TypeError("source-20 edge requires a work charger")
    if charge_bits is not None and not callable(charge_bits):
        raise TypeError("source-20 edge bit charger must be callable")
    provider.require_global_release_admission()

    occurrence = BoundaryOccurrence(BoundaryState("N", 2, 10), 10)
    if (
        occurrence.value(charge_work=charge_work, charge_bits=charge_bits)
        != (ordered_children[0])
    ):
        raise ValueError("source-20 selected child differs from its weighted source")
    class_count = provider.class_count
    source_class = _exact_source_class(
        provider,
        occurrence.state,
        charge_work=charge_work,
        class_count=class_count,
    )
    row = provider.class_row(source_class, charge_work=charge_work)
    if row.rank is not None or row.control.kind != "fork":
        raise ValueError("source-20 child has no infinite weighted continuation")
    return Source20FirstChildEntry(
        parent_index,
        parent_value,
        ordered_children,
        0,
        child_index,
        SOURCE20_SELECTED_CHILD,
        source_class,
        provider.artifact_sha256,
        occurrence,
        _seal=_SOURCE20_ENTRY_SEAL,
    )


def select_semantic_macro_child(
    source: BoundaryOccurrence,
    prefix: OccurrencePrefixReturn,
    *,
    fork_value: int,
    ordered_literal_children: tuple[int, int],
    provider: FutureProvider,
    charge_work: WorkCharger,
    charge_bits: BitsCharge | None = None,
) -> SemanticMacroChild:
    """Select the admitted unique unranked child for one exact macro fork.

    ``source`` must be the exact boundary occurrence used to construct
    ``prefix``.  The caller supplies the terminal integer and its ordered
    literal N/Z children from its current source view; all are checked against
    the occurrence return before the FutureCID slot is applied.
    """
    if type(source) is not BoundaryOccurrence:
        raise TypeError("semantic branch source must be an exact boundary occurrence")
    source._validate()
    if type(prefix) is not OccurrencePrefixReturn:
        raise TypeError("semantic branch needs an exact occurrence prefix")
    if type(provider) not in (SemanticFutureProvider, SemanticFutureProviderLease):
        raise TypeError("semantic branch needs a kernel-admitted future provider")
    if not callable(charge_work):
        raise TypeError("semantic branch requires a work charger")
    if charge_bits is not None and not callable(charge_bits):
        raise TypeError("semantic branch bit charger must be callable")

    provider.require_runtime_admission()
    if prefix.source != source:
        raise ValueError("semantic branch prefix is bound to another source occurrence")
    if prefix.template.source != source.state:
        raise ValueError("semantic branch template is bound to another source state")
    if prefix.outcome != "fork":
        raise ValueError("semantic branch source does not reach a fork")
    if type(fork_value) is not int:
        raise ValueError("semantic branch terminal differs from its exact prefix")
    terminal_value = prefix.terminal_value
    charge_work(1)
    if charge_bits is not None:
        charge_bits(fork_value.bit_length() + terminal_value.bit_length())
    if fork_value != terminal_value:
        raise ValueError("semantic branch terminal differs from its exact prefix")
    if (
        type(ordered_literal_children) is not tuple
        or len(ordered_literal_children) != 2
        or any(type(value) is not int for value in ordered_literal_children)
    ):
        raise TypeError("semantic branch needs both ordered literal integer children")

    ordered_children = prefix.ordered_literal_children(
        charge_work=charge_work,
        charge_bits=charge_bits,
    )
    boundary_children, expected_literals = ordered_children.validated_parts()
    if len(boundary_children) != 2:
        raise ValueError("semantic branch prefix lost its ordered N/Z children")
    charge_work(1)
    if charge_bits is not None:
        charge_bits(
            sum(value.bit_length() for value in ordered_literal_children)
            + sum(value.bit_length() for value in expected_literals)
        )
    if ordered_literal_children != expected_literals:
        raise ValueError(
            "semantic branch literals differ from the exact boundary children"
        )
    destination_a = prefix.template.destination_a
    if type(destination_a) is not int:
        raise ValueError("semantic branch fork lost its exact destination coefficient")

    selection = provider.select_unique_unranked_child(
        source.state,
        charge_work=charge_work,
    )
    if type(selection) is not UnrankedChildSelection:
        raise TypeError("semantic provider returned a malformed child selection")
    _validate_selection_class_bindings(
        source.state,
        (boundary_children[0].state, boundary_children[1].state),
        selection,
        provider,
        charge_work=charge_work,
    )
    if selection.fork_coefficient != destination_a:
        raise ValueError(
            "semantic provider Fork coefficient differs from the literal macro"
        )
    occurrence = ordered_children.bind_slot(selection.selected_slot)
    if occurrence.target is not boundary_children[selection.selected_slot]:
        raise ValueError("semantic provider slot maps to another boundary occurrence")
    literal_value = expected_literals[selection.selected_slot]
    weighted_action = occurrence.weighted_action()
    if (
        boundary_state_signature(weighted_action.start)
        != boundary_state_signature(source.state)
        or boundary_state_signature(weighted_action.end)
        != boundary_state_signature(occurrence.target.state)
        or weighted_action.exponent_delta != prefix.width_delta
    ):
        raise ValueError("semantic branch lost its exact weighted occurrence binding")

    return SemanticMacroChild(
        source,
        prefix,
        selection,
        occurrence,
        literal_value,
        weighted_action,
        _seal=_SEMANTIC_MACRO_CHILD_SEAL,
    )


def select_global_semantic_macro_child(
    source: BoundaryOccurrence,
    prefix: OccurrencePrefixReturn,
    *,
    fork_value: int,
    ordered_literal_children: tuple[int, int],
    provider: FutureProvider,
    charge_work: WorkCharger,
    charge_bits: BitsCharge | None = None,
) -> SemanticMacroChild:
    """Require the global theorem before selecting a production branch.

    Finite fixture admission is sufficient for testing the exact occurrence
    adapter, but cannot establish an infinite continuation in production.
    Check release authority before observing the occurrence or its children.
    """
    if type(provider) not in (SemanticFutureProvider, SemanticFutureProviderLease):
        raise TypeError("semantic branch needs a kernel-admitted future provider")
    provider.require_global_release_admission()
    return select_semantic_macro_child(
        source,
        prefix,
        fork_value=fork_value,
        ordered_literal_children=ordered_literal_children,
        provider=provider,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )


__all__ = [
    "SemanticMacroChild",
    "Source20FirstChildEntry",
    "bind_source20_first_child_entry",
    "select_global_semantic_macro_child",
    "select_semantic_macro_child",
]
