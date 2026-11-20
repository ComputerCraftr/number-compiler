"""Ledger-owned memo of immutable source-free Collatz action templates."""

from __future__ import annotations

from collections.abc import Generator
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Self, TypeAlias

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.interfaces.border_macros import BorderWireValue
from number_compiler.resources.construction_scope import RuntimeConstruction
from number_compiler.resources.ledger import (
    LedgerReservation,
    OwnedMemo,
    ResourceLedger,
)
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.collatz.border_identity import (
    BOUNDARY_SELECTOR_IDENTITIES,
    CLOSED_BORDER_CYCLE_TAG,
    CYCLE_26847,
    ENTRY_0563,
    ENTRY_89_AT_NINE,
    ENTRY_421,
    ENTRY_4721,
    ENTRY_26847_PHASES,
    MIXED_PARITY_MOTIF_TAG,
    PATH_305,
    PATH_630,
    BoundaryActionIdentity,
    CycleEntryPhase,
    GuardedBorderPath,
    MixedParityMotif,
    cycle_phase,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)

BoundaryTemplateIdentity = BoundaryActionIdentity | MixedParityMotif
BoundaryTemplateKey: TypeAlias = tuple[BorderWireValue, int]
BoundaryTemplateValue: TypeAlias = tuple[
    BorderWireValue,
    int,
    tuple[DyadicTerminalFieldAction, int, int, int],
]
# Exact action-template semantics, not Python identity hashes or occurrence IDs.
# Immutable wire keys retain every selector guard and the canonical entry phase.
_BOUNDARY_ID_BY_WIRE = {
    identity.structural_key(): identity for identity in BOUNDARY_SELECTOR_IDENTITIES
}
_BOUNDARY_DECLARATIONS = tuple(
    (identity, identity.structural_key()) for identity in BOUNDARY_SELECTOR_IDENTITIES
)


def _template_identity_key(identity: BoundaryTemplateIdentity) -> BorderWireValue:
    """Validate an input once, then use a pure, source-free semantic key."""
    if type(identity) is MixedParityMotif:
        identity.require_valid()
        return (MIXED_PARITY_MOTIF_TAG, identity.bits)
    if type(identity) is CycleEntryPhase:
        key = identity.structural_key()
    elif type(identity) is GuardedBorderPath:
        key = identity.structural_key()
    else:
        raise TypeError("boundary action template key is malformed")
    canonical = _BOUNDARY_ID_BY_WIRE.get(key)
    if canonical is None:
        raise ValueError("unknown Collatz boundary action identity")
    # Canonical identities are checked by singleton pointer here only to
    # authenticate the registry declaration.  The cache key is entirely the
    # semantic wire value, never a Python object ID or source occurrence.
    for registered, declared in _BOUNDARY_DECLARATIONS:
        if identity is registered and declared != key:
            raise ValueError(
                "registered boundary action identity changed after admission"
            )
    # The canonical instance may be mutated through object.__setattr__, so
    # authenticate its declaration even when a separately constructed but
    # structurally equivalent identity was supplied.
    if canonical is not identity and canonical.structural_key() != key:
        raise ValueError("registered boundary action identity changed after admission")
    return key


def _template_identity_cost(identity: BorderWireValue) -> int:
    """Return the stored structural word size without widening its wire type."""
    if type(identity) is not tuple or len(identity) != 2:
        return 1
    tag, word = identity
    if tag == MIXED_PARITY_MOTIF_TAG and type(word) is tuple:
        return 2 + len(word)
    if tag == CLOSED_BORDER_CYCLE_TAG and type(word) is tuple:
        return len(word)
    return 1


def _template_construction_scratch_nodes(
    identity: BoundaryTemplateIdentity, repetitions: int
) -> int:
    """Bound live coefficient and temporary storage before a cold template build."""
    if type(identity) is MixedParityMotif:
        identity.require_valid()
        steps = len(identity.bits) * repetitions
        odds = sum(identity.bits) * repetitions
    else:
        # Every registered border template has at most five normalized letters
        # and two odd events per repetition. This deliberately bounds all
        # action coefficients without duplicating the family-specific formulas
        # used by the action constructor.
        steps = 5 * repetitions + 1
        odds = 2 * repetitions
    coefficient_bits = 4 * (steps + 2 * odds + 8)
    return 128 + 32 * ((coefficient_bits + 63) // 64)


def boundary_macro_26847_phase(identity: BoundaryActionIdentity) -> int | None:
    """Return a typed cycle occurrence's phase on the five-digit border."""
    for phase, entry in enumerate(ENTRY_26847_PHASES):
        if identity is entry:
            entry.require_valid()
            return phase
    return cycle_phase(identity, CYCLE_26847)


def build_boundary_action_template(
    identity: BoundaryTemplateIdentity, repetitions: int
) -> tuple[DyadicTerminalFieldAction, int, int, int]:
    """Intern the *full parity action*, including accumulator coefficients.

    Unlike an innovation Moore observer ID, this key represents an exact
    certified affine program, not just equal carry/borrow outputs. The caller
    must still independently authenticate the source's guard and exit.
    """
    if type(repetitions) is not int or repetitions < 1:
        raise ValueError("guarded boundary action needs a positive repeat count")
    if isinstance(identity, MixedParityMotif):
        fields = DyadicTerminalFieldAction.zero_run(0)
        for bit in identity.bits:
            fields = fields.then(
                DyadicTerminalFieldAction.one_run(1)
                if bit
                else DyadicTerminalFieldAction.zero_run(1)
            )
        fields = fields.power(repetitions)
        odd = sum(identity.bits) * repetitions
        ticks = fields.steps + odd
    elif identity == ENTRY_421:
        motif = DyadicTerminalFieldAction.one_run(1).then(
            DyadicTerminalFieldAction.zero_run(1)
        )
        fields = (
            DyadicTerminalFieldAction.zero_run(2)
            .then(motif.power(repetitions - 1))
            .then(DyadicTerminalFieldAction.one_run(1))
        )
        odd = repetitions
        ticks = 3 * repetitions + 1
    elif identity in (ENTRY_4721, ENTRY_0563):
        fields = DyadicTerminalFieldAction.zero_run(1).then(
            DyadicTerminalFieldAction.one_run(2 * repetitions)
        )
        odd = 2 * repetitions
        ticks = 4 * repetitions + 1
    elif (phase := boundary_macro_26847_phase(identity)) is not None:
        fields = DyadicTerminalFieldAction.zero_run(4 - phase)
        if repetitions > 1:
            motif = DyadicTerminalFieldAction.one_run(1).then(
                DyadicTerminalFieldAction.zero_run(3)
            )
            fields = fields.then(motif.power(repetitions - 1))
        fields = fields.then(DyadicTerminalFieldAction.one_run(1))
        odd = repetitions
        ticks = 5 * repetitions + 1 - phase
    elif identity == PATH_630:
        fields = (
            DyadicTerminalFieldAction.zero_run(1)
            .then(DyadicTerminalFieldAction.one_run(1))
            .then(DyadicTerminalFieldAction.zero_run(repetitions))
        )
        odd = 1
        ticks = repetitions + 3
    elif identity == PATH_305:
        fields = DyadicTerminalFieldAction.one_run(1).then(
            DyadicTerminalFieldAction.zero_run(repetitions)
        )
        odd = 1
        ticks = repetitions + 2
    elif identity == ENTRY_89_AT_NINE:
        fields = DyadicTerminalFieldAction.one_run(repetitions)
        odd = repetitions
        ticks = 2 * repetitions
    else:
        raise ValueError("unknown source-certified boundary action")
    if fields.steps + odd != ticks:
        raise AssertionError("guarded template lost its physical tick clock")
    return fields, odd, ticks, fields.source_residue


@dataclass(slots=True)
class _ScratchLease:
    reservation: LedgerReservation
    nodes: int


class BoundaryActionTemplateMemo:
    """Per-query, ledger-accounted templates for exact guarded parity actions."""

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("boundary action templates require their query ledger")
        self.ledger = ledger
        self._closed = False
        self._closing = False
        self._scratch_owner: int | None = None
        self._scratch_reservations: tuple[_ScratchLease, ...] = ()
        self._scratch_store: LedgerDict[int, None] | None = None
        self._templates: (
            OwnedMemo[
                BoundaryTemplateKey,
                BoundaryTemplateValue,
            ]
            | None
        ) = None

    def __enter__(self) -> Self:
        if self._closed or self._closing:
            raise RuntimeError("boundary action template memo is closed")
        return self

    def __exit__(self, *_args: object) -> None:
        self.dispose()

    def dispose(self) -> None:
        """Release the memo; retain a retry path if ledger cleanup fails."""
        if self._closed:
            return
        self._closing = True
        for lease in tuple(reversed(self._scratch_reservations)):
            lease.reservation.close()
            self._remove_scratch_lease(lease)
        if self._templates is not None:
            self._templates.dispose()
        if self._scratch_owner is not None:
            self.ledger.mark_disposed(self._scratch_owner)
        self._closing = False
        self._closed = True

    def _scratch_account(self) -> int:
        owner = self._scratch_owner
        if owner is not None:
            return owner
        owner = self.ledger.register(
            f"collatz-boundary-template-scratch-{self.ledger.owner_count}",
            "temporary",
        )
        try:
            store = self.ledger.make_dict(owner, key_type=int, value_type=type(None))
            self.ledger.register_container(
                owner,
                store,
                node_count=self._scratch_node_count,
            )
        except BaseException:
            self.ledger.mark_disposed(owner)
            raise
        self._scratch_owner = owner
        self._scratch_store = store
        return owner

    def _scratch_node_count(self) -> int:
        return sum(lease.nodes for lease in self._scratch_reservations)

    def _remove_scratch_lease(self, lease: _ScratchLease) -> None:
        self._scratch_reservations = tuple(
            current for current in self._scratch_reservations if current is not lease
        )

    @contextmanager
    def scratch(self, *, nodes: int) -> Generator[None, None, None]:
        """Reserve bounded selector/construction temporaries on the query ledger."""
        if self._closed or self._closing:
            raise RuntimeError("boundary action template memo is closed")
        owner = self._scratch_account()
        reservation = LedgerReservation(self.ledger, owner)
        lease = _ScratchLease(reservation, 0)
        self._scratch_reservations = (*self._scratch_reservations, lease)
        try:
            reservation.reserve(nodes=nodes)
            lease.nodes = nodes
        except BaseException as error:
            try:
                reservation.close()
            except BaseException as cleanup_error:
                raise error from cleanup_error
            else:
                self._remove_scratch_lease(lease)
            raise
        try:
            yield
        finally:
            reservation.close()
            self._remove_scratch_lease(lease)

    def _memo(
        self,
    ) -> OwnedMemo[
        BoundaryTemplateKey,
        BoundaryTemplateValue,
    ]:
        if self._templates is None:
            with RuntimeConstruction(self.ledger):
                owner = self.ledger.register(
                    f"collatz-boundary-action-templates-{self.ledger.owner_count}",
                    "query_memo",
                )

                def template_cost(
                    _key: BoundaryTemplateKey,
                    value: BoundaryTemplateValue,
                ) -> int:
                    template = value[2]
                    fields = template[0]
                    return (
                        8
                        + _template_identity_cost(value[0])
                        + sum(
                            (max(1, component.bit_length()) + 63) // 64
                            for component in (
                                fields.steps,
                                fields.gain,
                                fields.offset,
                                fields.sum_gain,
                                fields.sum_offset,
                                fields.previous_gain,
                                fields.previous_offset,
                                template[1],
                                template[2],
                                template[3],
                            )
                        )
                    )

                templates = OwnedMemo(
                    self.ledger,
                    owner,
                    node_cost=template_cost,
                    evictable=True,
                )
                self.ledger.register_execution_root(self)
                for counter in (
                    "lookups",
                    "hits",
                    "misses",
                    "publications",
                    "bypasses",
                ):
                    self.ledger.bump(f"collatz_boundary_template_{counter}", 0)
            self._templates = templates
        return self._templates

    def get(
        self, identity: BoundaryTemplateIdentity, repetitions: int
    ) -> tuple[DyadicTerminalFieldAction, int, int, int]:
        if self._closed or self._closing:
            raise RuntimeError("boundary action template memo is closed")
        if type(repetitions) is not int:
            raise TypeError("boundary action template repeat count is malformed")
        if repetitions < 1:
            raise ValueError("boundary action repeat count must be positive")
        semantic = _template_identity_key(identity)
        key = semantic, repetitions
        self.ledger.bump(_collatz_keys.COLLATZ_BOUNDARY_TEMPLATE_LOOKUPS)
        memo = self._memo()
        cached = memo.get(key)
        if cached is not None:
            if (
                type(cached) is not tuple
                or len(cached) != 3
                or cached[0] != semantic
                or cached[1] != repetitions
                or type(cached[2]) is not tuple
                or len(cached[2]) != 4
                or type(cached[2][0]) is not DyadicTerminalFieldAction
                or not cached[2][0].producer_issued
                or any(type(value) is not int for value in cached[2][1:])
            ):
                raise ValueError("cached boundary action template is malformed")
            template = cached[2]
            fields, odd, ticks, guard = template
            self.ledger.bump(_collatz_keys.COLLATZ_BOUNDARY_TEMPLATE_VALIDATIONS)
            self.ledger.bump(
                _collatz_keys.COLLATZ_BOUNDARY_TEMPLATE_VALIDATION_OPERAND_BITS,
                fields.gain.bit_length()
                + fields.offset.bit_length()
                + guard.bit_length(),
            )
            if (
                fields.steps <= 0
                or fields.steps + odd != ticks
                or not 0 <= guard < fields.source_modulus
                or (fields.gain * guard + fields.offset) % fields.source_modulus != 0
            ):
                raise ValueError("cached boundary action template is inconsistent")
            self.ledger.bump(_collatz_keys.COLLATZ_BOUNDARY_TEMPLATE_HITS)
            return template
        self.ledger.bump(_collatz_keys.COLLATZ_BOUNDARY_TEMPLATE_MISSES)
        scratch_nodes = _template_construction_scratch_nodes(identity, repetitions)
        with self.scratch(nodes=scratch_nodes):
            if isinstance(identity, MixedParityMotif):
                width = len(identity.bits) * repetitions
                self.ledger.bump(
                    _collatz_keys.COLLATZ_MIXED_CLOCK_COEFFICIENT_CONSTRUCTIONS
                )
                self.ledger.bump(
                    _collatz_keys.COLLATZ_MIXED_CLOCK_REQUESTED_GUARD_BITS, width
                )
            template = build_boundary_action_template(identity, repetitions)
            bound_template: BoundaryTemplateValue = semantic, repetitions, template
            try:
                memo[key] = bound_template
            except BlockContextBudgetExceeded:
                self.ledger.bump(_collatz_keys.COLLATZ_BOUNDARY_TEMPLATE_BYPASSES)
            else:
                self.ledger.bump(_collatz_keys.COLLATZ_BOUNDARY_TEMPLATE_PUBLICATIONS)
        return template


__all__ = [
    "BoundaryActionTemplateMemo",
    "BoundaryTemplateIdentity",
    "boundary_macro_26847_phase",
    "build_boundary_action_template",
]
