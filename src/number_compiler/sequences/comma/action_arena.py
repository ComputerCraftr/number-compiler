"""Ledger-owned comma actions and authenticated boundary templates.

These records describe admitted actions; the source-image adapter remains the sole
scheduler consumer. Boundary macros carry exact arithmetic but no branch authority.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator
from dataclasses import dataclass
from math import gcd
from typing import cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.fields.consumer_pullback import PrefixSafety
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList
from number_compiler.sequences.comma.arithmetic import (
    CycleTransfer,
    cycle_transfer,
    phase_prefix_displacement,
)
from number_compiler.sequences.comma.boundary_quotient import (
    PERIOD,
    AffineWeight,
    BoundaryState,
    MacroTemplate,
    SectorFragment,
    construct_macro,
)
from number_compiler.sequences.comma.cycle_actions import CycleActionReuse


@dataclass(frozen=True, slots=True)
class CommaActionID(ArenaHandle):
    pass


@dataclass(frozen=True, slots=True)
class _Action:
    kind: str
    steps: int
    leading: int = 0
    entering_digit: int = 0
    cycles: int = 0
    displacement: int = 0
    maximum_guard: int = 0
    child_digit: int = 0
    boundary_source: BoundaryState | None = None
    boundary_exponent: int = 0
    before: CommaActionID | None = None
    after: CommaActionID | None = None


def _action_snapshot(node: _Action) -> tuple[object, ...]:
    """Keep primitive fields separate from mutable private record identities."""

    def handle(value: CommaActionID | None) -> tuple[object, str, int] | None:
        if value is None:
            return None
        return value.owner, value.kind, value.local_id

    state = node.boundary_source
    boundary = None if state is None else (state.kind, state.a, state.exponent_residue)
    return (
        node.kind,
        node.steps,
        node.leading,
        node.entering_digit,
        node.cycles,
        node.displacement,
        node.maximum_guard,
        node.child_digit,
        boundary,
        node.boundary_exponent,
        handle(node.before),
        handle(node.after),
    )


def _affine_snapshot(value: AffineWeight) -> tuple[int, int, int, int]:
    return (
        id(value),
        value.numerator_scale,
        value.numerator_offset,
        value.denominator,
    )


def _fragment_snapshot(fragment: SectorFragment) -> tuple[object, ...]:
    return (
        id(fragment),
        fragment.leading,
        fragment.entering_digit,
        _affine_snapshot(fragment.complete_cycles),
        fragment.period,
        fragment.displacement,
        fragment.maximum_guard,
        fragment.literal_steps,
        fragment.literal_increment,
    )


def _template_header(template: MacroTemplate) -> tuple[object, ...]:
    state = template.source
    return (
        id(template),
        id(state),
        state.kind,
        state.a,
        state.exponent_residue,
        template.outcome,
        template.exponent_delta,
        template.destination_a,
        _affine_snapshot(template.weight),
        _affine_snapshot(template.endpoint),
        id(template.ordered_children),
        tuple(
            (id(child), child.kind, child.a, child.exponent_residue)
            for child in template.ordered_children
        ),
        id(template.sector_fragments),
        id(template.prefix_weights),
        id(template.prefix_displacements),
    )


def _template_seal(template: MacroTemplate) -> tuple[object, ...]:
    """Copy primitive descriptor fields once, never a hot-path full hash."""
    return (
        _template_header(template),
        tuple(_fragment_snapshot(item) for item in template.sector_fragments),
        tuple(_affine_snapshot(item) for item in template.prefix_weights),
        tuple(_affine_snapshot(item) for item in template.prefix_displacements),
    )


def _seal_integer_bits(value: object) -> int:
    """Count integer payload bits with an explicit bounded nesting stack."""
    stack: list[Iterator[object]] = [iter((value,))]
    bits = 0
    while stack:
        try:
            item = next(stack[-1])
        except StopIteration:
            stack.pop()
            continue
        if type(item) is int:
            bits += max(1, item.bit_length())
        elif type(item) is tuple:
            if len(stack) >= 8:
                raise ValueError("comma boundary seal nesting exceeds schema")
            stack.append(iter(item))
    return bits


class CommaActionArena:
    """Ledger-owned, scoped binary action DAG for admitted phase cycles."""

    def __init__(
        self, ledger: ResourceLedger, max_work: int, *, shared_cache: bool = True
    ) -> None:
        self.ledger = ledger
        self.max_work = max_work
        self.token = ArenaToken("comma-actions")
        self.kind = "comma-action"
        self._owner = ledger.register("comma-actions", "temporal_action")
        self._key_owner = ledger.register("comma-action-keys", "action_interning")
        self._nodes: LedgerList[_Action] = ledger.make_list(
            self._owner, append_only=False
        )
        self._snapshot_owner = ledger.register(
            "comma-action-snapshots", "action_publication_seal"
        )
        self._snapshots: LedgerList[tuple[object, ...]] = ledger.make_list(
            self._snapshot_owner, nodes_per_entry=0, append_only=False
        )
        self._keys: LedgerDict[tuple[object, ...], CommaActionID] = ledger.make_dict(
            self._key_owner
        )
        self._boundary_owner = ledger.register(
            "comma-boundary-templates", "boundary_template"
        )
        self._boundary_templates: LedgerDict[BoundaryState, MacroTemplate] = (
            ledger.make_dict(self._boundary_owner)
        )
        self._boundary_seal_owner = ledger.register(
            "comma-boundary-template-seals", "boundary_publication_seal"
        )
        self._boundary_seals: LedgerDict[BoundaryState, tuple[object, ...]] = (
            ledger.make_dict(self._boundary_seal_owner, nodes_per_entry=1)
        )
        self._boundary_seal_node_owner = ledger.register(
            "comma-boundary-seal-components", "boundary_publication_seal_component"
        )
        self._boundary_seal_nodes: LedgerList[object] = ledger.make_list(
            self._boundary_seal_node_owner, append_only=False
        )
        self._boundary_node_owner = ledger.register(
            "comma-boundary-template-nodes", "boundary_template_node"
        )
        self._boundary_nodes: LedgerList[object] = ledger.make_list(
            self._boundary_node_owner, append_only=False
        )
        self.ledger.bump("comma_transfer_phase_terms", 0)
        self.ledger.bump("comma_cycle_rule_evaluations", 0)
        self.ledger.bump("comma_evaluated_transitions", 0)
        self.identity = self._intern(("identity",), _Action("identity", 0))
        self.cycle_reuse = CycleActionReuse(
            ledger, self.charge, self.charge_bits, shared=shared_cache
        )

    def charge(self, amount: int = 1) -> None:
        used = self.ledger.counters.get("comma_work", 0) + self.ledger.counters.get(
            "comma_certificate_work", 0
        )
        if amount > self.max_work - used:
            self.ledger.bump("comma_budget_refusals")
            raise ValueError("comma construction exceeds --max-comma-work")
        self.ledger.bump("comma_work", amount)

    def charge_bits(self, bits: int) -> None:
        self.ledger.bump("comma_operand_bit_work", bits)

    def _intern(self, key: tuple[object, ...], node: _Action) -> CommaActionID:
        self.ledger.bump("comma_action_requests")
        old = self._keys.get(key)
        if old is not None:
            existing = self.node(old)
            requested_snapshot = _action_snapshot(node)
            existing_snapshot = _action_snapshot(existing)
            # Complete cycles may arrive through either direct construction or
            # chronological squaring. Their decomposition children are a
            # construction route, not part of the normalized extensional
            # action. Every other action retains its full binding.
            if node.kind == existing.kind == "cycle":
                requested_snapshot = requested_snapshot[:-2]
                existing_snapshot = existing_snapshot[:-2]
            if requested_snapshot != existing_snapshot:
                raise ValueError("comma action key aliases a different effect")
            self.charge()
            self.charge_bits(max(1, node.steps.bit_length()))
            self.ledger.bump("comma_action_hits")
            return old
        self.ledger.bump("comma_action_misses")
        self.charge()
        self.charge_bits(
            max(1, node.steps.bit_length())
            + max(1, node.displacement.bit_length())
            + max(1, node.maximum_guard.bit_length())
        )
        self.ledger.reserve_many(
            (
                (self._owner, 1, 1),
                (self._key_owner, 1, 0),
                (self._snapshot_owner, 1, 0),
            )
        )
        try:
            identifier = CommaActionID(self.token, self.kind, len(self._nodes))
            self._nodes.append(node)
            self._snapshots.append(_action_snapshot(node))
            self._keys[key] = identifier
        except BaseException:
            self._keys.pop(key, None)
            if len(self._snapshots) > len(self._nodes):
                self._snapshots.pop()
            if len(self._nodes) and self._nodes[-1] is node:
                self._nodes.pop()
            if len(self._snapshots) > len(self._nodes):
                self._snapshots.pop()
            self.ledger.release(self._owner, entries=1, nodes=1)
            self.ledger.release(self._key_owner, entries=1)
            self.ledger.release(self._snapshot_owner, entries=1)
            raise
        self.ledger.bump("comma_action_publications")
        return identifier

    def node(self, identifier: CommaActionID) -> _Action:
        if type(identifier) is not CommaActionID:
            raise TypeError("expected a scoped comma action")
        identifier.validate(self.token, self.kind, size=len(self._nodes))
        if len(self._snapshots) != len(self._nodes):
            raise ValueError("comma action publication lost its seal")
        node = self._nodes[identifier.local_id]
        if _action_snapshot(node) != self._snapshots[identifier.local_id]:
            raise ValueError("comma action publication was altered")
        return node

    def step(self, child_digit: int) -> CommaActionID:
        if type(child_digit) is not int or not 1 <= child_digit <= 9:
            raise ValueError("comma child digit must be 1 through 9")
        return self._intern(
            ("step", child_digit), _Action("step", 1, child_digit=child_digit)
        )

    def transfer(self, leading: int, digit: int) -> CycleTransfer:
        """Charge the canonical closed-form cyclotomic phase transfer."""
        self.charge(5)
        transfer = cycle_transfer(leading, digit)
        self.charge_bits(5 * 128)
        self.ledger.bump("comma_transfer_constructions")
        self.ledger.bump("comma_cycle_rule_evaluations")
        return transfer

    def one_cycle(self, leading: int, digit: int) -> CommaActionID:
        # cycle_request checks the complete local parent before deriving the
        # transfer and then consults the process cache on a local miss.
        return self.cycle_request(leading, digit, 1)[0]

    def phase_prefix(self, leading: int, digit: int, steps: int) -> CommaActionID:
        """An incomplete physical phase orbit, with its strict interior guard.

        Port dwell weights count diagonal rows. They never supply ``steps``:
        the source classifier recovers the physical phase before admission.
        """
        transfer = self.transfer(leading, digit)
        if type(steps) is not int or not 0 < steps < transfer.period:
            raise ValueError("comma phase prefix must be a positive partial orbit")
        self.charge(steps + 2)
        self.charge_bits(32 * steps)
        displacement = phase_prefix_displacement(leading, digit, steps)
        return self._intern(
            ("phase-prefix", leading, digit, steps),
            _Action(
                "phase-prefix",
                steps,
                leading=leading,
                entering_digit=digit,
                displacement=displacement,
                maximum_guard=displacement + int(leading < 9),
            ),
        )

    def compose(self, before: CommaActionID, after: CommaActionID) -> CommaActionID:
        self.charge()
        left, right = self.node(before), self.node(after)
        if left.kind == "identity":
            return after
        if right.kind == "identity":
            return before
        self.charge_bits(left.steps.bit_length() + right.steps.bit_length())
        if (
            left.kind == right.kind == "cycle"
            and left.leading == right.leading
            and left.entering_digit == right.entering_digit
        ):
            # Cycle count addition and the two additions / minimum comparison
            # in PrefixSafety.then use both source operands, not just the
            # normalized descriptor subsequently passed to the interner.
            self.charge(4)
            self.charge_bits(
                left.cycles.bit_length()
                + right.cycles.bit_length()
                + 2 * left.displacement.bit_length()
                + right.displacement.bit_length()
                + right.maximum_guard.bit_length()
                + left.maximum_guard.bit_length()
                + max(left.displacement.bit_length(), right.maximum_guard.bit_length())
                + 1
            )
            cycles = left.cycles + right.cycles
            safety = PrefixSafety(-left.displacement, -left.maximum_guard).then(
                PrefixSafety(-right.displacement, -right.maximum_guard)
            )
            return self._intern(
                ("cycle", left.leading, left.entering_digit, cycles),
                _Action(
                    "cycle",
                    left.steps + right.steps,
                    left.leading,
                    left.entering_digit,
                    cycles,
                    -safety.delta,
                    -safety.minimum,
                    before=before,
                    after=after,
                ),
            )
        # Mixed effects retain chronological children. Equal durations alone
        # do not imply equal future output or admission at a seam.
        return self._intern(
            ("sequence", before, after),
            _Action(
                "sequence",
                left.steps + right.steps,
                before=before,
                after=after,
            ),
        )

    def cycles(self, leading: int, digit: int, count: int) -> CommaActionID:
        return self.cycle_request(leading, digit, count)[0]

    def cycle_request(
        self, leading: int, digit: int, count: int
    ) -> tuple[CommaActionID, bool]:
        """Read a complete parent before constructing its arithmetic payload.

        The Boolean reports retrieval only. The CLI records an applied hit
        after the scheduler admits and publishes the receiving occurrence.
        """
        reuse = self.cycle_reuse
        reuse.request(leading, digit, count)
        # A complete phase orbit visits every digit in one gcd coset. Its
        # displacement and strict guard therefore depend on the coset, not on
        # the particular entering digit. Keep the canonical coset in the
        # semantic action ID; the receiving occurrence still proves that it
        # belongs to this input domain before application.
        phase = digit % gcd(leading, 10)
        key = ("cycle", leading, phase, count)
        old = self._keys.get(key)
        if old is not None:
            try:
                self.node(old)
            except Exception:
                reuse.count("admission_rejections")
                raise
            reuse.count("local_hits")
            reuse.count("exact_hits")
            return old, True
        (steps, displacement, guard), hit = reuse.resolve(leading, digit, count)
        return self._intern(
            key,
            _Action("cycle", steps, leading, phase, count, displacement, guard),
        ), hit

    def _boundary_template(self, state: BoundaryState) -> MacroTemplate:
        """Retain one complete constructor result per exact quotient state.

        This private arithmetic path is not an infinite-branch admission.
        Its use at translated exponents awaits the checked lifting theorem.
        """
        if type(state) is not BoundaryState:
            raise TypeError("comma boundary state must be exact")
        found = self._boundary_templates.get(state)
        if found is not None:
            self.charge()
            self.ledger.bump("comma_boundary_seal_checks")
            seal = self._boundary_seals.get(state)
            header = _template_header(found)
            self.charge_bits(
                _seal_integer_bits(header)
                + (0 if seal is None else _seal_integer_bits(seal[0]))
            )
            if seal is None or header != seal[0]:
                raise ValueError("comma boundary template publication was altered")
            self.ledger.bump("comma_boundary_template_hits")
            return found
        self.ledger.bump("comma_boundary_template_misses")
        template = construct_macro(
            state, charge=self.charge, charge_bits=self.charge_bits
        )
        components: tuple[object, ...] = (
            template,
            *template.sector_fragments,
            *template.prefix_weights,
            *template.prefix_displacements,
        )
        retained = len(components)
        self.charge(retained)
        self.charge_bits(
            retained
            * max(
                1,
                4
                * (
                    (
                        state.exponent_residue
                        if state.exponent_residue >= 5
                        else state.exponent_residue + PERIOD
                    )
                    + template.exponent_delta
                    + 1
                ),
                template.weight.numerator_scale.bit_length(),
                template.weight.numerator_offset.bit_length(),
                template.endpoint.numerator_scale.bit_length(),
                template.endpoint.numerator_offset.bit_length(),
            )
        )
        self.charge(retained)
        seal_node_count = retained - 1
        self.ledger.reserve_many(
            (
                (self._boundary_owner, 1, 0),
                (self._boundary_seal_owner, 1, 1),
                (self._boundary_seal_node_owner, seal_node_count, seal_node_count),
                (self._boundary_node_owner, retained, retained),
            )
        )
        first_node = len(self._boundary_nodes)
        first_seal_node = len(self._boundary_seal_nodes)
        try:
            seal = _template_seal(template)
            seal_nodes = (
                *cast(tuple[object, ...], seal[1]),
                *cast(tuple[object, ...], seal[2]),
                *cast(tuple[object, ...], seal[3]),
            )
            if len(seal_nodes) != seal_node_count:
                raise ValueError("comma boundary seal has another component count")
            seal_integer_bits = _seal_integer_bits(seal)
            self.charge_bits(seal_integer_bits)
            self._boundary_nodes.extend(components)
            self._boundary_seal_nodes.extend(seal_nodes)
            self._boundary_templates[state] = template
            self._boundary_seals[state] = seal
        except BaseException:
            if len(self._boundary_nodes) > first_node:
                del self._boundary_nodes[first_node:]
            if len(self._boundary_seal_nodes) > first_seal_node:
                del self._boundary_seal_nodes[first_seal_node:]
            self._boundary_templates.pop(state, None)
            self._boundary_seals.pop(state, None)
            self.ledger.release(self._boundary_owner, entries=1)
            self.ledger.release(self._boundary_seal_owner, entries=1, nodes=1)
            self.ledger.release(
                self._boundary_seal_node_owner,
                entries=seal_node_count,
                nodes=seal_node_count,
            )
            self.ledger.release(
                self._boundary_node_owner, entries=retained, nodes=retained
            )
            raise
        self.ledger.bump("comma_boundary_template_publications")
        self.ledger.bump("comma_boundary_template_retained_nodes", retained)
        self.ledger.bump("comma_boundary_seal_retained_slots", seal_node_count + 1)
        self.ledger.bump("comma_boundary_seal_retained_integer_bits", seal_integer_bits)
        return template

    def _boundary_read_guard(
        self, state: BoundaryState, template: MacroTemplate
    ) -> Callable[[str, int], None]:
        self.charge()
        self.ledger.bump("comma_boundary_seal_checks")
        seal = self._boundary_seals.get(state)
        header = _template_header(template)
        self.charge_bits(
            _seal_integer_bits(header)
            + (0 if seal is None else _seal_integer_bits(seal[0]))
        )
        if seal is None or header != seal[0]:
            raise ValueError("comma boundary template publication was altered")

        def verify(kind: str, index: int) -> None:
            self.charge()
            self.ledger.bump("comma_boundary_seal_checks")
            if kind == "fragment":
                current = _fragment_snapshot(template.sector_fragments[index])
                expected = cast(tuple[object, ...], seal[1])[index]
            elif kind == "weight":
                current = _affine_snapshot(template.prefix_weights[index])
                expected = cast(tuple[object, ...], seal[2])[index]
            elif kind == "displacement":
                current = _affine_snapshot(template.prefix_displacements[index])
                expected = cast(tuple[object, ...], seal[3])[index]
            else:
                raise ValueError("unknown comma boundary component")
            self.charge_bits(_seal_integer_bits(current) + _seal_integer_bits(expected))
            if current != expected:
                raise ValueError("comma boundary template publication was altered")

        return verify

    def _boundary_prefix(
        self, state: BoundaryState, exponent: int, transitions: int
    ) -> CommaActionID:
        """Construct an exact-source prefix ending no later than the fork.

        The representative exponent is the sole currently admitted input for
        this unproved symbolic constructor.  A checked whole-ray contract must
        be installed before this method can transport to other exponents.
        """
        if type(state) is not BoundaryState:
            raise TypeError("comma boundary state must be exact")
        representative = state.exponent_residue
        if representative < 5:
            representative += PERIOD
        if type(exponent) is not int or exponent != representative:
            raise ValueError("comma boundary lifting is not yet admitted")
        if type(transitions) is not int or transitions < 0:
            raise ValueError("comma boundary prefix length must be nonnegative")
        template = self._boundary_template(state)
        if transitions > template.weight.evaluate(
            exponent, charge_bits=self.charge_bits
        ):
            raise ValueError("comma boundary prefix crosses its next branch")
        return self._intern(
            ("boundary-prefix", state, exponent, transitions),
            _Action(
                "boundary-prefix",
                transitions,
                boundary_source=state,
                boundary_exponent=exponent,
            ),
        )
