"""Ledger-owned comma actions and authenticated boundary templates.

These records describe admitted actions; the source-image adapter remains the sole
scheduler consumer. Boundary macros carry exact arithmetic but no branch authority.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator, Mapping, Sequence
from dataclasses import dataclass
from math import gcd
from typing import cast

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.fields.consumer_pullback import PrefixSafety
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import comma as _comma_keys
from number_compiler.resources.stores import LedgerDict, LedgerList
from number_compiler.sequences.comma.arithmetic import (
    CycleTransfer,
    cycle_transfer,
    phase_prefix_displacement,
)
from number_compiler.sequences.comma.boundary_quotient import (
    PERIOD,
    BoundaryState,
    MacroTemplate,
    boundary_state_signature,
    construct_macro,
    macro_template_retained_components,
)
from number_compiler.sequences.comma.boundary_quotient import (
    macro_template_component_seal as _template_seal,
)
from number_compiler.sequences.comma.boundary_quotient import (
    macro_template_header as _template_header,
)
from number_compiler.sequences.comma.cycle_actions import CycleActionReuse
from number_compiler.sequences.comma.occurrence import BoundaryOccurrence


@dataclass(frozen=True, slots=True)
class CommaActionID(ArenaHandle):
    pass


@dataclass(frozen=True, slots=True)
class CommaActionRecord:
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
    boundary_target: BoundaryState | None = None
    future_digest: str = ""
    before: CommaActionID | None = None
    after: CommaActionID | None = None


@dataclass(frozen=True, slots=True)
class CommaActionArenaAuditSnapshot:
    """Read-only stores and ledger identities for comma payload verification."""

    ledger: ResourceLedger
    token: ArenaToken
    kind: str
    owner: int
    key_owner: int
    snapshot_owner: int
    boundary_owner: int
    boundary_seal_owner: int
    boundary_seal_node_owner: int
    boundary_node_owner: int
    nodes: Sequence[CommaActionRecord]
    snapshots: Sequence[tuple[object, ...]]
    keys: Mapping[tuple[object, ...], CommaActionID]
    boundary_templates: Mapping[BoundaryState, MacroTemplate]
    boundary_seals: Mapping[BoundaryState, tuple[object, ...]]
    boundary_seal_nodes: Sequence[object]
    boundary_nodes: Sequence[object]


def action_snapshot(node: CommaActionRecord) -> tuple[object, ...]:
    """Keep primitive fields separate from mutable private record identities."""

    def handle(value: CommaActionID | None) -> tuple[object, str, int] | None:
        if value is None:
            return None
        return value.owner, value.kind, value.local_id

    state = node.boundary_source
    boundary = None if state is None else (state.kind, state.a, state.exponent_residue)
    target = node.boundary_target
    target_signature = (
        None if target is None else (target.kind, target.a, target.exponent_residue)
    )
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
        target_signature,
        node.future_digest,
        handle(node.before),
        handle(node.after),
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
        elif is_exact_object_tuple(item):
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
        self._nodes: LedgerList[CommaActionRecord] = ledger.make_list(
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
        self.ledger.bump(_comma_keys.COMMA_TRANSFER_PHASE_TERMS, 0)
        self.ledger.bump(_comma_keys.COMMA_CYCLE_RULE_EVALUATIONS, 0)
        self.ledger.bump(_comma_keys.COMMA_EVALUATED_TRANSITIONS, 0)
        self.identity = self.intern_record(
            ("identity",), CommaActionRecord("identity", 0)
        )
        self.cycle_reuse = CycleActionReuse(
            ledger, self.charge, self.charge_bits, shared=shared_cache
        )

    def charge(self, amount: int = 1) -> None:
        used = self.ledger.counters.get(
            _comma_keys.COMMA_WORK, 0
        ) + self.ledger.counters.get(_comma_keys.COMMA_CERTIFICATE_WORK, 0)
        if amount > self.max_work - used:
            self.ledger.bump(_comma_keys.COMMA_BUDGET_REFUSALS)
            raise ValueError("comma construction exceeds --max-comma-work")
        self.ledger.bump(_comma_keys.COMMA_WORK, amount)

    def charge_bits(self, bits: int) -> None:
        self.ledger.bump(_comma_keys.COMMA_OPERAND_BIT_WORK, bits)

    def intern_record(
        self, key: tuple[object, ...], node: CommaActionRecord
    ) -> CommaActionID:
        self.ledger.bump(_comma_keys.COMMA_ACTION_REQUESTS)
        old = self._keys.get(key)
        if old is not None:
            existing = self.node(old)
            requested_snapshot = action_snapshot(node)
            existing_snapshot = action_snapshot(existing)
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
            self.ledger.bump(_comma_keys.COMMA_ACTION_HITS)
            return old
        self.ledger.bump(_comma_keys.COMMA_ACTION_MISSES)
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
            self._snapshots.append(action_snapshot(node))
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
        self.ledger.bump(_comma_keys.COMMA_ACTION_PUBLICATIONS)
        return identifier

    def node(self, identifier: CommaActionID) -> CommaActionRecord:
        if type(identifier) is not CommaActionID:
            raise TypeError("expected a scoped comma action")
        identifier.validate(self.token, self.kind, size=len(self._nodes))
        if len(self._snapshots) != len(self._nodes):
            raise ValueError("comma action publication lost its seal")
        node = self._nodes[identifier.local_id]
        if action_snapshot(node) != self._snapshots[identifier.local_id]:
            raise ValueError("comma action publication was altered")
        return node

    def audit_snapshot(self) -> CommaActionArenaAuditSnapshot:
        """Expose retained action stores through immutable read-only views."""
        return CommaActionArenaAuditSnapshot(
            ledger=self.ledger,
            token=self.token,
            kind=self.kind,
            owner=self._owner,
            key_owner=self._key_owner,
            snapshot_owner=self._snapshot_owner,
            boundary_owner=self._boundary_owner,
            boundary_seal_owner=self._boundary_seal_owner,
            boundary_seal_node_owner=self._boundary_seal_node_owner,
            boundary_node_owner=self._boundary_node_owner,
            nodes=self._nodes.audit_view(),
            snapshots=self._snapshots.audit_view(),
            keys=self._keys.audit_view(),
            boundary_templates=self._boundary_templates.audit_view(),
            boundary_seals=self._boundary_seals.audit_view(),
            boundary_seal_nodes=self._boundary_seal_nodes.audit_view(),
            boundary_nodes=self._boundary_nodes.audit_view(),
        )

    def bind_payload_audit_root(self, root: object) -> None:
        """Bind exact owned stores to the corresponding term audit root."""
        from number_compiler.sequences.comma.power import CommaTerm

        if type(root) is not CommaTerm or root.arena is not self:
            raise TypeError("comma audit stores require their exact owning term")
        for attribute, store in (
            ("_audit_action_nodes", self._nodes),
            ("_audit_action_keys", self._keys),
            ("_audit_action_snapshots", self._snapshots),
            ("_audit_boundary_templates", self._boundary_templates),
            ("_audit_boundary_seals", self._boundary_seals),
            ("_audit_boundary_seal_nodes", self._boundary_seal_nodes),
            ("_audit_boundary_nodes", self._boundary_nodes),
        ):
            setattr(root, attribute, store)

    def payload_audit_root_is_bound(self, root: object) -> bool:
        """Check exact root-to-store aliases without exporting writable stores."""
        from number_compiler.sequences.comma.power import CommaTerm

        if type(root) is not CommaTerm or root.arena is not self:
            return False
        return all(
            getattr(root, attribute, None) is store
            for attribute, store in (
                ("_audit_action_nodes", self._nodes),
                ("_audit_action_keys", self._keys),
                ("_audit_action_snapshots", self._snapshots),
                ("_audit_boundary_templates", self._boundary_templates),
                ("_audit_boundary_seals", self._boundary_seals),
                ("_audit_boundary_seal_nodes", self._boundary_seal_nodes),
                ("_audit_boundary_nodes", self._boundary_nodes),
            )
        )

    def step(self, child_digit: int) -> CommaActionID:
        if type(child_digit) is not int or not 1 <= child_digit <= 9:
            raise ValueError("comma child digit must be 1 through 9")
        return self.intern_record(
            ("step", child_digit), CommaActionRecord("step", 1, child_digit=child_digit)
        )

    def transfer(self, leading: int, digit: int) -> CycleTransfer:
        """Charge the canonical closed-form cyclotomic phase transfer."""
        self.charge(5)
        transfer = cycle_transfer(leading, digit)
        self.charge_bits(5 * 128)
        self.ledger.bump(_comma_keys.COMMA_TRANSFER_CONSTRUCTIONS)
        self.ledger.bump(_comma_keys.COMMA_CYCLE_RULE_EVALUATIONS)
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
        return self.intern_record(
            ("phase-prefix", leading, digit, steps),
            CommaActionRecord(
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
        if (
            left.kind == right.kind == "boundary-prefix-occurrence"
            and left.boundary_source == right.boundary_source
        ):
            self.charge_bits(
                left.steps.bit_length()
                + right.steps.bit_length()
                + max(left.steps, right.steps).bit_length()
            )
            return self._boundary_prefix_occurrence_steps(
                cast(BoundaryState, left.boundary_source),
                left.steps + right.steps,
            )
        occurrence_actions = {
            "boundary-prefix-occurrence",
            "global-boundary-return",
            "source20-first-child",
        }
        if left.kind in occurrence_actions or right.kind in occurrence_actions:
            raise ValueError(
                "occurrence-bound comma returns are applied as complete actions"
            )
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
            return self.intern_record(
                ("cycle", left.leading, left.entering_digit, cycles),
                CommaActionRecord(
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
        return self.intern_record(
            ("sequence", before, after),
            CommaActionRecord(
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
        return self.intern_record(
            key,
            CommaActionRecord(
                "cycle", steps, leading, phase, count, displacement, guard
            ),
        ), hit

    def boundary_template(self, state: BoundaryState) -> MacroTemplate:
        """Retain one complete constructor result per exact quotient state.

        This private arithmetic path is not an infinite-branch admission.
        Its use at translated exponents awaits the checked lifting theorem.
        """
        if type(state) is not BoundaryState:
            raise TypeError("comma boundary state must be exact")
        boundary_state_signature(state)
        found = self._boundary_templates.get(state)
        if found is not None:
            self.charge()
            self.ledger.bump(_comma_keys.COMMA_BOUNDARY_SEAL_CHECKS)
            seal = self._boundary_seals.get(state)
            header = _template_header(found)
            self.charge_bits(
                _seal_integer_bits(header)
                + (0 if seal is None else _seal_integer_bits(seal[0]))
            )
            if seal is None or not found.owns_component_seal(seal) or header != seal[0]:
                raise ValueError(
                    "comma boundary template publication was altered "
                    "(snapshot mismatch)"
                )
            self.ledger.bump(_comma_keys.COMMA_BOUNDARY_TEMPLATE_HITS)
            return found
        self.ledger.bump(_comma_keys.COMMA_BOUNDARY_TEMPLATE_MISSES)
        template = construct_macro(
            state, charge=self.charge, charge_bits=self.charge_bits
        )
        # Charge graph inspection before allocating its flattened owner list.
        # Each segment contributes its wrapper and four retained children;
        # adjacent edges may share child identities, but still require reading
        # each reference before the later identity de-duplication.
        self.charge(
            2
            + len(template.sector_fragments)
            + len(template.prefix_weights)
            + len(template.prefix_displacements)
            + 5 * len(template.chart_segments)
        )
        components = macro_template_retained_components(template)
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
        seal_node_count = (
            len(template.sector_fragments)
            + len(template.prefix_weights)
            + len(template.prefix_displacements)
            + len(template.chart_segments)
        )
        self.charge(seal_node_count + 1)
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
                *cast(tuple[object, ...], seal[4]),
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
        self.ledger.bump(_comma_keys.COMMA_BOUNDARY_TEMPLATE_PUBLICATIONS)
        self.ledger.bump(_comma_keys.COMMA_BOUNDARY_TEMPLATE_RETAINED_NODES, retained)
        self.ledger.bump(
            _comma_keys.COMMA_BOUNDARY_SEAL_RETAINED_SLOTS, seal_node_count + 1
        )
        self.ledger.bump(
            _comma_keys.COMMA_BOUNDARY_SEAL_RETAINED_INTEGER_BITS, seal_integer_bits
        )
        return template

    def boundary_read_guard(
        self, state: BoundaryState, template: MacroTemplate
    ) -> Callable[[str, int], None]:
        self.charge()
        self.ledger.bump(_comma_keys.COMMA_BOUNDARY_SEAL_CHECKS)
        seal = self._boundary_seals.get(state)
        header = _template_header(template)
        self.charge_bits(
            _seal_integer_bits(header)
            + (0 if seal is None else _seal_integer_bits(seal[0]))
        )
        if seal is None or not template.owns_component_seal(seal) or header != seal[0]:
            raise ValueError(
                "comma boundary template publication was altered (snapshot mismatch)"
            )

        def verify(kind: str, index: int) -> None:
            self.charge()
            self.ledger.bump(_comma_keys.COMMA_BOUNDARY_SEAL_CHECKS)
            if kind == "fragment":
                expected = cast(tuple[object, ...], seal[1])[index]
            elif kind == "weight":
                expected = cast(tuple[object, ...], seal[2])[index]
            elif kind == "displacement":
                expected = cast(tuple[object, ...], seal[3])[index]
            elif kind == "chart_segment":
                expected = cast(tuple[object, ...], seal[4])[index]
            else:
                raise ValueError("unknown comma boundary component")
            self.charge_bits(_seal_integer_bits(expected))

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
        boundary_state_signature(state)
        representative = state.exponent_residue
        if representative < 5:
            representative += PERIOD
        if type(exponent) is not int or exponent != representative:
            raise ValueError("comma boundary lifting is not yet admitted")
        if type(transitions) is not int or transitions < 0:
            raise ValueError("comma boundary prefix length must be nonnegative")
        template = self.boundary_template(state)
        if transitions > template.weight.evaluate(
            exponent, charge_bits=self.charge_bits
        ):
            raise ValueError("comma boundary prefix crosses its next branch")
        return self.intern_record(
            ("boundary-prefix", state, exponent, transitions),
            CommaActionRecord(
                "boundary-prefix",
                transitions,
                boundary_source=state,
                boundary_exponent=exponent,
            ),
        )

    def boundary_prefix_occurrence(
        self, source: BoundaryOccurrence, transitions: int
    ) -> CommaActionID:
        """Build a receiver-bound prefix action with no exponent in its ID.

        This is an internal application path. The public comma constructor
        remains gated on its certified prefix until the all-exponent
        constructor refinement is accepted. At application time the source
        image must reconstruct this exact boundary occurrence from its value;
        the exponent is therefore occurrence context, never action identity.
        """
        if type(source) is not BoundaryOccurrence:
            raise TypeError("comma boundary prefix needs an exact occurrence")
        source.validate()
        if type(transitions) is not int or transitions < 0:
            raise ValueError("comma boundary prefix length must be nonnegative")
        template = self.boundary_template(source.state)
        total = template.weight.evaluate(source.exponent, charge_bits=self.charge_bits)
        if transitions > total:
            raise ValueError("comma boundary prefix crosses its next branch")
        return self._boundary_prefix_occurrence_steps(source.state, transitions)

    def _boundary_prefix_occurrence_steps(
        self, state: BoundaryState, transitions: int
    ) -> CommaActionID:
        """Intern the normalized cumulative prefix used by a returned image.

        This constructor deliberately has no receiving exponent. The admitted
        source image validates the complete cumulative prefix when it is
        applied, so composition can remain independent of occurrence geometry.
        """
        if type(state) is not BoundaryState:
            raise TypeError("comma boundary prefix state must be exact")
        boundary_state_signature(state)
        if type(transitions) is not int or transitions < 0:
            raise ValueError("comma boundary prefix length must be nonnegative")
        return self.intern_record(
            ("boundary-prefix-occurrence", state, transitions),
            CommaActionRecord(
                "boundary-prefix-occurrence",
                transitions,
                boundary_source=state,
            ),
        )

    def global_boundary_return(
        self,
        source: BoundaryState,
        artifact_sha256: str,
    ) -> CommaActionID:
        """Intern one source-guarded return under its admitted provider.

        The selected target belongs to the application result, not the
        reusable action identity. The immutable artifact and source state
        determine its guarded outcome.
        """
        if type(source) is not BoundaryState:
            raise TypeError("comma future return needs an exact boundary source")
        boundary_state_signature(source)
        from number_compiler.sequences.comma.future_authority import (
            valid_artifact_digest,
        )

        if not valid_artifact_digest(artifact_sha256):
            raise ValueError("comma future return needs an admitted artifact digest")
        template = self.boundary_template(source)
        if template.outcome != "fork":
            raise ValueError("comma future return source is not a macro fork")
        key = ("global-boundary-return", source, artifact_sha256)
        return self.intern_record(
            key,
            CommaActionRecord(
                "global-boundary-return",
                0,
                boundary_source=source,
                future_digest=artifact_sha256,
            ),
        )

    def source20_first_child(self, artifact_sha256: str) -> CommaActionID:
        """Intern the exact root-20 first edge under the global theorem."""
        from number_compiler.sequences.comma.future_authority import (
            valid_artifact_digest,
        )

        if not valid_artifact_digest(artifact_sha256):
            raise ValueError("comma source-20 action needs an admitted artifact digest")
        return self.intern_record(
            ("source20-first-child", artifact_sha256),
            CommaActionRecord("source20-first-child", 1, future_digest=artifact_sha256),
        )
