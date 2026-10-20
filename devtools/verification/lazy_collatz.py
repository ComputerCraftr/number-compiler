"""Collatz projection through symbolic programs and bounded carry streams.

Only the original source contains digits.  Programs contain operation IDs and
shift counts; summaries contain carry states and coordinate witnesses.  The
stream evaluator deliberately does not memoize emitted intermediate bits.
"""

from __future__ import annotations

from collections.abc import Iterator, Mapping, MutableMapping, MutableSequence, Sequence
from dataclasses import dataclass
from enum import IntEnum
from types import MappingProxyType
from typing import TYPE_CHECKING

from devtools.verification.collatz_carry_ranges import (
    CarryRangeSummary as _CarryRangeSummary,
)
from devtools.verification.collatz_carry_ranges import (
    CarryRangeTransfer as _CarryRangeTransfer,
)
from devtools.verification.lazy_collatz_metrics import collect_lazy_collatz_metrics
from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    ArenaToken,
    ExactSource,
    LoweringCapability,
)
from number_compiler.arithmetic.fields.dyadic_tile import (
    DyadicSpan,
)
from number_compiler.arithmetic.fields.dyadic_tile import (
    source_span as dyadic_source_span,
)
from number_compiler.projection.microblock_cache import (
    ExactMicroblock,
    MicroblockCache,
    MicroblockKey,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.proof_payload_admission import (
    register_proof_geometry_fields,
    register_proof_opaque_types,
)

if TYPE_CHECKING:
    from devtools.verification.lazy_collatz_range import CollatzRangeEvaluator
    from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry


@dataclass(frozen=True, slots=True)
class _Program:
    kind: str
    left: int = 0
    right: int = 0
    shift: int = 0

    def __post_init__(self) -> None:
        if self.kind not in ("identity", "compose", "shift", "mul3") or any(
            type(value) is not int or value < 0
            for value in (self.left, self.right, self.shift)
        ):
            raise ValueError("invalid symbolic Collatz program")


Program = _Program


class Mul3Carry(IntEnum):
    ZERO = 0
    ONE = 1
    TWO = 2


@dataclass(slots=True)
class _Mul3Port:
    program: ActionProgramID
    state: Mul3Carry = Mul3Carry.ONE

    def __post_init__(self) -> None:
        if (
            type(self.program) is not ActionProgramID
            or self.program.kind != "program"
            or type(self.state) is not Mul3Carry
        ):
            raise ValueError(
                "mul3 ports require a symbolic program and a finite carry state"
            )

    def advance(self, bit: int, ledger: ResourceLedger) -> int:
        if bit not in (0, 1) or type(self.state) is not Mul3Carry:
            raise ValueError("mul3 ports accept only their finite carry states")
        total = ledger.observe_arithmetic(3 * bit + int(self.state))
        self.state = Mul3Carry(total >> 1)
        return total & 1


Mul3Port = _Mul3Port


@dataclass(slots=True)
class _ShiftPort:
    program: ActionProgramID
    remaining: int

    def __post_init__(self) -> None:
        if (
            type(self.program) is not ActionProgramID
            or self.program.kind != "program"
            or type(self.remaining) is not int
            or self.remaining < 0
        ):
            raise ValueError("shift ports require a symbolic program and coordinate")


ShiftPort = _ShiftPort


@dataclass(frozen=True, slots=True)
class _SummaryKey:
    program: ActionProgramID
    width: int


SummaryKey = _SummaryKey


@dataclass(frozen=True, slots=True)
class _SourceRangeKey:
    width: int


SourceRangeKey = _SourceRangeKey


@dataclass(frozen=True, slots=True)
class _ResultKey:
    kind: str
    steps: int


ResultKey = _ResultKey


@dataclass(frozen=True, slots=True)
class _ExactProgramWidth:
    """Typed geometry metadata for one source-bound symbolic program."""

    program: ActionProgramID
    width: int

    def __post_init__(self) -> None:
        if (
            type(self.program) is not ActionProgramID
            or self.program.kind != "program"
            or type(self.width) is not int
            or self.width <= 0
        ):
            raise ValueError("invalid exact Collatz program extent")


@dataclass(frozen=True, slots=True)
class CollatzLazyView:
    """An original source under a symbolic action; width is geometry."""

    source: ArenaHandle
    program: ActionProgramID
    width: int
    exact_width: bool = True


@dataclass(frozen=True, slots=True)
class LazyCollatzPayloadAuditSnapshot:
    """Read-only view of stores and values needed by the independent payload audit."""

    token: ArenaToken
    source_ref: ArenaHandle
    initial: CollatzLazyView
    programs: tuple[Program, ...]
    program_owner: int
    program_store: object
    program_key_owner: int
    program_key_store: object
    summary_owner: int
    summary_store: object
    summary_payloads: Mapping[SummaryKey, _CarryRangeSummary]
    mul3_owner: int
    mul3_store: object
    mul3_payloads: Mapping[SummaryKey, object]


@dataclass(frozen=True, slots=True)
class LazyCollatzResult:
    view: CollatzLazyView
    # Only complete accelerated events are included in this event schedule.
    valuations: tuple[int, ...]
    repeated_twos: int = 0
    initial_shift: int = 0
    partial_ticks: int = 0

    @property
    def events(self) -> int:
        return len(self.valuations) + self.repeated_twos

    @property
    def shift(self) -> int:
        return sum(self.valuations) + 2 * self.repeated_twos

    @property
    def odd_ticks(self) -> int:
        return self.events + int(self.partial_ticks > 0)


class LazyCollatzApplication:
    """An index-owned exact lazy Collatz application.

    Branch discovery can be linear in the requested event count.  Evaluation
    uses a pipeline of finite carry machines, never an expanded affine offset
    or arbitrary-precision prefix.  Repeated fixed-point events are certified
    from a width/point query and need no expanded pipeline.
    """

    def __init__(
        self,
        blank: int,
        steps: int,
        source: Sequence[int],
        ledger: ResourceLedger | None = None,
        source_geometry: SourceGeometry | None = None,
    ) -> None:
        if type(blank) is not int or type(steps) is not int or steps < 0:
            raise ValueError(steps)
        digits = tuple(source)
        if (
            not digits
            or any(type(bit) is not int or bit not in (0, 1) for bit in digits)
            or not any(digits)
        ):
            raise ValueError("Collatz requires a nonzero binary source")
        self.blank, self.steps = int(blank), int(steps)
        self.source_geometry = source_geometry
        self.ledger = (
            (
                source_geometry.ledger
                if source_geometry is not None
                else ResourceLedger()
            )
            if ledger is None
            else ledger
        )
        if source_geometry is not None:
            from number_compiler.arithmetic.contracts.source_geometry import (
                SourceGeometry,
            )

            if (
                type(source_geometry) is not SourceGeometry
                or source_geometry.ledger is not self.ledger
            ):
                raise ValueError("Collatz source geometry belongs to another scope")
            source_geometry.require_source(digits, self.blank)
        self.ledger.register_execution_root(self)
        self.token = ArenaToken("lazy-collatz")
        namespace = f"collatz-{len(self.ledger.inventory())}"
        self._program_owner = self.ledger.register(
            namespace + "-programs", "action_program"
        )
        self._program_key_owner = self.ledger.register(
            namespace + "-program-interner", "action_interner"
        )
        self._source_owner = self.ledger.register(namespace + "-source", "exact_source")
        self._summary_owner = self.ledger.register(
            namespace + "-range-summaries", "spatial_binding"
        )
        self._result_owner = self.ledger.register(
            namespace + "-lazy-results", "lazy_field"
        )
        self._transfer_owner = self.ledger.register(
            namespace + "-source-transfers", "spatial_binding"
        )
        self._width_owner = self.ledger.register(
            namespace + "-program-widths",
            "action_construction_metadata",
        )
        mul3_owner = self.ledger.register(
            namespace + "-mul3-summaries", "spatial_binding"
        )
        self.ledger.reserve(self._source_owner, entries=1, nodes=1)
        self.original = ExactSource(digits, 2, orbit="collatz", blank=blank)
        self.ledger.register_container(
            self._source_owner,
            (self.original,),
            node_count=lambda: 1,
            payloads=lambda: (self.original,),
        )
        self._source_ref = ArenaHandle(self.token, "source", 0)
        self.ledger.register_root(self._source_owner, self._source_ref)
        self._programs: MutableSequence[_Program] = self.ledger.make_list(
            self._program_owner
        )
        self._program_ids: MutableMapping[_Program, int] = self.ledger.make_dict(
            self._program_key_owner
        )
        self._summaries: MutableMapping[_SummaryKey, _CarryRangeSummary] = (
            self.ledger.make_dict(self._summary_owner, nodes_per_entry=1)
        )
        self._results: MutableMapping[_ResultKey, LazyCollatzResult] = (
            self.ledger.make_dict(self._result_owner, nodes_per_entry=1)
        )
        self._source_ranges: MutableMapping[_SourceRangeKey, _CarryRangeTransfer] = (
            self.ledger.make_dict(self._transfer_owner, nodes_per_entry=1)
        )
        self._exact_program_widths: MutableMapping[
            ActionProgramID, _ExactProgramWidth
        ] = self.ledger.make_dict(
            self._width_owner,
        )
        self._mul3_summaries: OwnedMemo[_SummaryKey, _CarryRangeTransfer] = OwnedMemo(
            self.ledger,
            mul3_owner,
            nodes_per_entry=1,
            evictable=True,
        )
        self.ledger.register_container(
            self._program_owner,
            self._programs,
            node_count=lambda: len(self._programs),
            payloads=lambda: self._programs,
        )
        self.ledger.register_container(
            self._program_key_owner,
            self._program_ids,
            payloads=lambda: self._program_ids.items(),
            composition_count=lambda: sum(
                node.kind == "compose" for node in self._program_ids
            ),
        )
        self.ledger.register_container(
            self._summary_owner,
            self._summaries,
            node_count=lambda: len(self._summaries),
            payloads=lambda: self._summaries.items(),
            evict=self._evict_summaries,
        )
        self.ledger.register_container(
            self._result_owner,
            self._results,
            node_count=lambda: len(self._results),
            payloads=lambda: self._results.items(),
        )
        self.ledger.register_container(
            self._transfer_owner,
            self._source_ranges,
            node_count=lambda: len(self._source_ranges),
            payloads=lambda: self._source_ranges.items(),
            evict=self._evict_source_ranges,
        )
        identity = self.intern_record(_Program("identity"))
        width = max(i for i, bit in enumerate(digits) if bit) + 1
        self.initial = CollatzLazyView(self._source_ref, identity, width)
        self._set_exact_program_width(identity.local_id, width)
        self.branch_evaluations = 0
        self.carry_cell_evaluations = 0
        self.point_queries = 0
        self.summary_queries = 0
        self.program_compositions = 0
        self.applications = 0
        self.fixed_cycle_skips = 0
        self.maximum_carry = 0
        self.source_transfer_compositions = 0
        from devtools.verification.lazy_collatz_range import CollatzRangeEvaluator

        self._microblocks = MicroblockCache.shared(
            self.ledger,
            self.token,
            self._validate_microblock_program,
        )
        self._range_evaluator = CollatzRangeEvaluator(self)

    def payload_audit_snapshot(self) -> LazyCollatzPayloadAuditSnapshot:
        """Return immutable program metadata and exact stores for forensic audits."""
        memo = self._mul3_summaries.audit_snapshot()
        return LazyCollatzPayloadAuditSnapshot(
            token=self.token,
            source_ref=self._source_ref,
            initial=self.initial,
            programs=tuple(self._programs),
            program_owner=self._program_owner,
            program_store=self._programs,
            program_key_owner=self._program_key_owner,
            program_key_store=self._program_ids,
            summary_owner=self._summary_owner,
            summary_store=self._summaries,
            summary_payloads=MappingProxyType(dict(self._summaries)),
            mul3_owner=memo.owner,
            mul3_store=memo.container,
            mul3_payloads=memo.payload_view,
        )

    def _validate_microblock_program(self, program: ActionProgramID) -> _Program:
        if type(program) is not ActionProgramID:
            raise TypeError("Collatz microblocks require an action-program ID")
        program.validate(self.token, "action-program", size=len(self._programs))
        return self._programs[program.local_id]

    def _microblock_key(
        self,
        program: ActionProgramID,
        block: int,
    ) -> MicroblockKey:
        """Return the cache key for one aligned 64-bit program observation.

        ``LazyCollatzApplication`` predates the public compiler's
        ``action-program`` spelling.  The key is a typed view of the same
        already-validated local program identity, not a second program arena.
        """
        if type(program) is not ActionProgramID:
            raise TypeError("Collatz microblocks require an action-program ID")
        program.validate(self.token, "program", size=len(self._programs))
        if type(block) is not int or block < 0:
            raise ValueError("Collatz microblock index must be nonnegative")
        key_program = ActionProgramID(
            self.token,
            "action-program",
            program.local_id,
        )
        return MicroblockKey(key_program, 2, 0, block, "binary")

    def _source_block(self, block: int) -> int:
        """Read one bounded block from immutable original-source geometry."""
        start = block * 64
        encoded = 0
        geometry = self.source_geometry
        for offset in range(64):
            position = start + offset
            if position >= len(self._source):
                break
            bit = (
                self._source[position] if geometry is None else geometry.read(position)
            )
            encoded |= bit << offset
            self.ledger.bump("collatz_source_reads")
        return encoded

    def program_block(self, program: ActionProgramID, block: int) -> int:
        from devtools.verification.collatz_microblock_projection import (
            program_block as project_program_block,
        )

        return project_program_block(self, program, block)

    def program_bit(self, program: ActionProgramID, position: int) -> int:
        from devtools.verification.collatz_microblock_projection import (
            program_bit as project_program_bit,
        )

        return project_program_bit(self, program, position)

    def program_record(self, program: ActionProgramID) -> Program:
        """Resolve one authenticated immutable program node for an evaluator."""
        if type(program) is not ActionProgramID:
            raise TypeError("Collatz program lookup requires an action-program ID")
        program.validate(self.token, "program", size=len(self._programs))
        return self._programs[program.local_id]

    @property
    def program_count(self) -> int:
        return len(self._programs)

    @property
    def source_width(self) -> int:
        return len(self._source)

    def source_cell(self, position: int) -> int:
        geometry = self.source_geometry
        return self._source[position] if geometry is None else geometry.read(position)

    def source_block(self, block: int) -> int:
        """Read a bounded aligned block from the original source."""
        return self._source_block(block)

    def known_program_width(self, program: ActionProgramID) -> int | None:
        """Return an exact source width when the program has one."""
        return self._known_program_width(program)

    @property
    def range_evaluator(self) -> CollatzRangeEvaluator:
        """Expose the scoped finite range evaluator to sibling projections."""
        return self._range_evaluator

    def append_program(
        self,
        view: CollatzLazyView,
        operation: Program,
        width: int,
        *,
        exact_width: bool | None = None,
    ) -> CollatzLazyView:
        """Append one admitted symbolic operation to an existing lazy view."""
        return self._append(view, operation, width, exact_width=exact_width)

    def cached_microblock(
        self, program: ActionProgramID, block: int
    ) -> ExactMicroblock | None:
        """Read one retained microblock through its canonical program key."""
        return self._microblocks.get(self._microblock_key(program, block))

    def publish_microblock(
        self, program: ActionProgramID, block: int, value: ExactMicroblock
    ) -> None:
        """Publish one computed microblock through its bounded cache."""
        self._microblocks.put(self._microblock_key(program, block), value)

    def finish_program_scan(self, program: ActionProgramID, width: int) -> None:
        """Keep one complete capped stage plus its bounded right halo.

        Physical branch discovery consumes a program from left to right before
        appending its successor.  Older stages are then dead providers: the
        current stage's aligned blocks are the exact input needed by the next
        action.  Releasing them here avoids FIFO churn when a long trajectory
        crosses the global 1,024-block cap.
        """
        if type(width) is not int or width <= 0:
            raise ValueError("a completed Collatz scan requires positive extent")
        if self._known_program_width(program) != width:
            # A caller may ask for a strict prefix of an otherwise longer
            # program.  Such a prefix cannot authorize dead-stage eviction or
            # a zero right halo.
            return
        # Exact width proves the next aligned block is zero.  Publish that
        # bounded halo directly; recomputing it through dead ancestors would
        # turn a capped accelerator back into continuation replay.
        halo_key = self._microblock_key(program, (width + 63) // 64)
        if self._microblocks.get(halo_key) is None:
            self._microblocks.put(halo_key, ExactMicroblock(0, 64))
        for key in tuple(self._microblocks.blocks):
            if (
                key.kind == "binary"
                and key.program.owner is self.token
                and key.program.local_id != program.local_id
            ):
                self._microblocks.discard(key)
        self.ledger.bump("collatz_dead_microblock_stages_released")

    def _evict_summaries(self) -> None:
        size = len(self._summaries)
        self._summaries.clear()
        self.ledger.release(self._summary_owner, entries=size, nodes=size)

    def _evict_source_ranges(self) -> None:
        size = len(self._source_ranges)
        self._source_ranges.clear()
        self.ledger.release(self._transfer_owner, entries=size, nodes=size)

    def _arithmetic(self, value: int) -> None:
        self.ledger.observe_arithmetic(value)

    @property
    def _source(self) -> tuple[int, ...]:
        return self.original.digits

    def intern_record(self, node: _Program) -> ActionProgramID:
        found = self._program_ids.get(node)
        if found is not None:
            if node.kind == "compose":
                self.ledger.bump("composition_cache_hits")
            return ActionProgramID(self.token, "program", found)
        self.ledger.reserve_many(
            ((self._program_owner, 1, 1), (self._program_key_owner, 1, 0))
        )
        index = len(self._programs)
        self._programs.append(node)
        self._program_ids[node] = index
        if node.kind == "compose":
            self.ledger.bump("composition_evaluations")
        return ActionProgramID(self.token, "program", index)

    def _validate(self, view: CollatzLazyView) -> None:
        if type(view) is not CollatzLazyView or type(view.source) is not ArenaHandle:
            raise ValueError("expected a scoped Collatz lazy view")
        view.source.validate(self.token, "source")
        if type(view.program) is not ActionProgramID:
            raise ValueError("expected a Collatz action-program handle")
        view.program.validate(self.token, "program", size=len(self._programs))
        if (
            type(view.width) is not int
            or view.width <= 0
            or type(view.exact_width) is not bool
            or view.source.local_id != 0
        ):
            raise ValueError("invalid Collatz view handle")

    def _append(
        self,
        view: CollatzLazyView,
        operation: _Program,
        width: int,
        *,
        exact_width: bool | None = None,
    ) -> CollatzLazyView:
        self._validate(view)
        if type(operation) is not _Program:
            raise TypeError("Collatz append requires a canonical program node")
        if type(width) is not int or width <= 0:
            raise ValueError("Collatz appended extent must be positive")
        exact = view.exact_width if exact_width is None else exact_width
        if type(exact) is not bool:
            raise TypeError("Collatz exact-width metadata must be Boolean")
        if operation.kind == "shift" and operation.shift == 0:
            result = CollatzLazyView(view.source, view.program, width, exact)
            if exact:
                self._set_exact_program_width(result.program.local_id, width)
            return result
        atom = self.intern_record(operation)
        if view.program.local_id == 0:
            program = atom
        else:
            self.ledger.bump("composition_requests")
            program = self.intern_record(
                _Program("compose", view.program.local_id, atom.local_id)
            )
            self.program_compositions += 1
        result = CollatzLazyView(view.source, program, width, exact)
        if exact:
            self._set_exact_program_width(program.local_id, width)
        return result

    def _set_exact_program_width(self, program_id: int, width: int) -> None:
        """Publish source-bound extent metadata through the index ledger."""
        if type(program_id) is not int or program_id < 0:
            raise ValueError("Collatz program identity must be nonnegative")
        if type(width) is not int or width <= 0:
            raise ValueError("Collatz exact program width must be positive")
        program = ActionProgramID(self.token, "program", program_id)
        program.validate(self.token, "program", size=len(self._programs))
        record = _ExactProgramWidth(program, width)
        prior = self._exact_program_widths.get(program)
        if prior is not None:
            if prior.width != width:
                raise ValueError("one Collatz program acquired two exact extents")
            return
        self.ledger.reserve(self._width_owner, entries=1)
        try:
            self._exact_program_widths[program] = record
        except BaseException:
            self.ledger.release(self._width_owner, entries=1)
            raise

    def _known_program_width(self, program: ActionProgramID) -> int | None:
        """Resolve typed exact extent metadata without numeric packing."""
        if type(program) is not ActionProgramID:
            raise TypeError("Collatz extent lookup requires an action-program ID")
        program.validate(self.token, "program", size=len(self._programs))
        record = self._exact_program_widths.get(program)
        return None if record is None else record.width

    def _operations(self, view: CollatzLazyView) -> list[ActionProgramID]:
        self._validate(view)
        stack = [view.program]
        out: list[ActionProgramID] = []
        while stack:
            self.ledger.bump("collatz_stream_dag_visits")
            reference = stack.pop()
            node_id = reference.local_id
            node = self._programs[node_id]
            if node.kind == "compose":
                stack.extend(
                    (
                        ActionProgramID(self.token, "program", node.right),
                        ActionProgramID(self.token, "program", node.left),
                    )
                )
            elif node.kind != "identity":
                out.append(ActionProgramID(self.token, "program", node_id))
        return out

    def stream(self, view: CollatzLazyView) -> Iterator[int]:
        """An iterative stream; each stage has one finite carry/shift counter."""
        self._validate(view)
        ports: list[_Mul3Port | _ShiftPort] = []
        for reference in self._operations(view):
            node = self._programs[reference.local_id]
            if node.kind == "mul3":
                ports.append(_Mul3Port(reference))
                if node.shift:
                    ports.append(_ShiftPort(reference, node.shift))
            elif node.kind == "shift":
                ports.append(_ShiftPort(reference, node.shift))
            else:
                raise AssertionError(node.kind)
        peak = self.ledger.counters.get("collatz_stream_peak_ports", 0)
        self.ledger.bump("collatz_stream_peak_ports", max(0, len(ports) - peak))
        cursor = 0
        while True:
            bit = self._source[cursor] if cursor < len(self._source) else 0
            cursor += 1
            discarded = False
            for port in ports:
                if isinstance(port, _ShiftPort):
                    if port.remaining:
                        port.remaining -= 1
                        discarded = True
                        break
                else:
                    bit = port.advance(bit, self.ledger)
                    self.maximum_carry = max(self.maximum_carry, int(port.state))
                    self.carry_cell_evaluations += 1
            if not discarded:
                self.ledger.bump("collatz_stream_emitted_bits")
                yield bit

    @source_reads_only
    def range_summary(self, view: CollatzLazyView) -> _CarryRangeSummary:
        """Summarize the full finite output range without retaining its bits."""
        self._validate(view)
        self.summary_queries += 1
        self.ledger.bump("symbolic_port_queries")
        key = _SummaryKey(view.program, view.width)
        # Arbitrary future prefixes collectively expose every bit through
        # last_one. Only the original source may retain this prefix observer.
        cacheable = view.program.local_id == 0
        found = self._summaries.get(key) if cacheable else None
        if found is not None:
            self.ledger.bump("summary_cache_hits")
            return found
        effect = self._range_evaluator.range_effect(view.program, 0, view.width)
        result = _CarryRangeSummary(view.width, 0, effect.first_one, effect.last_one)
        self.ledger.bump("summary_evaluations")
        if cacheable:
            self.ledger.reserve(self._summary_owner, entries=1, nodes=1)
            self._summaries[key] = result
        return result

    @source_reads_only
    def mul3_summary(self, view: CollatzLazyView) -> tuple[_CarryRangeSummary, ...]:
        """The complete three-carry observer of a source range, including flush."""
        self._validate(view)
        self.ledger.bump("symbolic_port_queries")
        self.ledger.bump(
            "symbolic_maximum_port_bits",
            max(0, 2 - self.ledger.counters.get("symbolic_maximum_port_bits", 0)),
        )
        self.ledger.bump("collatz_mul3_summary_requests")
        key = _SummaryKey(view.program, view.width)
        cacheable = view.program.local_id == 0
        found = self._mul3_summaries.get(key) if cacheable else None
        if found is not None:
            self.ledger.bump("collatz_mul3_summary_cache_hits")
            self.ledger.bump("summary_cache_hits")
            return found.rows
        self.ledger.bump("collatz_mul3_summary_evaluations")
        transfer = self._range_evaluator.range_effect(
            view.program, 0, view.width
        ).transfer
        result = transfer.compose(_CarryRangeTransfer.bit(0).repeat(2))
        self.maximum_carry = max(self.maximum_carry, 2)
        self.ledger.bump("summary_evaluations")
        if cacheable:
            self._mul3_summaries[key] = result
        return result.rows

    def _source_transfer(self, width: int) -> _CarryRangeTransfer:
        found = self._source_ranges.get(_SourceRangeKey(width))
        if found is not None:
            self.ledger.bump("summary_cache_hits")
            return found
        leaves = _CarryRangeTransfer.bit(0), _CarryRangeTransfer.bit(1)
        for bit in (0, 1):
            for carry in range(3):
                self._arithmetic(3 * bit + carry)
        blocks: list[_CarryRangeTransfer] = []
        for position in range(min(width, len(self._source))):
            current = leaves[self._source[position]]
            while blocks and blocks[-1].length == current.length:
                current = blocks.pop().compose(current)
                self.source_transfer_compositions += 1
            blocks.append(current)
        result = leaves[0].repeat(0)
        for block in blocks:
            result = result.compose(block)
            self.source_transfer_compositions += 1
        if width > len(self._source):
            result = result.compose(leaves[0].repeat(width - len(self._source)))
        self.ledger.bump("summary_evaluations")
        self.ledger.reserve(self._transfer_owner, entries=1, nodes=1)
        self._source_ranges[_SourceRangeKey(width)] = result
        return result

    @source_reads_only
    def view_point(self, view: CollatzLazyView, position: int) -> int:
        self._validate(view)
        if type(position) is not int:
            raise TypeError("Collatz point coordinate must be an exact integer")
        if position < 0 or position >= view.width:
            return 0
        if view.exact_width and view.width == 1:
            # Every certified Collatz view is positive. Exact one-bit extent
            # therefore proves the fixed value without traversing its prefix.
            return 1
        return self._range_evaluator.point(view.program, position)

    def _odd_event(self, view: CollatzLazyView) -> tuple[CollatzLazyView, int]:
        before = self.ledger.counters.get("collatz_event_summary_evaluations", 0)
        summary = self._range_evaluator.event_summary(view.program, view.width)
        self.branch_evaluations += (
            self.ledger.counters.get("collatz_event_summary_evaluations", 0) - before
        )
        if summary.first_one is None or summary.last_one is None:
            raise AssertionError("positive 3x+1 became zero")
        valuation = summary.first_one
        return self._append(
            view, _Program("mul3", shift=valuation), summary.last_one + 1 - valuation
        ), valuation

    def valuation_program(self, valuations: Iterator[int]) -> CollatzLazyView:
        """Apply an already certified schedule without numeric affine lowering."""
        view = self.initial
        for valuation in valuations:
            if type(valuation) is not int or valuation < 0:
                raise ValueError(valuation)
            view = self._append(
                view,
                _Program("mul3", shift=valuation),
                max(1, view.width + 2 - valuation),
                exact_width=False,
            )
        return CollatzLazyView(view.source, view.program, view.width, exact_width=False)

    def _remember(
        self, key: _ResultKey, result: LazyCollatzResult
    ) -> LazyCollatzResult:
        self.ledger.reserve(self._result_owner, entries=1, nodes=1)
        self._results[key] = result
        self.applications += 1
        return result

    def advance_events(self, events: int) -> LazyCollatzResult:
        if type(events) is not int or events < 0 or not self._source[0]:
            raise ValueError(
                "accelerated events require an odd source and nonnegative count"
            )
        key = _ResultKey("events", events)
        found = self._results.get(key)
        if found is not None:
            return found
        previous_key = max(
            (
                candidate
                for candidate in self._results
                if candidate.kind == "events" and candidate.steps < events
            ),
            key=lambda candidate: candidate.steps,
            default=None,
        )
        previous = None if previous_key is None else self._results[previous_key]
        view = self.initial if previous is None else previous.view
        valuations: list[int] = [] if previous is None else list(previous.valuations)
        completed = 0 if previous_key is None else previous_key.steps
        repeated = 0 if previous is None else previous.repeated_twos
        remaining = events - completed
        if previous is not None:
            self.ledger.bump("collatz_event_endpoint_reuse")
        while remaining:
            if view.width == 1 and self.view_point(view, 0) == 1:
                self.fixed_cycle_skips += remaining
                return self._remember(
                    key,
                    LazyCollatzResult(view, tuple(valuations), repeated + remaining),
                )
            view, valuation = self._odd_event(view)
            valuations.append(valuation)
            remaining -= 1
        return self._remember(key, LazyCollatzResult(view, tuple(valuations), repeated))

    def advance_physical(self, steps: int) -> LazyCollatzResult:
        if type(steps) is not int or steps < 0:
            raise ValueError(steps)
        key = _ResultKey("physical", steps)
        found = self._results.get(key)
        if found is not None:
            return found
        first = self.range_summary(self.initial).first_one
        if first is None:
            raise AssertionError("zero source")
        initial_shift = min(first, steps)
        view = self._append(
            self.initial,
            _Program("shift", shift=initial_shift),
            self.initial.width - initial_shift,
        )
        remaining = steps - initial_shift
        valuations: list[int] = []
        repeated = 0
        partial = 0
        while remaining:
            if view.width == 1 and self.view_point(view, 0) == 1:
                repeated, remaining = divmod(remaining, 3)
                self.fixed_cycle_skips += repeated
                if not remaining:
                    break
            target, valuation = self._odd_event(view)
            if remaining >= 1 + valuation:
                view = target
                valuations.append(valuation)
                remaining -= 1 + valuation
            else:
                partial = remaining
                view = self._append(
                    view,
                    _Program("mul3", shift=remaining - 1),
                    target.width + valuation - remaining + 1,
                )
                remaining = 0
        return self._remember(
            key,
            LazyCollatzResult(
                view, tuple(valuations), repeated, initial_shift, partial
            ),
        )

    @source_reads_only
    def active_width(self) -> int:
        return self.advance_physical(self.steps).view.width

    @source_reads_only
    def point(self, position: int) -> int:
        if type(position) is not int:
            raise TypeError("Collatz point coordinate must be an exact integer")
        self.point_queries += 1
        result = self.advance_physical(self.steps)
        if position < 0 or position >= result.view.width:
            return self.blank
        return self.view_point(result.view, position)

    def materialize_bits(
        self, view: CollatzLazyView, capability: LoweringCapability
    ) -> tuple[int, ...]:
        """Explicit endpoint lowering boundary; never called by point/width."""
        self._validate(view)
        if (
            type(capability) is not LoweringCapability
            or capability.owner is not self.token
        ):
            raise ValueError("foreign endpoint lowering capability")
        self.ledger.bump("endpoint_lowering_requests")
        stream = self.stream(view)
        output = tuple(next(stream) for _ in range(view.width))
        self.ledger.bump("explicitly_lowered_digits", len(output))
        self.ledger.bump("explicitly_materialized_endpoints")
        return output

    def retained_spans(self) -> tuple[DyadicSpan, ...]:
        # Reporting must not allocate another source/endpoint tree.
        return ()

    def source_span(self) -> DyadicSpan:
        """Explicit immutable source projection for compatibility diagnostics."""
        return dyadic_source_span(
            self._source, blank=0, logical_length=len(self._source)
        )

    def retained_entries(self) -> int:
        """Return the authoritative index-owned retained-entry inventory.

        The former hand-maintained sum omitted the microblock program-authority
        entry and therefore underreported every application by one.
        """
        return self.ledger.entries

    def metrics(self) -> dict[str, int]:
        return collect_lazy_collatz_metrics(
            self,
            program_entries=len(self._programs),
            summary_entries=(
                len(self._summaries)
                + len(self._source_ranges)
                + len(self._mul3_summaries)
            ),
        )


register_proof_geometry_fields(
    {
        _Program: frozenset(("left", "right", "shift")),
        _ExactProgramWidth: frozenset(("width",)),
        _ResultKey: frozenset(("steps",)),
        _SummaryKey: frozenset(("width",)),
        _SourceRangeKey: frozenset(("width",)),
        _Mul3Port: frozenset(),
        _ShiftPort: frozenset(("remaining",)),
        CollatzLazyView: frozenset(("width",)),
        LazyCollatzResult: frozenset(
            ("valuations", "repeated_twos", "initial_shift", "partial_ticks")
        ),
    }
)
register_proof_opaque_types(Mul3Carry)
