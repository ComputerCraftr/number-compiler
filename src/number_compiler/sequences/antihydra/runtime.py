"""Charged, source-bound finite Antihydra execution with lazy dyadic kernels."""

from __future__ import annotations

from collections.abc import Callable, MutableMapping
from dataclasses import dataclass
from typing import TYPE_CHECKING, TypeVar

from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.output_stream_metrics import (
    initialize_output_stream_metrics,
)
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.antihydra.blocks import (
    ArithmeticCylinder,
    Cylinder,
    arithmetic_from_word,
    arithmetic_kernel,
    kernel,
    physical_roof,
    terminal_effect,
)
from number_compiler.sequences.antihydra.machine import MACHINE_SHA256
from number_compiler.sequences.antihydra.projection_fragments import (
    ProjectionFragmentCache,
)
from number_compiler.sequences.antihydra.projection_workspace import (
    SectionImageWorkspace,
)

_SOURCE = object()
_CylinderT = TypeVar("_CylinderT", Cylinder, ArithmeticCylinder)

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.arithmetic_images import (
        AntihydraArithmeticImageWorkspace,
    )
    from number_compiler.sequences.antihydra.mahler_action import MahlerWorkspace


@dataclass(frozen=True, slots=True, init=False)
class Run:
    """Result issued only by the blank-source executor, never by an observer tuple."""

    requested: int
    returns: int
    h: int
    balance: int
    minimum: int
    left: int
    right: int
    halted: bool
    ledger: ResourceLedger
    _engine: CylinderEngine
    _term: AntihydraArithmeticTerm
    _source: object

    @property
    def physical_ticks(self) -> int:
        return self.left + self.right

    @property
    def head(self) -> int:
        return self.right - self.left

    @property
    def odd_events(self) -> int:
        return (self.returns + self.balance) // 3

    @property
    def source_binding(self) -> str:
        return f"{MACHINE_SHA256}:blank:{self.requested}"

    def require_source(self) -> None:
        if (
            type(self) is not Run
            or getattr(self, "_source", None) is not _SOURCE
            or type(getattr(self, "_engine", None)) is not CylinderEngine
            or type(getattr(self, "_term", None)) is not AntihydraArithmeticTerm
            or self._engine.ledger is not self.ledger
            or self._term.engine is not self._engine
            or self._term.ledger is not self.ledger
        ):
            raise ValueError("unbound Antihydra result")
        arithmetic = self._term._result
        if type(arithmetic) is not ArithmeticResult:
            raise ValueError("unbound Antihydra arithmetic result")
        arithmetic.require_source()
        self._term._validate_physical(self)


@dataclass(frozen=True, slots=True)
class ArithmeticSegment:
    """One retained chronological source cylinder, never a return itinerary."""

    start: int
    cylinder: ArithmeticCylinder


@dataclass(frozen=True, slots=True)
class _PhysicalPublication:
    """Charged endpoint seal for one observer-admissible physical result."""

    run: Run
    requested: int
    returns: int
    h: int
    balance: int
    minimum: int
    left: int
    right: int
    halted: bool

    def matches(self, run: Run) -> bool:
        return (
            run.requested,
            run.returns,
            run.h,
            run.balance,
            run.minimum,
            run.left,
            run.right,
            run.halted,
        ) == (
            self.requested,
            self.returns,
            self.h,
            self.balance,
            self.minimum,
            self.left,
            self.right,
            self.halted,
        )


@dataclass(frozen=True, slots=True, init=False)
class ArithmeticResult:
    """Total source-8 arithmetic image, independent of TM ledger admission."""

    requested: int
    h: int
    balance: int
    minimum: int
    first_failure_index: int | None
    ledger: ResourceLedger
    _term: AntihydraArithmeticTerm
    _source: object

    @property
    def returns(self) -> int:
        return self.requested

    @property
    def odd_events(self) -> int:
        """Centered odd steps in the total arithmetic image."""
        return (self.returns + self.balance) // 3

    @property
    def source_binding(self) -> str:
        return f"{MACHINE_SHA256}:blank:arithmetic:{self.requested}"

    def require_source(self) -> None:
        if (
            type(self) is not ArithmeticResult
            or getattr(self, "_source", None) is not _SOURCE
            or type(getattr(self, "_term", None)) is not AntihydraArithmeticTerm
            or self._term.ledger is not self.ledger
            or self._term._result is not self
        ):
            raise ValueError("unbound Antihydra arithmetic result")
        self._term._validate_result(self)


def authenticated_arithmetic_result(
    result: Run | ArithmeticResult,
) -> ArithmeticResult:
    """Return the exact total arithmetic owner behind a public source result."""
    if type(result) is ArithmeticResult:
        result.require_source()
        return result
    if type(result) is Run:
        result.require_source()
        if result.halted:
            raise ValueError("halted source has no returning Mahler seam")
        arithmetic = result._term._result
        if type(arithmetic) is not ArithmeticResult:
            raise ValueError("unbound Antihydra arithmetic result")
        # Run.require_source has already authenticated this exact term result
        # before checking the physical publication. No intervening constructor
        # or observer replaces it here, so a second aggregate check repeats work.
        return arithmetic
    raise TypeError("Mahler observations require an Antihydra source result")


class AntihydraArithmeticTerm:
    """Lazy, total nth arithmetic image with optional guarded physical roof."""

    def __init__(
        self,
        returns: int,
        *,
        max_steps: int = 4096,
        max_state_bits: int = 4096,
        max_cache_entries: int = 8192,
        shared_cache: bool = True,
        _engine: CylinderEngine | None = None,
    ) -> None:
        if type(shared_cache) is not bool:
            raise TypeError("shared_cache must be a bool")
        self.requested = require_integer(returns, "macro returns", 0)
        self.max_steps = require_integer(max_steps, "macro return budget", 0)
        self.max_state_bits = require_integer(max_state_bits, "integer bit budget", 4)
        self.max_cache_entries = require_integer(max_cache_entries, "cache budget", 32)
        if self.requested > self.max_steps or 4 + self.requested > self.max_state_bits:
            raise ValueError("Antihydra source execution budget exceeded")
        if _engine is not None and (
            type(_engine) is not CylinderEngine
            or _engine.capacity != self.max_cache_entries
        ):
            raise ValueError("Antihydra term has another cylinder engine")
        self.engine = (
            CylinderEngine(
                max_cache_entries=self.max_cache_entries, shared_cache=shared_cache
            )
            if _engine is None
            else _engine
        )
        self.ledger = self.engine.ledger
        initialize_output_stream_metrics(self.ledger, "antihydra_output_stream")
        self.ledger.bump(_shared_keys.ANTIHYDRA_DIGIT_CONVERSION_REQUESTS, 0)
        self.ledger.bump(_shared_keys.ANTIHYDRA_DIGIT_CONVERSION_EMITTED_DIGITS, 0)
        self.ledger.bump(_shared_keys.ANTIHYDRA_DIGIT_CONVERSION_OPERAND_BITS, 0)
        self.ledger.bump(_shared_keys.ANTIHYDRA_DIGIT_CONVERSION_FAILURES, 0)
        term_serial = self.engine.term_serial
        self.engine.term_serial += 1
        self.segment_owner = self.ledger.register(
            f"antihydra.arithmetic.segments.{term_serial}",
            "arithmetic_cylinder_support",
        )
        self._segments: LedgerList[ArithmeticSegment] = self.ledger.make_list(
            self.segment_owner, nodes_per_entry=1, append_only=False
        )
        self._mahler_prepared = False
        self._source_action_prepared = False
        self._segments_ready = False
        self.ledger.register_container(
            self.segment_owner,
            self._segments,
            payloads=lambda: self._segments,
            node_count=lambda: len(self._segments),
        )
        self.result_owner = self.ledger.register(
            f"antihydra.arithmetic.result.{term_serial}", "arithmetic_result"
        )
        self.result_publications: LedgerList[ArithmeticResult] = self.ledger.make_list(
            self.result_owner, nodes_per_entry=1, append_only=False
        )
        self.ledger.register_container(
            self.result_owner,
            self.result_publications,
            payloads=lambda: self.result_publications,
            node_count=lambda: len(self.result_publications),
        )
        self.physical_owner = self.ledger.register(
            f"antihydra.physical-result.{term_serial}", "physical_result"
        )
        self.physical_publications: LedgerList[_PhysicalPublication] = (
            self.ledger.make_list(
                self.physical_owner, nodes_per_entry=2, append_only=False
            )
        )
        self.ledger.register_container(
            self.physical_owner,
            self.physical_publications,
            payloads=lambda: self.physical_publications,
            node_count=lambda: 2 * len(self.physical_publications),
        )
        self._result: ArithmeticResult | None = None
        self.arithmetic_workspace: AntihydraArithmeticImageWorkspace | None = None
        self.mahler_workspace: MahlerWorkspace | None = None
        self.ledger.register_execution_root(self)
        from number_compiler.sequences.antihydra.payload_audit import (
            register_antihydra_payload_contract,
        )

        register_antihydra_payload_contract(self)

    @property
    def _physical(self) -> Run | None:
        if not self.physical_publications:
            return None
        if len(self.physical_publications) != 1:
            raise ValueError("multiple Antihydra physical publications")
        return self.physical_publications[0].run

    @property
    def segments(self) -> LedgerList[ArithmeticSegment]:
        """Publish bounded chronological cylinders only for explicit consumers."""
        return self._materialize_segments(self.result())

    def _materialize_segments(
        self, result: Run | ArithmeticResult
    ) -> LedgerList[ArithmeticSegment]:
        if type(result) not in (Run, ArithmeticResult) or result._term is not self:
            raise ValueError("retained Antihydra support has another source result")
        if self._segments_ready:
            return self._segments
        if self._segments:
            raise ValueError("partial Antihydra arithmetic publication")
        workspace = self.arithmetic_workspace
        if workspace is None:
            raise ValueError("retained Antihydra arithmetic support was changed")
        try:
            for start, block in workspace.segments():
                self.ledger.reserve(self.segment_owner, entries=1, nodes=1)
                try:
                    self._segments.append(ArithmeticSegment(start, block))
                except BaseException:
                    self.ledger.release(self.segment_owner, entries=1, nodes=1)
                    raise
            self._segments_ready = True
            result.require_source()
        except BaseException:
            retained = len(self._segments)
            self._segments.clear()
            self.ledger.release(self.segment_owner, entries=retained, nodes=retained)
            self._segments_ready = False
            self.engine.count("arithmetic_segment_publication_rollbacks")
            raise
        self.engine.count("arithmetic_block_applications", len(self._segments))
        return self._segments

    def prepare_source_action(self) -> None:
        """Enable complete-root occurrence reuse before cold arithmetic discovery.

        The reusable record is the authenticated source-bound arithmetic action,
        not a finite Mahler quotient class.  Point/value consumers may use its
        exact affine transfer while Mahler keeps its separate safety binding.
        """
        if (
            self.engine.shared_cache
            and self.arithmetic_workspace is None
            and self._result is None
            and self.requested >= 1024
        ):
            self._source_action_prepared = True

    def prepare_mahler(self) -> None:
        """Declare a large requested consumer before arithmetic admission.

        Existing images remain authoritative: a late demand uses their direct
        associated projection, without reconstructing discarded chronology.
        """
        if (
            self.arithmetic_workspace is None
            and self._result is None
            and self.requested >= 1024
        ):
            self._mahler_prepared = True
            if self.engine.shared_cache:
                self._source_action_prepared = True

    def _arithmetic_image(self) -> AntihydraArithmeticImageWorkspace:
        """One admitted source image shared by arithmetic and safety demands."""
        from number_compiler.sequences.antihydra.arithmetic_images import (
            ANTIHYDRA_ARITHMETIC_LAW,
            AntihydraArithmeticImageWorkspace,
        )

        workspace = self.arithmetic_workspace
        if workspace is None:
            workspace = AntihydraArithmeticImageWorkspace(
                self.ledger,
                self.requested,
                shared_cache=self.engine.shared_cache,
                prepare_mahler=self._mahler_prepared,
                prepare_source_action=self._source_action_prepared,
            )
            self.arithmetic_workspace = workspace
        if (
            type(workspace) is not AntihydraArithmeticImageWorkspace
            or workspace.ledger is not self.ledger
            or workspace.returns != self.requested
            or workspace.seed != 8
            or workspace.law != ANTIHYDRA_ARITHMETIC_LAW
        ):
            raise ValueError("Antihydra arithmetic has another source image")
        workspace.validate_source(workspace.root_source)
        workspace.validate_action(workspace.root_action)
        image = workspace.image_node(workspace.root_payload)
        if (
            image.source != workspace.root_source
            or image.action != workspace.root_action
            or image.summary.width != self.requested
        ):
            raise ValueError("Antihydra arithmetic image has another source/action")
        return workspace

    def value(self) -> int:
        """Demand total arithmetic only; guarded safety remains an observer."""
        if self._result is not None:
            self._result.require_source()
            return self._result.h
        self.prepare_source_action()
        value = self._arithmetic_image().endpoint()
        if value.bit_length() > self.max_state_bits:
            raise ValueError("Antihydra arithmetic state exceeds bit budget")
        return value

    @source_reads_only
    def digit(self, index: int) -> int:
        """Read one binary cell without demanding ledger safety or the endpoint."""
        from number_compiler.hashlife.execution.dyadic_return_observers import (
            binary_cell,
        )

        index = require_integer(index, "digit coordinate")
        if index < 0:
            raise IndexError(index)
        self.prepare_source_action()
        symbol = binary_cell(self._arithmetic_image(), index)
        if symbol == 2:
            raise IndexError(index)
        return symbol

    def result(self) -> ArithmeticResult:
        if self._result is not None:
            self._result.require_source()
            self.engine.count("arithmetic_result_hits")
            return self._result
        if self._segments or self._segments_ready:
            raise ValueError("partial Antihydra arithmetic publication")
        try:
            workspace = self._arithmetic_image()
            summary = workspace.saturated_summary()
            h = workspace.endpoint()
            balance = summary.delta
            minimum = summary.minimum
            first_failure = workspace.first_failure_index()
            self.engine.count("arithmetic_returns", self.requested)
            self.engine.count(
                "arithmetic_endpoint_operand_bits",
                h.bit_length() + balance.bit_length(),
            )
            if (
                h.bit_length() > self.max_state_bits
                or balance.bit_length() > self.max_state_bits
            ):
                raise ValueError("Antihydra arithmetic state exceeds bit budget")
        except BaseException:
            retained = len(self._segments)
            self._segments.clear()
            self.ledger.release(self.segment_owner, entries=retained, nodes=retained)
            failed_workspace = self.arithmetic_workspace
            if failed_workspace is not None:
                failed_workspace.dispose()
                self.arithmetic_workspace = None
            self.engine.count("arithmetic_publication_rollbacks")
            raise
        result = object.__new__(ArithmeticResult)
        values = {
            "requested": self.requested,
            "h": h,
            "balance": balance,
            "minimum": minimum,
            "first_failure_index": first_failure,
            "ledger": self.ledger,
            "_term": self,
            "_source": _SOURCE,
        }
        for name, value in values.items():
            object.__setattr__(result, name, value)
        self.ledger.reserve(self.result_owner, entries=1, nodes=1)
        try:
            self.result_publications.append(result)
        except BaseException:
            self.ledger.release(self.result_owner, entries=1, nodes=1)
            raise
        self._result = result
        self.engine.count("arithmetic_result_publications")
        return result

    def _validate_result(self, result: ArithmeticResult) -> None:
        if (
            len(self.result_publications) != 1
            or self.result_publications[0] is not result
        ):
            raise ValueError("retained Antihydra arithmetic result was changed")
        workspace = self.arithmetic_workspace
        if workspace is None:
            raise ValueError("retained Antihydra arithmetic support was changed")
        workspace.validate()
        summary = workspace.saturated_summary()
        if type(self._segments_ready) is not bool or (
            not self._segments_ready and self._segments
        ):
            raise ValueError("retained Antihydra arithmetic support was changed")
        if self._segments_ready:
            # The workspace is independently source-authenticated. Compare
            # each retained segment as it is reconstructed; materializing a
            # second tuple of every cylinder on each observer call costs
            # uncharged storage and delays rejection of a changed first row.
            expected = workspace.segments()
            for segment in self._segments:
                try:
                    start, expected_block = next(expected)
                except StopIteration as error:
                    raise ValueError(
                        "retained Antihydra arithmetic support was changed"
                    ) from error
                self.engine.count("arithmetic_result_validation_reconstructions")
                self.engine.count(
                    "arithmetic_result_validation_operand_bits",
                    expected_block.residue.bit_length()
                    + expected_block.output.bit_length()
                    + expected_block.parity_word.bit_length(),
                )
                if (
                    type(segment) is not ArithmeticSegment
                    or type(segment.start) is not int
                ):
                    raise ValueError(
                        "retained Antihydra arithmetic support was changed"
                    )
                block = segment.cylinder
                if type(block) is not ArithmeticCylinder:
                    raise ValueError(
                        "retained Antihydra arithmetic support was changed"
                    )
                try:
                    block.__post_init__()
                except ValueError as error:
                    raise ValueError(
                        "retained Antihydra arithmetic support was changed"
                    ) from error
                if block != expected_block or segment.start != start:
                    raise ValueError(
                        "retained Antihydra arithmetic support was changed"
                    )
                self.engine.count("arithmetic_result_validation_blocks")
            if next(expected, None) is not None:
                self.engine.count("arithmetic_result_validation_reconstructions")
                raise ValueError("retained Antihydra arithmetic support was changed")
        h = workspace.endpoint()
        first_failure = workspace.first_failure_index()
        if (
            summary.width != self.requested
            or result.requested != self.requested
            or (result.h, result.balance, result.minimum, result.first_failure_index)
            != (h, summary.delta, summary.minimum, first_failure)
        ):
            raise ValueError("Antihydra arithmetic result was changed")

    def _validate_physical(self, run: Run) -> None:
        if len(self.physical_publications) != 1:
            raise ValueError("unbound Antihydra physical publication")
        publication = self.physical_publications[0]
        if publication.run is not run or not publication.matches(run):
            raise ValueError("Antihydra physical result was changed")

    def _physical_block(
        self,
        block: ArithmeticCylinder,
        h: int,
        balance: int,
        left: int,
        right: int,
        completed: int,
    ) -> tuple[int, int, int, int, int, bool]:
        def roof_for(arithmetic: ArithmeticCylinder, source_h: int) -> Cylinder:
            if arithmetic.residue != source_h % (1 << arithmetic.width):
                raise ValueError("physical roof has another arithmetic source")
            roof = physical_roof(arithmetic)
            self.engine.count("physical_roof_construction_requests")
            self.engine.count("physical_roof_terms", arithmetic.width)
            return roof

        while True:
            if balance + block.minimum >= 0:
                roof = roof_for(block, h)
                if (
                    roof.width,
                    roof.residue,
                    roof.output,
                    roof.delta,
                    roof.minimum,
                ) != (
                    block.width,
                    block.residue,
                    block.output,
                    block.delta,
                    block.minimum,
                ):
                    raise ArithmeticError("physical roof changed the arithmetic action")
                h, balance, dl, dr = roof.apply(h, balance)
                self.engine.count("physical_roof_evaluations")
                return (
                    h,
                    balance,
                    left + dl,
                    right + dr,
                    completed + block.width,
                    False,
                )
            if block.width == 1:
                dl, dr = terminal_effect(h)
                self.engine.count("terminal_macro_steps")
                return h, -1, left + dl, right + dr, completed + 1, True
            first_width = 1 << ((block.width - 1).bit_length() - 1)
            first = arithmetic_from_word(
                h % (1 << first_width),
                first_width,
                block.parity_word & ((1 << first_width) - 1),
            )
            self.engine.count("physical_first_failure_descents")
            if balance + first.minimum < 0:
                block = first
                continue
            roof = roof_for(first, h)
            h, balance, dl, dr = roof.apply(h, balance)
            left, right = left + dl, right + dr
            completed += first_width
            self.engine.count("physical_roof_evaluations")
            last_width = block.width - first_width
            block = arithmetic_from_word(
                h % (1 << last_width),
                last_width,
                block.parity_word >> first_width,
            )

    def physical_run(self) -> Run:
        result = self.result()
        cached = self._physical
        if cached is not None:
            cached.require_source()
            self.engine.count("physical_run_hits")
            return cached
        h, balance, minimum, left, right, completed = 8, 0, 0, 5, 6, 0
        halted = False
        for segment in self._materialize_segments(result):
            if segment.start != completed:
                raise ValueError("retained Antihydra source block was changed")
            old_balance = balance
            h, balance, left, right, completed, halted = self._physical_block(
                segment.cylinder, h, balance, left, right, completed
            )
            minimum = min(minimum, old_balance + segment.cylinder.minimum)
            if halted:
                minimum = -1
                break
        run_result = object.__new__(Run)
        values = {
            "requested": result.requested,
            "returns": completed,
            "h": h,
            "balance": balance,
            "minimum": minimum,
            "left": left,
            "right": right,
            "halted": halted,
            "ledger": self.ledger,
            "_engine": self.engine,
            "_term": self,
            "_source": _SOURCE,
        }
        for name, value in values.items():
            object.__setattr__(run_result, name, value)
        publication = _PhysicalPublication(
            run_result,
            run_result.requested,
            run_result.returns,
            run_result.h,
            run_result.balance,
            run_result.minimum,
            run_result.left,
            run_result.right,
            run_result.halted,
        )
        self.ledger.reserve(self.physical_owner, entries=1, nodes=2)
        try:
            self.physical_publications.append(publication)
        except BaseException:
            self.ledger.release(self.physical_owner, entries=1, nodes=2)
            raise
        self.engine.count("physical_run_publications")
        return run_result

    def metrics(self) -> dict[str, object]:
        return {
            "requested_returns": self.requested,
            "retained_source_blocks": len(self._segments),
            "retained_nodes": self.ledger.nodes,
            "peak_nodes": self.ledger.peak_nodes,
            "work_counters": dict(self.ledger.counters),
        }


class CylinderEngine:
    """One owned memo; no global tables and no hidden scalar physical replay."""

    def __init__(
        self, *, max_cache_entries: int = 8192, shared_cache: bool = True
    ) -> None:
        if type(shared_cache) is not bool:
            raise TypeError("shared_cache must be a bool")
        self._shared_cache = shared_cache
        require_integer(max_cache_entries, "cache budget", 32)
        self.ledger = ResourceLedger(
            max_nodes=max_cache_entries + 32, max_cache_entries=max_cache_entries
        )
        owner = self.ledger.register("antihydra.cylinders", "arithmetic_cylinder")
        self.memo: OwnedMemo[tuple[int, int], Cylinder] = OwnedMemo(
            self.ledger, owner, nodes_per_entry=1
        )
        arithmetic_owner = self.ledger.register(
            "antihydra.arithmetic-cylinders", "arithmetic_cylinder"
        )
        self.arithmetic_memo: OwnedMemo[tuple[int, int], ArithmeticCylinder] = (
            OwnedMemo(self.ledger, arithmetic_owner, nodes_per_entry=1)
        )
        self.workspace = self.ledger.register("antihydra.construction", "workspace")
        self.stack: LedgerList[tuple[int, int, bool]] = self.ledger.make_list(
            self.workspace, nodes_per_entry=1, append_only=False
        )
        self.capacity = max_cache_entries
        self.term_serial = 0
        self.projection_workspace: SectionImageWorkspace | None = None
        self.projection_fragments = ProjectionFragmentCache(self.ledger)
        self.projection_fragment_driver: object | None = None
        self.ledger.register_execution_root(self)
        from number_compiler.sequences.antihydra.payload_audit import (
            register_antihydra_payload_contract,
        )

        register_antihydra_payload_contract(self)

    @property
    def audit_memo_store(self) -> object:
        """Expose the exact registered memo container to the audit contract."""
        return self.memo._data

    @property
    def audit_arithmetic_memo_store(
        self,
    ) -> object:
        """Expose the exact registered arithmetic container to the audit contract."""
        return self.arithmetic_memo._data

    @property
    def shared_cache(self) -> bool:
        """Construction-time cache policy, read-only through the public option."""
        return self._shared_cache

    def count(self, name: str, amount: int = 1) -> None:
        counters = self.ledger.counters
        counters[name] = counters.get(name, 0) + amount

    def cylinder(self, residue: int, width: int) -> Cylinder:
        return self._build_cylinder(residue, width, self.memo, kernel, "")

    def arithmetic_cylinder(self, residue: int, width: int) -> ArithmeticCylinder:
        """Build a powered arithmetic action without constructing clock roofs."""
        return self._build_cylinder(
            residue, width, self.arithmetic_memo, arithmetic_kernel, "arithmetic_"
        )

    def _build_cylinder(
        self,
        residue: int,
        width: int,
        memo: MutableMapping[tuple[int, int], _CylinderT],
        build_leaf: Callable[[int, int], _CylinderT],
        prefix: str,
    ) -> _CylinderT:
        residue = require_integer(residue, "cylinder residue")
        require_integer(width, "block width", 1, 64)
        residue %= 1 << width
        key = width, residue
        if key in memo:
            self.count(prefix + "cylinder_cache_hits")
            return memo[key]
        # A width<=64 construction needs at most 15 new dyadic nodes.
        if len(self.memo) + len(self.arithmetic_memo) + 32 > self.capacity:
            self.count("cache_evictions", len(self.memo) + len(self.arithmetic_memo))
            self.memo.clear()
            self.arithmetic_memo.clear()
        self.ledger.reserve(self.workspace, entries=16, nodes=16)
        try:
            stack = self.stack
            stack.append((width, residue, False))
            while stack:
                size, source, _expanded = stack.pop()
                current = size, source
                if current in memo:
                    continue
                if size <= 8:
                    memo[current] = build_leaf(source, size)
                    self.count(prefix + "kernel_branch_steps", size)
                    continue
                first_width = 1 << ((size - 1).bit_length() - 1)
                last_width = size - first_width
                first_key: tuple[int, int] = first_width, source % (1 << first_width)
                if first_key not in memo:
                    stack.extend(((size, source, False), (*first_key, False)))
                    continue
                first = memo[first_key]
                middle = 3**first_width * (source >> first_width) + first.output
                last_key: tuple[int, int] = last_width, middle % (1 << last_width)
                if last_key not in memo:
                    stack.extend(((size, source, True), (*last_key, False)))
                    continue
                memo[current] = first.then(memo[last_key])
                self.count(prefix + "cylinder_compositions")
            return memo[key]
        finally:
            self.stack.clear()
            self.ledger.release(self.workspace, entries=16, nodes=16)

    def execute(
        self, returns: int, *, max_returns: int = 4096, max_bits: int = 4096
    ) -> Run:
        term = AntihydraArithmeticTerm(
            returns,
            max_steps=max_returns,
            max_state_bits=max_bits,
            max_cache_entries=self.capacity,
            _engine=self,
        )
        return term.physical_run()


def run(returns: int, *, max_returns: int = 4096, max_bits: int = 4096) -> Run:
    return CylinderEngine().execute(returns, max_returns=max_returns, max_bits=max_bits)
