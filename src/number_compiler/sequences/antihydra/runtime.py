"""Charged, source-bound finite Antihydra execution with lazy dyadic kernels."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.antihydra.blocks import (
    ArithmeticCylinder,
    Cylinder,
    admitted_arithmetic_cylinder,
    arithmetic_from_word,
    arithmetic_kernel,
    kernel,
    physical_roof,
    terminal_effect,
)
from number_compiler.sequences.antihydra.machine import MACHINE_SHA256
from number_compiler.sequences.antihydra.projection_workspace import SectionImageWorkspace
from number_compiler.sequences.antihydra.projection_fragments import (
    ProjectionFragmentCache,
)

_SOURCE = object()


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


class AntihydraArithmeticTerm:
    """Lazy, total nth arithmetic image with optional guarded physical roof."""

    def __init__(
        self,
        returns: int,
        *,
        max_steps: int = 4096,
        max_state_bits: int = 4096,
        max_cache_entries: int = 8192,
        _engine: CylinderEngine | None = None,
    ) -> None:
        self.requested = require_integer(returns, "macro returns", 0)
        self.max_steps = require_integer(max_steps, "macro return budget", 0)
        self.max_state_bits = require_integer(max_state_bits, "integer bit budget", 4)
        self.max_cache_entries = require_integer(
            max_cache_entries, "cache budget", 32
        )
        if self.requested > self.max_steps or 4 + self.requested > self.max_state_bits:
            raise ValueError("Antihydra source execution budget exceeded")
        if _engine is not None and (
            type(_engine) is not CylinderEngine
            or _engine.capacity != self.max_cache_entries
        ):
            raise ValueError("Antihydra term has another cylinder engine")
        self.engine = (
            CylinderEngine(max_cache_entries=self.max_cache_entries)
            if _engine is None
            else _engine
        )
        self.ledger = self.engine.ledger
        term_serial = self.engine.term_serial
        self.engine.term_serial += 1
        self.segment_owner = self.ledger.register(
            f"antihydra.arithmetic.segments.{term_serial}",
            "arithmetic_cylinder_support",
        )
        self.segments: LedgerList[ArithmeticSegment] = self.ledger.make_list(
            self.segment_owner, nodes_per_entry=1, append_only=False
        )
        self.ledger.register_container(
            self.segment_owner,
            self.segments,
            payloads=lambda: self.segments,
            node_count=lambda: len(self.segments),
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
        self.ledger.register_execution_root(self)

    @property
    def _physical(self) -> Run | None:
        if not self.physical_publications:
            return None
        if len(self.physical_publications) != 1:
            raise ValueError("multiple Antihydra physical publications")
        return self.physical_publications[0].run

    def _first_failure(
        self, block: ArithmeticCylinder, h: int, balance: int, start: int
    ) -> int:
        if balance + block.minimum >= 0:
            raise ValueError("safe cylinder has no first failure")
        while block.width > 1:
            first_width = 1 << ((block.width - 1).bit_length() - 1)
            first = arithmetic_from_word(
                h % (1 << first_width),
                first_width,
                block.parity_word & ((1 << first_width) - 1),
            )
            self.engine.count("first_failure_descents")
            if balance + first.minimum < 0:
                block = first
                continue
            h, balance = first.advance(h, balance)
            start += first_width
            last_width = block.width - first_width
            block = arithmetic_from_word(
                h % (1 << last_width),
                last_width,
                block.parity_word >> first_width,
            )
        return start

    def result(self) -> ArithmeticResult:
        if self._result is not None:
            self._result.require_source()
            self.engine.count("arithmetic_result_hits")
            return self._result
        if self.segments:
            raise ValueError("partial Antihydra arithmetic publication")
        h = 8
        balance = minimum = 0
        first_failure: int | None = None
        completed = 0
        try:
            while completed < self.requested:
                width = min(64, self.requested - completed)
                block = self.engine.arithmetic_cylinder(h % (1 << width), width)
                self.ledger.reserve(self.segment_owner, entries=1, nodes=1)
                self.segments.append(ArithmeticSegment(completed, block))
                if first_failure is None and balance + block.minimum < 0:
                    first_failure = self._first_failure(block, h, balance, completed)
                old_balance = balance
                h, balance = block.advance(h, balance)
                minimum = min(minimum, old_balance + block.minimum)
                completed += width
                self.engine.count("arithmetic_block_applications")
                self.engine.count("arithmetic_returns", width)
                self.engine.count(
                    "arithmetic_operand_bits", h.bit_length() + balance.bit_length()
                )
                if (
                    h.bit_length() > self.max_state_bits
                    or balance.bit_length() > self.max_state_bits
                ):
                    raise ValueError("Antihydra arithmetic state exceeds bit budget")
        except BaseException:
            retained = len(self.segments)
            self.segments.clear()
            self.ledger.release(
                self.segment_owner, entries=retained, nodes=retained
            )
            self.engine.count("arithmetic_publication_rollbacks")
            raise
        result = object.__new__(ArithmeticResult)
        values = dict(
            requested=self.requested,
            h=h,
            balance=balance,
            minimum=minimum,
            first_failure_index=first_failure,
            ledger=self.ledger,
            _term=self,
            _source=_SOURCE,
        )
        for name, value in values.items():
            object.__setattr__(result, name, value)
        self._result = result
        self.engine.count("arithmetic_result_publications")
        return result

    def _validate_result(self, result: ArithmeticResult) -> None:
        h, balance, minimum, completed = 8, 0, 0, 0
        first_failure: int | None = None
        for segment in self.segments:
            if type(segment) is not ArithmeticSegment or type(segment.start) is not int:
                raise ValueError("retained Antihydra arithmetic support was changed")
            block = segment.cylinder
            if type(block) is not ArithmeticCylinder:
                raise ValueError("retained Antihydra arithmetic support was changed")
            try:
                block.__post_init__()
            except ValueError as error:
                raise ValueError(
                    "retained Antihydra arithmetic support was changed"
                ) from error
            canonical = admitted_arithmetic_cylinder(block.residue, block.width)
            self.engine.count(
                "arithmetic_result_validation_branch_steps", block.width
            )
            if canonical != block:
                raise ValueError("retained Antihydra arithmetic support was changed")
            if (
                segment.start != completed
                or block.residue != h % (1 << block.width)
            ):
                raise ValueError("retained Antihydra arithmetic support was changed")
            if first_failure is None and balance + block.minimum < 0:
                first_failure = self._first_failure(block, h, balance, completed)
            old_balance = balance
            h, balance = block.advance(h, balance)
            minimum = min(minimum, old_balance + block.minimum)
            completed += block.width
            self.engine.count("arithmetic_result_validation_blocks")
            self.engine.count(
                "arithmetic_result_validation_operand_bits",
                h.bit_length() + balance.bit_length(),
            )
        if (
            completed != self.requested
            or result.requested != self.requested
            or (result.h, result.balance, result.minimum, result.first_failure_index)
            != (h, balance, minimum, first_failure)
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
        for segment in self.segments:
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
        values = dict(
            requested=result.requested,
            returns=completed,
            h=h,
            balance=balance,
            minimum=minimum,
            left=left,
            right=right,
            halted=halted,
            ledger=self.ledger,
            _engine=self.engine,
            _term=self,
            _source=_SOURCE,
        )
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
            "retained_source_blocks": len(self.segments),
            "retained_nodes": self.ledger.nodes,
            "peak_nodes": self.ledger.peak_nodes,
            "work_counters": dict(self.ledger.counters),
        }


class CylinderEngine:
    """One owned memo; no global tables and no hidden scalar physical replay."""

    def __init__(self, *, max_cache_entries: int = 8192) -> None:
        require_integer(max_cache_entries, "cache budget", 32)
        self.ledger = ResourceLedger(max_nodes=max_cache_entries + 32,
                                     max_cache_entries=max_cache_entries)
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

    def count(self, name: str, amount: int = 1) -> None:
        counters = self.ledger.counters
        counters[name] = counters.get(name, 0) + amount

    def cylinder(self, residue: int, width: int) -> Cylinder:
        require_integer(width, "block width", 1, 64)
        residue %= 1 << width
        key = width, residue
        if key in self.memo:
            self.count("cylinder_cache_hits")
            return self.memo[key]
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
                size, source, expanded = stack.pop()
                current = size, source
                if current in self.memo:
                    continue
                if size <= 8:
                    self.memo[current] = kernel(source, size)
                    self.count("kernel_branch_steps", size)
                    continue
                first_width = 1 << ((size - 1).bit_length() - 1)
                last_width = size - first_width
                first_key = first_width, source % (1 << first_width)
                if first_key not in self.memo:
                    stack.extend(((size, source, False), (*first_key, False)))
                    continue
                first = self.memo[first_key]
                middle = 3**first_width * (source >> first_width) + first.output
                last_key = last_width, middle % (1 << last_width)
                if last_key not in self.memo:
                    stack.extend(((size, source, True), (*last_key, False)))
                    continue
                self.memo[current] = first.then(self.memo[last_key])
                self.count("cylinder_compositions")
            return self.memo[key]
        finally:
            self.stack.clear()
            self.ledger.release(self.workspace, entries=16, nodes=16)

    def arithmetic_cylinder(self, residue: int, width: int) -> ArithmeticCylinder:
        """Build a powered arithmetic action without constructing clock roofs."""
        require_integer(width, "block width", 1, 64)
        residue %= 1 << width
        key = width, residue
        if key in self.arithmetic_memo:
            self.count("arithmetic_cylinder_cache_hits")
            return self.arithmetic_memo[key]
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
                if current in self.arithmetic_memo:
                    continue
                if size <= 8:
                    self.arithmetic_memo[current] = arithmetic_kernel(source, size)
                    self.count("arithmetic_kernel_branch_steps", size)
                    continue
                first_width = 1 << ((size - 1).bit_length() - 1)
                last_width = size - first_width
                first_key = first_width, source % (1 << first_width)
                if first_key not in self.arithmetic_memo:
                    stack.extend(((size, source, False), (*first_key, False)))
                    continue
                first = self.arithmetic_memo[first_key]
                middle = 3**first_width * (source >> first_width) + first.output
                last_key = last_width, middle % (1 << last_width)
                if last_key not in self.arithmetic_memo:
                    stack.extend(((size, source, True), (*last_key, False)))
                    continue
                self.arithmetic_memo[current] = first.then(
                    self.arithmetic_memo[last_key]
                )
                self.count("arithmetic_cylinder_compositions")
            return self.arithmetic_memo[key]
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
