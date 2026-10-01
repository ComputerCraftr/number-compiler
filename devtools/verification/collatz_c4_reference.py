"""Collatz reference execution through bounded C4 bisimulation-machine rungs.

This test oracle retains the SHA-verified minimized physical Collatz C4
bimachine. Reverse/add uses the production primitive grammar and has no finite
machine shortcut.

A query never builds a future ``DyadicTile`` and never retains an intermediate
field.  For sources whose *encoded* working word fits the fixed transient
microblock budget, one transient word is represented as <=64-bit limbs and
updated in place.  Only the final requested-output microblocks may be retained by
the shared capped ``MicroblockCache``.  Wider sources are deliberately routed to
the generic diamond executor by ``build_bounded_application``; there is no
successor-loop fallback here.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BlockEffect,
    BoundarySide,
    BoundaryState,
)
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.contracts.temporal_family import (
    TemporalFamilyCertificate,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.projection.microblock_cache import (
    ExactMicroblock,
    MicroblockCache,
    MicroblockKey,
)
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class CollatzC4ReferenceMetrics:
    family: str
    temporal_state_classes: int
    temporal_action_classes: int
    exact_spatial_occurrences: int
    symbolic_action_nodes: int
    jump_entries: int
    primitive_step_evaluations: int
    query_requests: int
    quotient_builds: int
    residual_physical_steps: int = 0
    action_compositions: int = 0
    action_applications: int = 0
    nonlinear_branch_evaluations: int = 0
    exact_endpoint_entries: int = 0


class _TransientMicroWord:
    """One exact transient word encoded only as bounded 64-bit limbs.

    The object is never registered as retained state and must not escape the
    query.  ``payload_bytes`` charges the complete backing limb allocation, not
    the number of logically active symbols.
    """

    __slots__ = ("bits", "blank", "blocks", "mask", "per_block", "width")

    def __init__(self, source: Sequence[int], *, blank: int, width: int) -> None:
        if (
            type(blank) is not int
            or blank < 1
            or type(width) is not int
            or width < len(source)
        ):
            raise ValueError("invalid transient microblock word")
        if any(type(value) is not int or not 0 <= value <= blank for value in source):
            raise ValueError("source symbol is outside the bounded working alphabet")
        self.blank = blank
        self.width = width
        self.bits = max(1, blank.bit_length())
        self.per_block = max(1, 64 // self.bits)
        self.mask = (1 << self.bits) - 1
        nblocks = (width + self.per_block - 1) // self.per_block
        self.blocks = [0] * nblocks
        for position in range(width):
            self.set(position, blank)
        for position, value in enumerate(source):
            self.set(position, int(value))

    @property
    def payload_bytes(self) -> int:
        # Charge the complete 64-bit backing limb for every block.
        return 8 * len(self.blocks)

    def _locate(self, position: int) -> tuple[int, int]:
        if type(position) is not int or not 0 <= position < self.width:
            raise IndexError(position)
        block, offset = divmod(position, self.per_block)
        return block, offset * self.bits

    def get(self, position: int) -> int:
        block, shift = self._locate(position)
        return (self.blocks[block] >> shift) & self.mask

    def set(self, position: int, value: int) -> None:
        if type(value) is not int or not 0 <= value <= self.mask:
            raise ValueError("transient microblock symbol does not fit its encoding")
        block, shift = self._locate(position)
        mask = self.mask << shift
        self.blocks[block] = (self.blocks[block] & ~mask) | (value << shift)
        if self.blocks[block].bit_length() > 64:
            raise AssertionError("transient microblock exceeded 64 encoded bits")

    def active_width(self) -> int:
        for position in range(self.width - 1, -1, -1):
            if self.get(position) != self.blank:
                return position + 1
        return 0


class CollatzC4ReferenceApplication:
    """Bounded Collatz reference executor over verified minimized C4 rungs."""

    __slots__ = (
        "__weakref__",
        "_bits",
        "_final_fills",
        "_machine_applications",
        "_machine_symbol_visits",
        "_queries",
        "_residual_steps",
        "_symbols_per_block",
        "_width",
        "base",
        "blank",
        "certificate",
        "compiler",
        "is_collatz_c4_executor",
        "ledger",
        "logical_length",
        "microblocks",
        "program",
        "source_geometry",
    )

    def __init__(
        self,
        effect: BlockEffect,
        source: Sequence[int],
        *,
        logical_length: int,
        certificate: TemporalFamilyCertificate,
        ledger: ResourceLedger,
        compiler: LazyCompiler,
        source_geometry: SourceGeometry,
        microblocks: MicroblockCache,
    ) -> None:
        certificate.validate(effect)
        if (
            compiler.ledger is not ledger
            or source_geometry.ledger is not ledger
            or microblocks.ledger is not ledger
        ):
            raise ValueError("family executor resources belong to different indices")
        source_geometry.require_source(source, effect.blank)
        if certificate.family != "collatz":
            raise ValueError(certificate.family)
        self.ledger = ledger
        self.compiler = compiler
        self.program = compiler.reference(effect)
        self.certificate = certificate
        self.logical_length = int(logical_length)
        self.source_geometry = source_geometry
        self.microblocks = microblocks
        self.base, self.blank = int(effect.base), int(effect.blank)
        self._width: int | None = None
        self._queries = 0
        self._machine_applications = 0
        self._machine_symbol_visits = 0
        self._residual_steps = 0
        self._final_fills = 0
        self._bits = max(1, self.blank.bit_length())
        self._symbols_per_block = max(1, 64 // self._bits)
        self.is_collatz_c4_executor = True
        ledger.register_execution_root(self)
        ledger.bump("family_bisimulation_executor_instances", 1)

        transient = self.transient_payload_bytes(self.blank, self.logical_length)
        if transient > self.microblocks.MAX_TRANSIENT_BYTES:
            raise ValueError(
                "working word exceeds the fixed transient microblock budget"
            )
        ledger.counters["family_bisimulation_transient_payload_peak_bytes"] = max(
            ledger.counters.get("family_bisimulation_transient_payload_peak_bytes", 0),
            transient,
        )

    @staticmethod
    def transient_payload_bytes(blank: int, logical_length: int) -> int:
        bits = max(1, int(blank).bit_length())
        per_block = max(1, 64 // bits)
        return 8 * ((int(logical_length) + per_block - 1) // per_block)

    def _block_key(self, block: int) -> MicroblockKey:
        return MicroblockKey(self.program, self.base, 0, block, "output")

    def _decode(self, value: ExactMicroblock, offset: int) -> int | None:
        count = value.bit_count // self._bits
        if offset >= count:
            return None
        return (value.encoded >> (offset * self._bits)) & ((1 << self._bits) - 1)

    def _apply_machine(self, word: _TransientMicroWord, effect: BlockEffect) -> None:
        """Apply one complete finite rung in place with bounded right workspace.

        Only one right-boundary state per <=64-bit source microblock is retained
        across the pass.  Per-symbol right states exist only for the current
        microblock and are discarded before the next block.
        """
        nblocks = len(word.blocks)
        right_boundaries: list[BoundaryState] = [effect.initial(BoundarySide.RIGHT)] * (
            nblocks + 1
        )
        state = effect.initial(BoundarySide.RIGHT)
        right_boundaries[nblocks] = state
        for block_1 in range(nblocks - 1, -1, -1):
            start = block_1 * word.per_block
            stop = min(word.width, start + word.per_block)
            for position in range(stop - 1, start - 1, -1):
                state = effect.advance(BoundarySide.RIGHT, state, word.get(position))
                self._machine_symbol_visits += 1
            right_boundaries[block_1] = state

        left = effect.initial(BoundarySide.LEFT)
        local_peak = 0
        for block_2 in range(nblocks):
            start = block_2 * word.per_block
            stop = min(word.width, start + word.per_block)
            count = stop - start
            local_right: list[BoundaryState] = [right_boundaries[block_2 + 1]] * count
            state = right_boundaries[block_2 + 1]
            for offset in range(count - 1, -1, -1):
                position = start + offset
                local_right[offset] = state
                state = effect.advance(BoundarySide.RIGHT, state, word.get(position))
            if state != right_boundaries[block_2]:
                raise AssertionError(
                    "right boundary microblock reconstruction disagrees"
                )
            local_peak = max(local_peak, count)
            for offset in range(count):
                position = start + offset
                symbol = word.get(position)
                output = int(effect.emit(left, symbol, local_right[offset]))
                left = effect.advance(BoundarySide.LEFT, left, symbol)
                word.set(position, output)
                self._machine_symbol_visits += 2
        self._machine_applications += 1
        self.ledger.bump("family_bisimulation_machine_applications", 1)
        self.ledger.bump("family_bisimulation_symbol_visits", 3 * word.width)
        self.ledger.counters["family_bisimulation_right_workspace_peak"] = max(
            self.ledger.counters.get("family_bisimulation_right_workspace_peak", 0),
            nblocks + local_peak,
        )

    def _run_verified_rungs(self) -> _TransientMicroWord:
        self.compiler.resolve(self.program)
        # Read the authoritative immutable source through SourceGeometry.  The
        # padded blank exterior is source geometry too; bypassing this path
        # would make the family executor a second source authority.
        source_word = tuple(
            self.source_geometry.read(position)
            for position in range(self.logical_length)
        )
        word = _TransientMicroWord(
            source_word, blank=self.blank, width=self.logical_length
        )
        if word.payload_bytes > self.microblocks.MAX_TRANSIENT_BYTES:
            raise AssertionError(
                "transient payload preflight and construction disagree"
            )

        from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
            PhysicalCollatzFourBlockEffect,
        )
        from number_compiler.sequences.collatz.block_power import (
            CollatzPhysicalBlockEffect,
        )

        steps = self.certificate.steps
        c4 = PhysicalCollatzFourBlockEffect()
        for _ in range(steps // 4):
            self._apply_machine(word, c4)
        residual = steps & 3
        self._residual_steps += residual
        if residual:
            c1 = CollatzPhysicalBlockEffect()
            for _ in range(residual):
                self._apply_machine(word, c1)
        return word

    def _publish_final(self, word: _TransientMicroWord, width: int) -> None:
        prepared: list[tuple[MicroblockKey, ExactMicroblock]] = []
        if width:
            nblocks = (width + self._symbols_per_block - 1) // self._symbols_per_block
            for block in range(nblocks):
                start = block * self._symbols_per_block
                count = min(self._symbols_per_block, width - start)
                encoded = 0
                for offset in range(count):
                    value = word.get(start + offset)
                    if value == self.blank:
                        raise AssertionError("active final microblock contains a blank")
                    encoded |= value << (offset * self._bits)
                prepared.append(
                    (
                        self._block_key(block),
                        ExactMicroblock(encoded, count * self._bits),
                    )
                )
        published: list[MicroblockKey] = []
        try:
            for key, block_value in prepared:
                self.microblocks.put(key, block_value)
                published.append(key)
        except BaseException:
            for key in published:
                self.microblocks.discard(key)
            raise
        self._width = width
        self._final_fills += 1
        self.ledger.bump("family_bisimulation_final_fills", 1)
        self.ledger.counters["family_bisimulation_final_microblocks"] = len(prepared)

    def _ensure_final(self) -> None:
        if self._width is not None:
            # Width survives cache eviction; a missing requested block will call
            # this method after clearing width in point().
            return
        if self.ledger.max_cache_entries == 0:
            raise BlockContextBudgetExceeded(
                "zero cache budget rejects the required final microblock before execution"
            )
        word = self._run_verified_rungs()
        width = word.active_width()
        self._publish_final(word, width)

    def point(self, position: int) -> int:
        if type(position) is not int or not 0 <= position < self.logical_length:
            raise IndexError(position)
        self.compiler.resolve(self.program)
        self._queries += 1
        self.ledger.bump("scalar_observation_requests")
        if self._width is not None and position >= self._width:
            return self.blank
        block, offset = divmod(position, self._symbols_per_block)
        value = self.microblocks.get(self._block_key(block))
        if value is None:
            # The shared radix cache may evict output blocks.  Recompute the one
            # bounded final observation without retaining temporal history.
            self._width = None
            self._ensure_final()
            if self._width is not None and position >= self._width:
                return self.blank
            value = self.microblocks.get(self._block_key(block))
        if value is None:
            return self.blank
        decoded = self._decode(value, offset)
        return self.blank if decoded is None else int(decoded)

    def active_width(self) -> int:
        self.compiler.resolve(self.program)
        self.ledger.bump("width_queries")
        if self._width is None:
            self._ensure_final()
        assert self._width is not None
        return self._width

    def retained_spans(self) -> tuple[()]:
        return ()

    def retained_entries(self) -> int:
        return sum(
            1
            for key in self.microblocks.blocks
            if key.program == self.program
            and key.radix == self.base
            and key.stage == 0
            and key.kind == "output"
        )

    def metrics(self) -> CollatzC4ReferenceMetrics:
        family = "collatz-bisimulation-c4-linear"
        # Verified minimized C^4 kernel: 50 LEFT / 90 RIGHT classes.
        state_classes = 50 + 90
        action_classes = 1
        return CollatzC4ReferenceMetrics(
            family=family,
            temporal_state_classes=state_classes,
            temporal_action_classes=action_classes,
            exact_spatial_occurrences=0,
            symbolic_action_nodes=int(
                self.compiler.resolve(self.program).operator_nodes()
            ),
            jump_entries=self.retained_entries(),
            primitive_step_evaluations=0,
            query_requests=self._queries,
            quotient_builds=0,
            residual_physical_steps=self._residual_steps,
            action_compositions=0,
            action_applications=self._machine_applications,
            nonlinear_branch_evaluations=0,
            exact_endpoint_entries=0,
        )


__all__ = ["CollatzC4ReferenceApplication", "CollatzC4ReferenceMetrics"]
