"""Authenticated chronological occurrences for Antihydra projections."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import antihydra as _antihydra_keys
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.antihydra.blocks import (
    ArithmeticCylinder,
    arithmetic_from_word,
    physical_roof,
)
from number_compiler.sequences.antihydra.projection_audit_state import (
    ProjectionCursorAuditState,
    ProjectionStoreState,
)
from number_compiler.sequences.antihydra.projection_fragments import (
    ProjectionFragmentKey,
    projection_key_snapshot,
)
from number_compiler.sequences.antihydra.runtime import (
    AntihydraArithmeticTerm,
    ArithmeticSegment,
    Run,
)

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.observers import SpaceTimeProjection


_ONE_STEP_ROOFS = tuple(
    physical_roof(arithmetic_from_word(odd, 1, odd)) for odd in (0, 1)
)


@dataclass(frozen=True, slots=True)
class ProjectionOccurrenceID(ArenaHandle):
    """Revocable authority for the cursor's current source occurrence."""


ProjectionClass = tuple[tuple[int, int], int, int, int]


@dataclass(frozen=True, slots=True)
class ProjectionBlockImage:
    """Concrete bounded section classes discovered for one source cylinder."""

    source_h: int
    source_balance: int
    output_h: int
    output_balance: int
    head_delta: int
    time_delta: int
    classes: tuple[ProjectionClass, ...]

    def validate(self, key: ProjectionFragmentKey, width: int) -> None:
        if type(key) is not ProjectionFragmentKey or type(width) is not int:
            raise ValueError("invalid Antihydra projection block image")
        spatial_phase = key.spatial_width * (2 if key.spatial_sign == -1 else 1)
        temporal_phase = key.temporal_width * (2 if key.temporal_sign == -1 else 1)
        if (
            any(
                type(value) is not int
                for value in (
                    self.source_h,
                    self.source_balance,
                    self.output_h,
                    self.output_balance,
                    self.head_delta,
                    self.time_delta,
                )
            )
            or type(self.classes) is not tuple
            or not 1 <= width <= 64
            or len(self.classes) > width
            or self.source_h < 6
            or self.source_balance < 0
            or self.output_h < 6
            or self.output_balance < 0
            or self.time_delta < 0
            or abs(self.head_delta) > self.time_delta
        ):
            raise ValueError("invalid Antihydra projection block image")
        seen: set[tuple[tuple[int, int], int, int]] = set()
        for entry in self.classes:
            if type(entry) is not tuple or len(entry) != 4:
                raise ValueError("invalid Antihydra projection block class")
            section, head, time, copies = entry
            if (
                type(section) is not tuple
                or len(section) != 2
                or type(section[0]) is not int
                or type(section[1]) is not int
                or type(head) is not int
                or not 0 <= head < spatial_phase
                or type(time) is not int
                or not 0 <= time < temporal_phase
                or type(copies) is not int
                or not 1 <= copies < key.modulus
                or (section, head, time) in seen
            ):
                raise ValueError("invalid Antihydra projection block class")
            seen.add((section, head, time))


@dataclass(frozen=True, slots=True)
class ProjectionOccurrence:
    """One exact retained cylinder and its chronological input coordinates."""

    block: ArithmeticCylinder
    start: int
    h: int
    balance: int
    head: int
    time: int
    key: ProjectionFragmentKey
    image: ProjectionBlockImage | None = None

    def __post_init__(self) -> None:
        if type(self.block) is not ArithmeticCylinder:
            raise TypeError("projection occurrence requires an arithmetic cylinder")
        self.block.__post_init__()
        if (
            type(self.start) is not int
            or self.start < 0
            or type(self.h) is not int
            or self.h < 6
            or type(self.balance) is not int
            or self.balance < 0
            or type(self.head) is not int
            or type(self.time) is not int
            or self.time < 0
            or type(self.key) is not ProjectionFragmentKey
            or (self.image is not None and type(self.image) is not ProjectionBlockImage)
        ):
            raise ValueError("invalid Antihydra projection occurrence")
        if self.block.residue != self.h % (1 << self.block.width):
            raise ValueError("projection occurrence has another cylinder source")
        if self.image is not None:
            self.image.validate(self.key, self.block.width)
            output = self.block.advance(self.h, self.balance)
            if (
                (self.image.source_h, self.image.source_balance)
                != (self.h, self.balance)
                or (self.image.output_h, self.image.output_balance) != output
                or self.image.output_balance - self.balance != self.block.delta
            ):
                raise ValueError("projection block image has another source")
        key = self.key
        cylinder = (
            self.block.width,
            self.block.residue,
            self.block.output,
            self.block.delta,
            self.block.minimum,
            self.block.parity_word,
        )
        if (
            any(
                type(value) is not int
                for value in (
                    key.source_owner,
                    key.requested,
                    key.start,
                    key.spatial_width,
                    key.temporal_width,
                    key.spatial_sign,
                    key.temporal_sign,
                    key.modulus,
                    key.head_phase,
                    key.time_phase,
                )
            )
            or key.source_owner < 0
            or key.requested < 0
            or key.start != self.start
            or key.cylinder != cylinder
            or not 1 <= key.spatial_width <= 64
            or not 1 <= key.temporal_width <= 64
            or key.spatial_sign not in (-1, 1)
            or key.temporal_sign not in (-1, 1)
            or key.modulus < 2
            or not 0
            <= key.head_phase
            < key.spatial_width * (2 if key.spatial_sign == -1 else 1)
            or not 0
            <= key.time_phase
            < key.temporal_width * (2 if key.temporal_sign == -1 else 1)
        ):
            raise ValueError("projection occurrence has an invalid source key")


@dataclass(frozen=True, slots=True)
class _CursorState:
    projection: SpaceTimeProjection
    segment_index: int
    completed: int
    h: int
    balance: int
    head: int
    time: int
    terminal: bool
    segment_seals: tuple[tuple[int, int, int, int, int, int, int], ...]


class ProjectionOccurrenceCursor:
    """Transport one authenticated run through its retained segment support.

    The cursor owns one endpoint state and at most one issued occurrence.  Calling
    :meth:`next` revokes the preceding handle before deriving the next record.
    No caller-provided arithmetic or physical coordinate enters publication.
    """

    _KIND = "antihydra-projection-occurrence"
    # Include record/tuple slots and nested key/cylinder fields. Shared integer
    # references are conservatively counted again in their independent seals.
    _STATE_NODES = 9
    _STATE_SEAL_NODES = 36
    _SEGMENT_SEAL_NODES = 8
    _OCCURRENCE_NODES = 35
    _OCCURRENCE_SEAL_NODES = 40
    _CLASS_NODES = 7

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("projection occurrence cursor requires a resource ledger")
        self.ledger = ledger
        suffix = ledger.owner_count
        self._state_owner = ledger.register(
            f"antihydra.projection-occurrence-state.{suffix}", "workspace"
        )
        self._state_seal_owner = ledger.register(
            f"antihydra.projection-occurrence-state-seal.{suffix}",
            "projection_binding",
        )
        self._occurrence_owner = ledger.register(
            f"antihydra.projection-occurrences.{suffix}", "demanded_projection"
        )
        self._occurrence_seal_owner = ledger.register(
            f"antihydra.projection-occurrence-seals.{suffix}",
            "projection_binding",
        )
        self._states: LedgerList[_CursorState] = ledger.make_list(
            self._state_owner, append_only=False
        )
        self._state_seals: LedgerList[tuple[object, ...]] = ledger.make_list(
            self._state_seal_owner, append_only=False
        )
        self._occurrences: LedgerList[ProjectionOccurrence] = ledger.make_list(
            self._occurrence_owner, append_only=False
        )
        self._occurrence_seals: LedgerList[tuple[object, ...]] = ledger.make_list(
            self._occurrence_seal_owner, append_only=False
        )
        ledger.register_container(
            self._state_owner,
            self._states,
            node_count=lambda: sum(self._state_nodes(state) for state in self._states),
            payloads=self._states.__iter__,
        )
        ledger.register_container(
            self._state_seal_owner,
            self._state_seals,
            node_count=lambda: sum(
                self._state_seal_nodes(seal) for seal in self._state_seals
            ),
            payloads=self._state_seals.__iter__,
        )
        ledger.register_container(
            self._occurrence_owner,
            self._occurrences,
            node_count=lambda: sum(
                self._occurrence_nodes(record) for record in self._occurrences
            ),
            payloads=self._occurrences.__iter__,
        )
        ledger.register_container(
            self._occurrence_seal_owner,
            self._occurrence_seals,
            node_count=lambda: sum(
                self._occurrence_seal_nodes(seal) for seal in self._occurrence_seals
            ),
            payloads=self._occurrence_seals.__iter__,
        )
        self._token = ArenaToken("antihydra-projection-occurrences")
        self._active = False
        ledger.register_execution_root(self)
        from number_compiler.sequences.antihydra.payload_audit import (
            register_antihydra_payload_contract,
        )

        register_antihydra_payload_contract(self)

    def audit_snapshot(self) -> ProjectionCursorAuditState:
        return ProjectionCursorAuditState(
            (
                ProjectionStoreState(
                    self._state_owner, "_states", "workspace", self._states
                ),
                ProjectionStoreState(
                    self._state_seal_owner,
                    "_state_seals",
                    "projection_binding",
                    self._state_seals,
                ),
                ProjectionStoreState(
                    self._occurrence_owner,
                    "_occurrences",
                    "demanded_projection",
                    self._occurrences,
                ),
                ProjectionStoreState(
                    self._occurrence_seal_owner,
                    "_occurrence_seals",
                    "projection_binding",
                    self._occurrence_seals,
                ),
            ),
            self._active,
            type(self._token) is ArenaToken,
        )

    @staticmethod
    def _segment_seal(
        segment: ArithmeticSegment,
    ) -> tuple[int, int, int, int, int, int, int]:
        block = segment.cylinder
        return (
            segment.start,
            block.width,
            block.residue,
            block.output,
            block.delta,
            block.minimum,
            block.parity_word,
        )

    @classmethod
    def _state_nodes(cls, state: _CursorState) -> int:
        return cls._STATE_NODES + cls._SEGMENT_SEAL_NODES * len(state.segment_seals)

    @classmethod
    def _state_seal_nodes(cls, seal: tuple[object, ...]) -> int:
        if not is_exact_object_tuple(seal):
            return cls._STATE_SEAL_NODES
        segment_seals = seal[-1]
        count = len(segment_seals) if is_exact_object_tuple(segment_seals) else 0
        return cls._STATE_SEAL_NODES + cls._SEGMENT_SEAL_NODES * count

    @staticmethod
    def _occurrence_seal(record: ProjectionOccurrence) -> tuple[object, ...]:
        block = record.block
        return (
            block.width,
            block.residue,
            block.output,
            block.delta,
            block.minimum,
            block.parity_word,
            record.start,
            record.h,
            record.balance,
            record.head,
            record.time,
            projection_key_snapshot(record.key),
            None
            if record.image is None
            else (
                record.image.source_h,
                record.image.source_balance,
                record.image.output_h,
                record.image.output_balance,
                record.image.head_delta,
                record.image.time_delta,
                record.image.classes,
            ),
        )

    @classmethod
    def _occurrence_nodes(cls, record: ProjectionOccurrence) -> int:
        return cls._OCCURRENCE_NODES + (
            0 if record.image is None else cls._CLASS_NODES * len(record.image.classes)
        )

    @classmethod
    def _occurrence_seal_nodes(cls, seal: tuple[object, ...]) -> int:
        if not is_exact_object_tuple(seal):
            return cls._OCCURRENCE_SEAL_NODES
        image = seal[-1]
        if (
            not is_exact_object_tuple(image)
            or len(image) != 7
            or not is_exact_object_tuple(image[-1])
        ):
            return cls._OCCURRENCE_SEAL_NODES
        # The occurrence owns and charges the class tuple.  Its independent
        # seal retains one reference to that same immutable tuple plus the
        # seven-field image snapshot; it does not copy every class record.
        return cls._OCCURRENCE_SEAL_NODES + 8

    @staticmethod
    def _state_seal(state: _CursorState) -> tuple[object, ...]:
        result = state.projection.result
        term = result.source_term
        term_snapshot = term.audit_snapshot()
        # ``begin`` authenticates the result and materializes this exact store
        # before the first state is sealed.  Reading the public ``segments``
        # property here used to call ``result()`` (and therefore validate every
        # retained block) twice for every seal and on each cursor transition.
        # The store identity and length are part of this independent seal, while
        # each occurrence separately seals the block it consumes.
        segments = term_snapshot.segment_store
        return (
            state.projection,
            result,
            term,
            result.source_term.engine,
            result.ledger,
            result.source_authority_is_valid,
            term_snapshot.result,
            term.segment_owner,
            segments,
            len(segments),
            term.result_owner,
            term.result_publications,
            len(term.result_publications),
            term.physical_owner,
            term.physical_publications,
            state.projection.width,
            state.projection.time_width,
            state.projection.sign,
            state.projection.time_sign,
            state.projection.modulus,
            state.projection.period,
            state.projection.max_terms,
            state.projection.cache_entries,
            result.requested,
            result.returns,
            result.h,
            result.balance,
            result.minimum,
            result.left,
            result.right,
            result.halted,
            state.segment_index,
            state.completed,
            state.h,
            state.balance,
            state.head,
            state.time,
            state.terminal,
            # This immutable field snapshot was detached exactly once at
            # ``begin``. Reusing its identity keeps state sealing constant-time;
            # the current segment is compared with its corresponding row.
            state.segment_seals,
        )

    def _state(self) -> _CursorState:
        if not self._active or len(self._states) != 1 or len(self._state_seals) != 1:
            raise RuntimeError("projection occurrence cursor is not active")
        state = self._states[0]
        if type(state) is not _CursorState:
            raise ValueError("Antihydra projection cursor state was changed")
        from number_compiler.sequences.antihydra.observers import SpaceTimeProjection

        projection = state.projection
        if type(projection) is not SpaceTimeProjection:
            raise ValueError("Antihydra projection cursor state was changed")
        result = projection.result
        if (
            type(result) is not Run
            or result.ledger is not self.ledger
            or type(result.source_term) is not AntihydraArithmeticTerm
            or result.source_term.engine is not result.source_term.engine
            or any(
                type(value) is not int
                for value in (
                    state.segment_index,
                    state.completed,
                    state.h,
                    state.balance,
                    state.head,
                    state.time,
                )
            )
            or type(state.terminal) is not bool
            or type(state.segment_seals) is not tuple
            or state.segment_index < 0
            or state.completed < 0
            or state.h < 6
            or state.balance < 0
            or state.time < 0
            or self._state_seals[0] != self._state_seal(state)
        ):
            raise ValueError("Antihydra projection cursor state was changed")
        return state

    @property
    def projection(self) -> SpaceTimeProjection | None:
        """Return the authenticated active projection, or ``None`` when idle."""
        return self._state().projection if self._active else None

    def _replace_state(self, state: _CursorState) -> None:
        prior = self._states[0]
        prior_seal = self._state_seals[0]
        seal = self._state_seal(state)
        try:
            self._states[0] = state
            self._state_seals[0] = seal
        except BaseException:
            self._states[0] = prior
            self._state_seals[0] = prior_seal
            raise

    def _invalidate_occurrence(self) -> None:
        occurrence_nodes = sum(
            self._occurrence_nodes(record) for record in self._occurrences
        )
        seal_nodes = sum(
            self._occurrence_seal_nodes(seal) for seal in self._occurrence_seals
        )
        occurrence_count = len(self._occurrences)
        seal_count = len(self._occurrence_seals)
        self._occurrences.clear()
        self._occurrence_seals.clear()
        self.ledger.release(
            self._occurrence_owner,
            entries=occurrence_count,
            nodes=occurrence_nodes,
        )
        self.ledger.release(
            self._occurrence_seal_owner,
            entries=seal_count,
            nodes=seal_nodes,
        )
        self._token = ArenaToken("antihydra-projection-occurrences")

    def _build_image(
        self,
        projection: SpaceTimeProjection,
        source_h: int,
        source_balance: int,
        block: ArithmeticCylinder,
        key: ProjectionFragmentKey,
    ) -> ProjectionBlockImage:
        h, balance = source_h, source_balance
        head = time = 0
        minimum = 0
        classes: dict[tuple[tuple[int, int], int, int], int] = {}
        spatial_phase = projection.width * (2 if projection.sign == -1 else 1)
        temporal_phase = projection.time_width * (
            2 if projection.time_sign == -1 else 1
        )
        for offset in range(block.width):
            odd = (block.parity_word >> offset) & 1
            if odd != h & 1:
                raise ValueError("retained Antihydra projection support was changed")
            translated = (
                projection.section_key(balance, h - 4),
                head % spatial_phase,
                time % temporal_phase,
            )
            copies = (classes.get(translated, 0) + 1) % projection.modulus
            if copies:
                classes[translated] = copies
            else:
                classes.pop(translated, None)
            h, balance, left, right = _ONE_STEP_ROOFS[odd].apply(h, balance)
            minimum = min(minimum, balance - source_balance)
            head += right - left
            time += right + left
            self.ledger.bump(
                _antihydra_keys.ANTIHYDRA_PROJECTION_BLOCK_IMAGE_DISCOVERY_STEPS
            )
            self.ledger.bump(
                _antihydra_keys.ANTIHYDRA_PROJECTION_BLOCK_IMAGE_OPERAND_BITS,
                h.bit_length() + balance.bit_length() + time.bit_length(),
            )
        if (
            (h, balance) != block.advance(source_h, source_balance)
            or balance - source_balance != block.delta
            or minimum != block.minimum
        ):
            raise ValueError("retained Antihydra projection support was changed")
        image = ProjectionBlockImage(
            source_h,
            source_balance,
            h,
            balance,
            head,
            time,
            tuple((*translated, copies) for translated, copies in classes.items()),
        )
        image.validate(key, block.width)
        return image

    def begin(self, projection: SpaceTimeProjection) -> None:
        """Authenticate one nonhalting run and initialize its fixed source state."""
        from number_compiler.sequences.antihydra.observers import SpaceTimeProjection

        if type(projection) is not SpaceTimeProjection:
            raise TypeError("projection cursor requires a spacetime projection")
        if self._active or self._states or self._state_seals:
            raise RuntimeError("projection occurrence cursor is already active")
        result = projection.result
        result.require_source()
        if result.halted:
            raise ValueError("halted Antihydra runs require first-failure descent")
        if result.ledger is not self.ledger:
            raise ValueError("projection occurrence belongs to another ledger")
        # The cursor seal snapshots the authenticated retained store directly.
        # Publish it once here instead of reaching through the public property
        # during every subsequent state transition.
        result.source_term.materialize_segments(result)
        segments = result.source_term.audit_snapshot().segment_store
        segment_count = len(segments)
        state_nodes = self._STATE_NODES + self._SEGMENT_SEAL_NODES * segment_count
        seal_nodes = self._STATE_SEAL_NODES + self._SEGMENT_SEAL_NODES * segment_count
        self.ledger.reserve_many(
            (
                (self._state_owner, 1, state_nodes),
                (self._state_seal_owner, 1, seal_nodes),
            )
        )
        try:
            segment_seals = tuple(self._segment_seal(segment) for segment in segments)
            state = _CursorState(projection, 0, 0, 8, 0, 1, 11, False, segment_seals)
            seal = self._state_seal(state)
            self._states.append(state)
            self._state_seals.append(seal)
        except BaseException:
            self._states.clear()
            self._state_seals.clear()
            self.ledger.release(self._state_owner, entries=1, nodes=state_nodes)
            self.ledger.release(self._state_seal_owner, entries=1, nodes=seal_nodes)
            raise
        self.ledger.bump(
            _antihydra_keys.ANTIHYDRA_PROJECTION_OCCURRENCE_SEGMENT_SEAL_ROWS,
            segment_count,
        )
        self._active = True
        self.ledger.bump(_antihydra_keys.ANTIHYDRA_PROJECTION_OCCURRENCE_CURSOR_BEGINS)

    def next(self) -> ProjectionOccurrenceID | None:
        """Issue the next exact occurrence and advance the private cursor once."""
        state = self._state()
        self._invalidate_occurrence()
        term = state.projection.result.source_term
        segments = term.audit_snapshot().segment_store
        if state.segment_index == len(segments):
            if not state.terminal:
                self._replace_state(
                    _CursorState(
                        state.projection,
                        state.segment_index,
                        state.completed,
                        state.h,
                        state.balance,
                        state.head,
                        state.time,
                        True,
                        state.segment_seals,
                    )
                )
                self.ledger.bump(
                    _antihydra_keys.ANTIHYDRA_PROJECTION_OCCURRENCE_TERMINAL_STEPS
                )
            return None
        if not 0 <= state.segment_index < len(segments):
            raise ValueError("projection cursor has another segment position")
        segment = segments[state.segment_index]
        if type(segment) is not ArithmeticSegment or type(segment.start) is not int:
            raise ValueError("retained Antihydra projection support was changed")
        block = segment.cylinder
        if (
            type(block) is not ArithmeticCylinder
            or segment.start != state.completed
            or self._segment_seal(segment) != state.segment_seals[state.segment_index]
        ):
            raise ValueError("retained Antihydra projection support was changed")
        block.__post_init__()
        self.ledger.bump(
            _antihydra_keys.ANTIHYDRA_PROJECTION_OCCURRENCE_VALIDATION_STEPS,
            block.width,
        )
        if (
            block.residue != state.h % (1 << block.width)
            or state.balance + block.minimum < 0
        ):
            raise ValueError("retained Antihydra projection support was changed")
        key = state.projection.fragment_key(
            block,
            state.completed,
            state.head,
            state.time,
        )
        expected_key = ProjectionFragmentKey(
            term.segment_owner,
            state.projection.result.requested,
            state.completed,
            (
                block.width,
                block.residue,
                block.output,
                block.delta,
                block.minimum,
                block.parity_word,
            ),
            state.projection.width,
            state.projection.time_width,
            state.projection.sign,
            state.projection.time_sign,
            state.projection.modulus,
            state.head
            % (state.projection.width * (2 if state.projection.sign == -1 else 1)),
            state.time
            % (
                state.projection.time_width
                * (2 if state.projection.time_sign == -1 else 1)
            ),
        )
        if key != expected_key:
            raise ValueError("projection occurrence key has another source binding")
        occurrence = ProjectionOccurrence(
            block,
            state.completed,
            state.h,
            state.balance,
            state.head,
            state.time,
            key,
        )
        self.ledger.bump(
            _antihydra_keys.ANTIHYDRA_PROJECTION_OCCURRENCE_ROOF_STEPS, block.width
        )
        self.ledger.bump(
            _antihydra_keys.ANTIHYDRA_PROJECTION_OCCURRENCE_OPERAND_BITS,
            state.h.bit_length()
            + state.balance.bit_length()
            + state.head.bit_length()
            + state.time.bit_length(),
        )
        roof = physical_roof(block)
        output_h, output_balance, left, right = roof.apply(state.h, state.balance)
        following = _CursorState(
            state.projection,
            state.segment_index + 1,
            state.completed + block.width,
            output_h,
            output_balance,
            state.head + right - left,
            state.time + right + left,
            False,
            state.segment_seals,
        )
        occurrence_nodes = self._occurrence_nodes(occurrence)
        occurrence_seal = self._occurrence_seal(occurrence)
        seal_nodes = self._occurrence_seal_nodes(occurrence_seal)
        self.ledger.reserve_many(
            (
                (self._occurrence_owner, 1, occurrence_nodes),
                (self._occurrence_seal_owner, 1, seal_nodes),
            )
        )
        try:
            self._occurrences.append(occurrence)
            self._occurrence_seals.append(occurrence_seal)
            self._replace_state(following)
        except BaseException:
            self._occurrences.clear()
            self._occurrence_seals.clear()
            self.ledger.release(
                self._occurrence_owner, entries=1, nodes=occurrence_nodes
            )
            self.ledger.release(
                self._occurrence_seal_owner,
                entries=1,
                nodes=seal_nodes,
            )
            raise
        self.ledger.bump(_antihydra_keys.ANTIHYDRA_PROJECTION_OCCURRENCE_STEPS)
        return ProjectionOccurrenceID(self._token, self._KIND, 0)

    def materialize_image(
        self, reference: ProjectionOccurrenceID
    ) -> ProjectionOccurrence:
        """Discover and retain the sparse block image only for a cache miss."""
        record = self.resolve(reference)
        if record.image is not None:
            return record
        projection = self._state().projection
        image = self._build_image(
            projection,
            record.h,
            record.balance,
            record.block,
            record.key,
        )
        replacement = ProjectionOccurrence(
            record.block,
            record.start,
            record.h,
            record.balance,
            record.head,
            record.time,
            record.key,
            image,
        )
        old_nodes = self._occurrence_nodes(record)
        new_nodes = self._occurrence_nodes(replacement)
        old_seal = self._occurrence_seals[0]
        new_seal = self._occurrence_seal(replacement)
        old_seal_nodes = self._occurrence_seal_nodes(old_seal)
        new_seal_nodes = self._occurrence_seal_nodes(new_seal)
        additions = (
            (self._occurrence_owner, 0, new_nodes - old_nodes),
            (self._occurrence_seal_owner, 0, new_seal_nodes - old_seal_nodes),
        )
        self.ledger.reserve_many(additions)
        try:
            self._occurrences[0] = replacement
            self._occurrence_seals[0] = new_seal
        except BaseException:
            self._occurrences[0] = record
            self._occurrence_seals[0] = old_seal
            for owner, entries, nodes in additions:
                self.ledger.release(owner, entries=entries, nodes=nodes)
            raise
        self.ledger.bump(_antihydra_keys.ANTIHYDRA_PROJECTION_BLOCK_IMAGE_PUBLICATIONS)
        return replacement

    def resolve(self, reference: ProjectionOccurrenceID) -> ProjectionOccurrence:
        """Resolve only the current generation's independently sealed occurrence."""
        if type(reference) is not ProjectionOccurrenceID:
            raise TypeError("expected an Antihydra projection occurrence ID")
        state = self._state()
        reference.validate(self._token, self._KIND, size=len(self._occurrences))
        if len(self._occurrences) != 1 or len(self._occurrence_seals) != 1:
            raise ValueError("projection occurrence authority is inactive")
        record = self._occurrences[0]
        if type(record) is not ProjectionOccurrence:
            raise ValueError("Antihydra projection occurrence was changed")
        source_index = state.segment_index - 1
        segments = state.projection.result.source_term.audit_snapshot().segment_store
        if (
            not 0 <= source_index < len(segments)
            or segments[source_index].cylinder is not record.block
            or self._segment_seal(segments[source_index])
            != state.segment_seals[source_index]
        ):
            raise ValueError("retained Antihydra arithmetic support was changed")
        try:
            record.__post_init__()
        except (TypeError, ValueError) as error:
            raise ValueError("Antihydra projection occurrence was changed") from error
        if self._occurrence_seals[0] != self._occurrence_seal(record):
            raise ValueError("Antihydra projection occurrence was changed")
        return record

    def finish(self) -> None:
        """Require complete consumption and the authenticated physical endpoint."""
        state = self._state()
        result = state.projection.result
        result.require_source()
        if (
            not state.terminal
            or state.segment_index
            != len(result.source_term.audit_snapshot().segment_store)
            or (
                state.completed,
                state.h,
                state.balance,
                state.head,
                state.time,
            )
            != (
                result.returns,
                result.h,
                result.balance,
                result.head,
                result.physical_ticks,
            )
        ):
            raise ArithmeticError("projection occurrence cursor diverged from its run")
        self.ledger.bump(
            _antihydra_keys.ANTIHYDRA_PROJECTION_OCCURRENCE_CURSOR_FINISHES
        )

    def clear(self) -> None:
        """Revoke the active generation and release every transient record."""
        self._invalidate_occurrence()
        state_count = len(self._states)
        seal_count = len(self._state_seals)
        state_nodes = sum(self._state_nodes(state) for state in self._states)
        seal_nodes = sum(self._state_seal_nodes(seal) for seal in self._state_seals)
        self._states.clear()
        self._state_seals.clear()
        self.ledger.release(
            self._state_owner,
            entries=state_count,
            nodes=state_nodes,
        )
        self.ledger.release(
            self._state_seal_owner,
            entries=seal_count,
            nodes=seal_nodes,
        )
        self._active = False
        self.ledger.bump(_antihydra_keys.ANTIHYDRA_PROJECTION_OCCURRENCE_CURSOR_CLEARS)


__all__ = [
    "ProjectionBlockImage",
    "ProjectionOccurrence",
    "ProjectionOccurrenceCursor",
    "ProjectionOccurrenceID",
]
