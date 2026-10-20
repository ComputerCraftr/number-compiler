"""Budgeted Moore quotients for guarded Collatz innovation observers.

These finite machines describe observer output only.  Their IDs cannot
authorize an endpoint, width, source transport, or safety action.  Every
constructed table belongs to the caller's query-local
``InnovationObserverMemo``; no process-global cache retains a source table.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.functions.finite_observer import (
    minimize_finite_observer,
    partition_representatives,
    refine_observer_partition,
)
from number_compiler.sequences.collatz.border_identity import (
    ENTRY_89_AT_NINE,
    ENTRY_421,
    ENTRY_4721,
    PATH_630,
    CycleEntryPhase,
    GuardedBorderPath,
)
from number_compiler.sequences.collatz.innovation_temporal_tape import (
    InnovationCoreIdentity,
    InnovationObserverMemo,
    innovation_moore_clock,
)

_INNOVATION_CORES: tuple[InnovationCoreIdentity, ...] = (
    ENTRY_421,
    ENTRY_4721,
    PATH_630,
    ENTRY_89_AT_NINE,
)
_ISSUED_FUTURE = object()
_UNISSUED = object()


def _check_memo(memo: InnovationObserverMemo | None) -> None:
    if memo is not None:
        if type(memo) is not InnovationObserverMemo:
            raise TypeError("innovation future memo must be query-owned")
        memo.check_open()


@dataclass(frozen=True, slots=True)
class GuardedInnovationFutureMoore:
    """Complete observer control graph and stable horizon for one modulus."""

    modulus: int
    local_to_global: tuple[tuple[int, ...], ...]
    global_outputs: tuple[tuple[str, ...], ...]
    global_successors: tuple[int, ...]
    global_representatives: tuple[int, ...]
    local_offsets: tuple[int, ...]
    local_states: tuple[tuple[InnovationCoreIdentity, int], ...]
    stabilization_horizon: int
    _authority: object = field(default=_UNISSUED, init=False, repr=False, compare=False)
    _seal: tuple[object, ...] = field(default=(), init=False, repr=False, compare=False)

    @property
    def producer_issued(self) -> bool:
        seal = self._seal
        return (
            self._authority is _ISSUED_FUTURE
            and len(seal) == 8
            and type(self.modulus) is int
            and type(self.stabilization_horizon) is int
            and type(seal[0]) is int
            and type(seal[7]) is int
            and seal[0] == self.modulus
            and self.local_to_global is seal[1]
            and self.global_outputs is seal[2]
            and self.global_successors is seal[3]
            and self.global_representatives is seal[4]
            and self.local_offsets is seal[5]
            and self.local_states is seal[6]
            and seal[7] == self.stabilization_horizon
        )

    def _check_issued(self) -> None:
        if not self.producer_issued:
            raise ValueError(
                "innovation future graph was not issued by its constructor"
            )

    @property
    def class_count(self) -> int:
        return len(self.global_outputs)

    @property
    def disjoint_class_count(self) -> int:
        return len(self.local_states)

    def _identity_index(self, identity: InnovationCoreIdentity) -> int:
        if type(identity) not in (CycleEntryPhase, GuardedBorderPath):
            raise TypeError("guarded Collatz clock requires a typed border identity")
        try:
            return _INNOVATION_CORES.index(identity)
        except ValueError as error:
            raise ValueError("unknown guarded Collatz border identity") from error

    def global_id(
        self,
        identity: InnovationCoreIdentity,
        phase: int,
        *,
        memo: InnovationObserverMemo | None = None,
    ) -> int:
        self._check_issued()
        phase = require_integer(phase, "innovation phase")
        _check_memo(memo)
        k = self._identity_index(identity)
        local = innovation_moore_clock(identity, self.modulus, memo=memo).class_id(
            phase
        )
        return self.local_to_global[k][local]

    def _finite_partition(
        self, returns: int, memo: InnovationObserverMemo | None
    ) -> tuple[int, ...]:
        self._check_issued()
        _check_memo(memo)
        horizon = min(returns, self.stabilization_horizon)
        key = (self.modulus, horizon)

        def build() -> tuple[int, ...]:
            # Horizon zero has no observed outputs, so every control agrees.
            # Each positive round then uses the shared one-step partition
            # operator over this already minimized graph.
            labels = (0,) * len(self.global_outputs)
            rows = tuple((target,) for target in self.global_successors)
            for _ in range(horizon):
                labels = refine_observer_partition(rows, self.global_outputs, labels)
                if memo is not None:
                    memo.note_refinement(len(labels))
            return labels

        if memo is None:
            return build()
        return memo.get_or_build(
            "finite-partition",
            key,
            build,
            work_nodes=max(1, 24 * len(self.global_outputs)),
        )

    def finite_id(
        self,
        identity: InnovationCoreIdentity,
        phase: int,
        returns: int,
        *,
        memo: InnovationObserverMemo | None = None,
    ) -> int:
        self._check_issued()
        phase = require_integer(phase, "innovation phase")
        returns = require_integer(returns, "finite Moore horizon", 0)
        _check_memo(memo)
        k = self._identity_index(identity)
        local = innovation_moore_clock(identity, self.modulus, memo=memo).class_id(
            phase
        )
        labels = self._finite_partition(returns, memo)
        return labels[self.local_to_global[k][local]]

    def finite_count(
        self,
        returns: int,
        *,
        memo: InnovationObserverMemo | None = None,
    ) -> int:
        self._check_issued()
        returns = require_integer(returns, "finite Moore horizon", 0)
        _check_memo(memo)
        labels = self._finite_partition(returns, memo)
        return max(labels, default=0) + 1

    def successor(self, control_id: int) -> int:
        self._check_issued()
        if type(control_id) is not int or not 0 <= control_id < self.class_count:
            raise ValueError("Moore control ID is not in the certified alphabet")
        return self.global_successors[control_id]

    def advance(
        self,
        control_id: int,
        returns: int,
        *,
        memo: InnovationObserverMemo | None = None,
    ) -> int:
        """Advance a canonical phase in bounded orbit time, not O(returns)."""
        self._check_issued()
        control_id = require_integer(control_id, "Moore control ID", 0)
        returns = require_integer(returns, "Moore return count", 0)
        _check_memo(memo)
        from number_compiler.sequences.collatz.innovation_temporal_tape import (
            global_class_orbit,
        )

        orbit = global_class_orbit(self.modulus, control_id, memo=memo)
        if returns < len(orbit.ids):
            return orbit.ids[returns]
        return orbit.ids[orbit.prefix + (returns - orbit.prefix) % orbit.period]

    def finite_representative(
        self,
        returns: int,
        control_id: int,
        *,
        memo: InnovationObserverMemo | None = None,
    ) -> int:
        """Return a global representative of an exact h-motif class."""
        self._check_issued()
        returns = require_integer(returns, "finite Moore horizon", 0)
        control_id = require_integer(control_id, "finite Moore control ID", 0)
        _check_memo(memo)
        labels = self._finite_partition(returns, memo)
        if control_id > max(labels):
            raise ValueError("unrecognized finite Moore control ID")
        return labels.index(control_id)


def innovation_future_moore(
    modulus: int,
    *,
    memo: InnovationObserverMemo | None = None,
) -> GuardedInnovationFutureMoore:
    """Minimize all four exact modular core machines at this modulus.

    The refinement retains only the current and next partition.  Finite
    horizon partitions are computed on demand and memoized in the same
    query-owned store, avoiding the former state-by-depth matrix.
    """

    modulus = require_integer(modulus, "innovation future modulus", 3, 4096)
    if modulus % 2 == 0:
        raise ValueError("innovation future modulus must be odd")
    _check_memo(memo)

    def build() -> GuardedInnovationFutureMoore:
        clocks = tuple(
            innovation_moore_clock(identity, modulus, memo=memo)
            for identity in _INNOVATION_CORES
        )
        states = tuple(
            (identity, local)
            for identity, clock in zip(_INNOVATION_CORES, clocks, strict=True)
            for local in range(clock.class_count)
        )
        offsets: list[int] = []
        cursor = 0
        for clock in clocks:
            offsets.append(cursor)
            cursor += clock.class_count
        output = tuple(
            clocks[_INNOVATION_CORES.index(identity)].outputs[local]
            for identity, local in states
        )
        successors = tuple(
            offsets[_INNOVATION_CORES.index(identity)]
            + clocks[_INNOVATION_CORES.index(identity)].successors[local]
            for identity, local in states
        )

        minimized = minimize_finite_observer(
            tuple((target,) for target in successors),
            output,
            on_refinement=(None if memo is None else memo.note_refinement),
        )
        labels = minimized.class_ids
        representatives = partition_representatives(labels, minimized.classes)
        stabilization = minimized.rounds
        class_output = tuple(output[i] for i in representatives)
        class_successors = tuple(labels[successors[i]] for i in representatives)
        local_to_global = tuple(
            tuple(labels[offsets[k] + j] for j in range(clock.class_count))
            for k, clock in enumerate(clocks)
        )
        graph = GuardedInnovationFutureMoore(
            modulus,
            local_to_global,
            class_output,
            class_successors,
            representatives,
            tuple(offsets),
            states,
            stabilization,
        )
        for i, state_pair in enumerate(states):
            class_id = labels[i]
            if (
                class_output[class_id] != output[i]
                or class_successors[class_id] != labels[successors[i]]
            ):
                raise AssertionError(
                    f"noncongruent innovation quotient at {state_pair}"
                )
        object.__setattr__(graph, "_authority", _ISSUED_FUTURE)
        object.__setattr__(
            graph,
            "_seal",
            (
                modulus,
                graph.local_to_global,
                graph.global_outputs,
                graph.global_successors,
                graph.global_representatives,
                graph.local_offsets,
                graph.local_states,
                stabilization,
            ),
        )
        return graph

    if memo is None:
        graph = build()
    else:
        # At most four unminimized phase sets enter this constructor. Refuse
        # before allocating refinement dictionaries without a linear scratch
        # envelope.
        graph = memo.get_or_build(
            "future-moore",
            (modulus,),
            build,
            work_nodes=max(1, 24 * 4 * modulus),
        )
    if (
        type(graph) is not GuardedInnovationFutureMoore
        or not graph.producer_issued
        or graph.modulus != modulus
    ):
        raise ValueError("innovation future memo returned a foreign quotient")
    return graph


__all__ = ["GuardedInnovationFutureMoore", "innovation_future_moore"]
