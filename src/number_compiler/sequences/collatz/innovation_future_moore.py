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
from number_compiler.sequences.collatz.innovation_temporal_tape import (
    InnovationObserverMemo,
    innovation_moore_clock,
)

_FAMILIES = ("421", "4721", "630", "989")
_ISSUED_FUTURE = object()
_UNISSUED = object()


def _check_memo(memo: InnovationObserverMemo | None) -> None:
    if memo is not None:
        if type(memo) is not InnovationObserverMemo:
            raise TypeError("innovation future memo must be query-owned")
        memo._check_open()


@dataclass(frozen=True, slots=True)
class GuardedInnovationFutureMoore:
    """Complete observer control graph and stable horizon for one modulus."""

    modulus: int
    local_to_global: tuple[tuple[int, ...], ...]
    global_outputs: tuple[tuple[str, ...], ...]
    global_successors: tuple[int, ...]
    global_representatives: tuple[int, ...]
    local_offsets: tuple[int, ...]
    local_states: tuple[tuple[str, int], ...]
    stabilization_horizon: int
    _authority: object = field(default=_UNISSUED, init=False, repr=False, compare=False)

    def _check_issued(self) -> None:
        if self._authority is not _ISSUED_FUTURE:
            raise ValueError(
                "innovation future graph was not issued by its constructor"
            )

    @property
    def class_count(self) -> int:
        return len(self.global_outputs)

    @property
    def disjoint_class_count(self) -> int:
        return len(self.local_states)

    def _family_index(self, family: str) -> int:
        if type(family) is not str:
            raise TypeError("guarded Collatz family must be a string")
        try:
            return _FAMILIES.index(family)
        except ValueError as error:
            raise ValueError("unknown guarded Collatz family") from error

    def global_id(
        self,
        family: str,
        phase: int,
        *,
        memo: InnovationObserverMemo | None = None,
    ) -> int:
        self._check_issued()
        phase = require_integer(phase, "innovation phase")
        _check_memo(memo)
        k = self._family_index(family)
        local = innovation_moore_clock(family, self.modulus, memo=memo).class_id(phase)
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
        return memo._get_or_build(
            "finite-partition",
            key,
            build,
            work_nodes=max(1, 24 * len(self.global_outputs)),
        )

    def finite_id(
        self,
        family: str,
        phase: int,
        returns: int,
        *,
        memo: InnovationObserverMemo | None = None,
    ) -> int:
        self._check_issued()
        phase = require_integer(phase, "innovation phase")
        returns = require_integer(returns, "finite Moore horizon", 0)
        _check_memo(memo)
        k = self._family_index(family)
        local = innovation_moore_clock(family, self.modulus, memo=memo).class_id(phase)
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
            _global_class_orbit,
        )

        orbit = _global_class_orbit(self.modulus, control_id, memo=memo)
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
            innovation_moore_clock(family, modulus, memo=memo) for family in _FAMILIES
        )
        states = tuple(
            (family, local)
            for family, clock in zip(_FAMILIES, clocks, strict=True)
            for local in range(clock.class_count)
        )
        offsets: list[int] = []
        cursor = 0
        for clock in clocks:
            offsets.append(cursor)
            cursor += clock.class_count
        output = tuple(
            clocks[_FAMILIES.index(family)].outputs[local] for family, local in states
        )
        successors = tuple(
            offsets[_FAMILIES.index(family)]
            + clocks[_FAMILIES.index(family)].successors[local]
            for family, local in states
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
        return graph

    if memo is None:
        return build()
    # At most four unminimized phase sets enter this constructor. Refuse before
    # allocating its refinement dictionaries if the caller's ledger cannot
    # admit a conservative linear scratch envelope.
    return memo._get_or_build(
        "future-moore",
        (modulus,),
        build,
        work_nodes=max(1, 24 * 4 * modulus),
    )


__all__ = ["GuardedInnovationFutureMoore", "innovation_future_moore"]
