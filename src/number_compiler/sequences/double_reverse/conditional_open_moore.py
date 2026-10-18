"""Complete-future Moore quotient of a 2rev10 open digit bank.

The finite ring does NOT wrap: every neighbour missing from a bounded pair
window is a typed input. All declared ingress alternatives are expanded to
closure before Moore refinement, including their conditional borrow outputs.

This model is a reusable algebra of *conditional* actions. A source-issued
spacetime cylinder must separately certify its actual inlet CONCAT/REPEAT
word before a powered action may publish observations about an integer.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass

from number_compiler.arithmetic.functions.finite_observer import (
    class_members,
    partition_by_signature,
    partition_quotient_rows,
    refine_observer_partition,
)
from number_compiler.arithmetic.functions.partial_count_action import (
    ActionUniverse,
    PartialCountAction,
)

from .open_temporal_ring import OpenRingPorts, OpenRingState
from .protected_temporal_bank import PERIODIC_CHANNELS, PeriodicBankFrame
from .temporal_bank_output_morphism import _row_output_label

MAX_OPEN_MOORE_STATES = 4096
MAX_OPEN_MOORE_LETTERS = 4096
MAX_OPEN_MOORE_TRANSITIONS = 1_048_576


class ConditionalOpenMooreBudgetExceeded(ValueError):
    """The finite conditional state graph exceeds its declared work budget."""


def _counts(frames: tuple[PeriodicBankFrame, ...]) -> tuple[int, ...]:
    return tuple(
        sum(frame.scalar(channel) for frame in frames) for channel in PERIODIC_CHANNELS
    )


OpenPortAction = PartialCountAction


@dataclass(frozen=True, slots=True)
class ConditionalOpenMoore:
    """Coarsest complete-future input-driven bank action on a closed graph."""

    alphabet: tuple[OpenRingPorts, ...]
    class_ids: tuple[int, ...]
    class_count: int
    initial_class: int
    transitions: tuple[tuple[int | None, ...], ...]
    emissions: tuple[tuple[tuple[PeriodicBankFrame, ...] | None, ...], ...]
    input_phases: int
    owner: ActionUniverse

    def letter(self, port: OpenRingPorts) -> OpenPortAction:
        try:
            i = self.alphabet.index(port)
        except ValueError as exc:
            raise ValueError("unadmitted open temporal ingress letter") from exc
        emitted_rows: list[tuple[int, ...] | None] = []
        for row in self.emissions:
            emitted = row[i]
            emitted_rows.append(None if emitted is None else _counts(emitted))
        return PartialCountAction(
            1,
            tuple(row[i] for row in self.transitions),
            tuple(emitted_rows),
            self.owner,
        )

    def word(self, letters: tuple[OpenRingPorts, ...]) -> OpenPortAction:
        result = PartialCountAction.identity(self.owner)
        for letter in letters:
            result = result.then(self.letter(letter))
        return result

    def repeat_program(
        self,
        motif: tuple[OpenRingPorts, ...],
        repeats: int,
        *,
        prefix: tuple[OpenRingPorts, ...] = (),
        suffix: tuple[OpenRingPorts, ...] = (),
    ) -> tuple[int, dict[str, int]]:
        """Evaluate an already-authorized CONCAT/REPEAT inlet program."""
        action = (
            self.word(prefix)
            .then(self.word(motif).power(repeats))
            .then(self.word(suffix))
        )
        target = action.targets[self.initial_class]
        values = action.counts[self.initial_class]
        if target is None or values is None:
            raise ValueError("input program violates a guarded Moore transition")
        return target, dict(zip(PERIODIC_CHANNELS, values, strict=True))


def minimize_conditional_open_ring(
    initial: OpenRingState,
    allowed_by_phase: tuple[tuple[OpenRingPorts, ...], ...],
    *,
    max_states: int = MAX_OPEN_MOORE_STATES,
) -> ConditionalOpenMoore:
    """Enumerate *all* admitted inlet choices, then minimize future outputs.

    `allowed_by_phase` is a DECLARED LANGUAGE, not an inferred arithmetic
    theorem. The producer must certify the source's inlet program separately.
    A budget exhaustion refuses; it never equates unexplored states.
    """
    if (
        type(initial) is not OpenRingState
        or type(allowed_by_phase) is not tuple
        or not allowed_by_phase
        or len(allowed_by_phase) > MAX_OPEN_MOORE_LETTERS
        or type(max_states) is not int
        or not 1 <= max_states <= MAX_OPEN_MOORE_STATES
    ):
        raise ValueError("conditional ring requires finite nonempty input domains")
    declared_letters = 0
    for phase in allowed_by_phase:
        if type(phase) is not tuple or not phase:
            raise ValueError("conditional ring input phases must be nonempty tuples")
        declared_letters += len(phase)
        if any(type(letter) is not OpenRingPorts for letter in phase):
            raise ValueError("conditional ring input phase contains an invalid port")
        if declared_letters > MAX_OPEN_MOORE_LETTERS:
            raise ValueError("conditional ring input alphabet exceeds its budget")
    if max_states * declared_letters > MAX_OPEN_MOORE_TRANSITIONS:
        raise ConditionalOpenMooreBudgetExceeded(
            "conditional ring transition graph exceeds its budget"
        )
    alphabet = tuple(
        sorted({letter for phase in allowed_by_phase for letter in phase}, key=repr)
    )
    allowed = tuple(frozenset(phase) for phase in allowed_by_phase)
    initial_node = (initial, 0)
    states: list[tuple[OpenRingState, int]] = [initial_node]
    ids: dict[tuple[OpenRingState, int], int] = {initial_node: 0}
    queue: deque[tuple[OpenRingState, int]] = deque((initial_node,))
    transitions: list[tuple[int | None, ...]] = []
    emissions: list[tuple[tuple[PeriodicBankFrame, ...] | None, ...]] = []
    while queue:
        state, input_phase = queue.popleft()
        current = ids[(state, input_phase)]
        if current != len(transitions):
            raise AssertionError("open-ring BFS lost its ordered state frontier")
        row: list[int | None] = []
        out: list[tuple[PeriodicBankFrame, ...] | None] = []
        for port in alphabet:
            if port not in allowed[input_phase]:
                row.append(None)
                out.append(None)
                continue
            target_state, frame = state.advance(port)
            key = (target_state, (input_phase + 1) % len(allowed))
            target = ids.get(key)
            if target is None:
                if len(states) >= max_states:
                    raise ConditionalOpenMooreBudgetExceeded(
                        "conditional open-ring state universe did not close "
                        "within budget"
                    )
                target = len(states)
                ids[key] = target
                states.append(key)
                queue.append(key)
            row.append(target)
            out.append(frame)
        transitions.append(tuple(row))
        emissions.append(tuple(out))
    rows = tuple(transitions)
    outputs = tuple(emissions)
    signature = tuple(
        tuple(None if output is None else _row_output_label(output) for output in row)
        for row in outputs
    )
    classes = partition_by_signature(signature)
    # Output-aware Moore refinement over every declared input, including
    # forbidden slots. This is *not* minimization of 10 local digit values.
    for _ in range(len(rows) + 1):
        updated = refine_observer_partition(rows, signature, classes)
        if updated == classes:
            break
        classes = updated
    else:
        raise AssertionError("open-ring future partition did not stabilize")
    class_count = max(classes) + 1
    quotient_rows = partition_quotient_rows(rows, classes, class_count)
    groups = class_members(classes, class_count)
    quotient_emissions: list[tuple[tuple[PeriodicBankFrame, ...] | None, ...]] = []
    for group in groups:
        first = outputs[group[0]]
        if any(outputs[s] != first for s in group[1:]):
            raise AssertionError("open-ring Moore class changes an admitted output")
        quotient_emissions.append(first)
    return ConditionalOpenMoore(
        alphabet,
        classes,
        class_count,
        classes[0],
        quotient_rows,
        tuple(quotient_emissions),
        len(allowed),
        ActionUniverse(class_count, len(PERIODIC_CHANNELS)),
    )


__all__ = [
    "ConditionalOpenMoore",
    "ConditionalOpenMooreBudgetExceeded",
    "OpenPortAction",
    "minimize_conditional_open_ring",
]
