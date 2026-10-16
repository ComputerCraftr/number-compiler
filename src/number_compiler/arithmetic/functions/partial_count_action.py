"""Conditional finite actions with additive observations and explicit refusal.

These values describe a declared finite language, not a physical source
certificate. Family publishers own inlet admission. Universe identity prevents
combining unrelated minimized graphs whose local integer labels happen to agree.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.morphism_core import binary_power

MAX_ACTION_PAYLOAD_BYTES = 32 * 1024 * 1024
MAX_POWER_SCALAR_OPERATIONS = 16 * 1024 * 1024


def _count_payload_bytes(
    counts: tuple[tuple[int, ...] | None, ...], extra_bits: int = 0
) -> int:
    return (
        64
        + 48 * len(counts)
        + sum(
            40 + sum(36 + (value.bit_length() + extra_bits + 7) // 8 for value in row)
            for row in counts
            if row is not None
        )
    )


@dataclass(frozen=True, slots=True, eq=False)
class ActionUniverse:
    states: int
    channels: int

    def __post_init__(self) -> None:
        if (
            type(self.states) is not int
            or type(self.channels) is not int
            or not 1 <= self.states <= 65_536
            or not 0 <= self.channels <= 256
            or self.states * max(1, self.channels) > 1_048_576
        ):
            raise ValueError("conditional action universe exceeds its finite budget")


@dataclass(frozen=True, slots=True)
class PartialCountAction:
    steps: int
    targets: tuple[int | None, ...]
    counts: tuple[tuple[int, ...] | None, ...]
    owner: ActionUniverse

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.owner) is not ActionUniverse:
            raise TypeError("conditional action requires its typed universe")
        self.owner.__post_init__()
        if (
            type(self.steps) is not int
            or self.steps < 0
            or self.steps.bit_length() > 65_536
            or type(self.targets) is not tuple
            or type(self.counts) is not tuple
            or len(self.targets) != self.owner.states
            or len(self.counts) != self.owner.states
        ):
            raise ValueError("malformed conditional action shape or duration")
        for target, count in zip(self.targets, self.counts, strict=True):
            if (target is None) != (count is None):
                raise ValueError("refused conditional action has an emission")
            if target is not None and (
                type(target) is not int or not 0 <= target < self.owner.states
            ):
                raise ValueError("conditional target leaves its universe")
            if count is not None and (
                type(count) is not tuple
                or len(count) != self.owner.channels
                or any(type(value) is not int or value < 0 for value in count)
                or any(value.bit_length() > 65_536 for value in count)
            ):
                raise ValueError("invalid conditional action observation vector")
        if _count_payload_bytes(self.counts) > MAX_ACTION_PAYLOAD_BYTES:
            raise ValueError("conditional action payload exceeds its allocation budget")

    @classmethod
    def identity(cls, owner: ActionUniverse) -> PartialCountAction:
        if type(owner) is not ActionUniverse:
            raise TypeError("conditional identity requires its typed universe")
        owner.__post_init__()
        return cls(
            0,
            tuple(range(owner.states)),
            ((0,) * owner.channels,) * owner.states,
            owner,
        )

    def then(self, after: PartialCountAction) -> PartialCountAction:
        self.validate()
        if type(after) is not PartialCountAction:
            raise TypeError("conditional composition requires another action")
        after.validate()
        if self.owner is not after.owner:
            raise ValueError("conditional actions belong to different universes")
        duration = self.steps + after.steps
        if duration.bit_length() > 65_536:
            raise ValueError("conditional composition exceeds its duration budget")
        bits = max(self._max_count_bits(), after._max_count_bits()) + 1
        self._preflight_uniform_payload(bits)
        targets: list[int | None] = []
        counts: list[tuple[int, ...] | None] = []
        for target, count in zip(self.targets, self.counts, strict=True):
            later = None if target is None else after.targets[target]
            emission = None if target is None else after.counts[target]
            if later is None or count is None or emission is None:
                targets.append(None)
                counts.append(None)
            else:
                targets.append(later)
                counts.append(
                    tuple(a + b for a, b in zip(count, emission, strict=True))
                )
        return PartialCountAction(duration, tuple(targets), tuple(counts), self.owner)

    def _max_count_bits(self) -> int:
        return max(
            (
                value.bit_length()
                for row in self.counts
                if row is not None
                for value in row
            ),
            default=0,
        )

    def _preflight_uniform_payload(self, count_bits: int) -> None:
        # Every receiver can reach the largest count row. Include tuple slots,
        # integer objects, target references and both top-level containers.
        per_state = 88 + self.owner.channels * (36 + (count_bits + 7) // 8)
        if 64 + self.owner.states * per_state > MAX_ACTION_PAYLOAD_BYTES:
            raise ValueError("conditional composition exceeds its allocation budget")

    def power(self, repetitions: int) -> PartialCountAction:
        self.validate()
        if (
            type(repetitions) is not int
            or repetitions < 0
            or repetitions.bit_length() > 65_536
        ):
            raise ValueError("conditional repetition exceeds its exponent budget")
        if (self.steps * repetitions).bit_length() > 65_536:
            raise ValueError("conditional repetition exceeds its duration budget")
        bits = repetitions.bit_length()
        self._preflight_uniform_payload(self._max_count_bits() + bits)
        if (
            2 * bits * self.owner.states * max(1, self.owner.channels)
            > MAX_POWER_SCALAR_OPERATIONS
            or _count_payload_bytes(self.counts, bits) > MAX_ACTION_PAYLOAD_BYTES
        ):
            raise ValueError(
                "conditional repetition exceeds its work or allocation budget"
            )
        return binary_power(
            self,
            repetitions,
            identity=self.identity(self.owner),
            compose=PartialCountAction.then,
        ).value
