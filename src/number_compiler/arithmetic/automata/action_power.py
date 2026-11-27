"""Scoped monoid powering with private integer cache keys.

The composition callback owns semantic interning.  This layer never observes
fields, tails, slabs, or endpoints and makes no assumption that discovering a
nonlinear branch schedule has logarithmic cost.
"""

from collections.abc import Callable
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
)


@dataclass(frozen=True, slots=True)
class ActionPowerMetrics:
    composition_requests: int
    composition_hits: int
    composition_entries: int
    power_requests: int
    power_hits: int
    power_entries: int


class ActionPowerArena:
    """Compose and square canonical actions in chronological order.

    ``compose(before, after)`` denotes ``after ∘ before``.  IDs belong to the
    callback's arena and are validated before lookup or identity shortcuts.
    Exact source-to-endpoint memoization belongs to the application owner.
    """

    def __init__(
        self,
        identity: ActionProgramID,
        compose: Callable[[ActionProgramID, ActionProgramID], ActionProgramID],
        *,
        validate: Callable[[ActionProgramID], int],
        memoize_compositions: bool = True,
    ) -> None:
        if type(identity) is not ActionProgramID:
            raise TypeError("action powering requires a scoped program ID")
        self._owner = identity.owner
        self._kind = identity.kind
        self.resolve_index = validate
        self._identity_id = self._validate(identity)
        self._compose = compose
        # An already memoized interner keeps its own arena-local keys.
        self._compositions: dict[tuple[int, int], int] | None = (
            {} if memoize_compositions else None
        )
        self._powers: dict[tuple[int, int], int] = {}
        self.composition_requests = 0
        self.composition_hits = 0
        self.power_requests = 0
        self.power_hits = 0

    @property
    def identity(self) -> ActionProgramID:
        return ActionProgramID(self._owner, self._kind, self._identity_id)

    def _validate(self, handle: ActionProgramID) -> int:
        if type(handle) is not ActionProgramID:
            raise TypeError("action powering requires a scoped program ID")
        ArenaHandle.validate(handle, self._owner, self._kind)
        result = self.resolve_index(handle)
        if type(result) is not int or result != handle.local_id:
            raise ValueError("action resolver returned a different local identity")
        return result

    def scoped_handle(self, local_id: int) -> ActionProgramID:
        result = ActionProgramID(self._owner, self._kind, local_id)
        self._validate(result)
        return result

    def compose(
        self, before: ActionProgramID, after: ActionProgramID
    ) -> ActionProgramID:
        before_id, after_id = self._validate(before), self._validate(after)
        self.composition_requests += 1
        if before_id == self._identity_id:
            return after
        if after_id == self._identity_id:
            return before
        key = (before_id, after_id)
        compositions = self._compositions
        found = None if compositions is None else compositions.get(key)
        if found is not None:
            self.composition_hits += 1
            return self.scoped_handle(found)
        result = self._compose(before, after)
        result_id = self._validate(result)
        if compositions is not None:
            compositions[key] = result_id
        return result

    def power(self, action_id: ActionProgramID, exponent: int) -> ActionProgramID:
        local_id = self._validate(action_id)
        if type(exponent) is not int or exponent < 0:
            raise ValueError(exponent)
        self.power_requests += 1
        key = (local_id, exponent)
        found = self._powers.get(key)
        if found is not None:
            self.power_hits += 1
            return self.scoped_handle(found)
        result = self.identity
        factor = action_id
        remaining = exponent
        while remaining:
            if remaining & 1:
                result = self.compose(result, factor)
            remaining >>= 1
            if remaining:
                factor = self.compose(factor, factor)
        self._powers[key] = self._validate(result)
        return result

    def metrics(self) -> ActionPowerMetrics:
        return ActionPowerMetrics(
            self.composition_requests,
            self.composition_hits,
            len(self._compositions or ()),
            self.power_requests,
            self.power_hits,
            len(self._powers),
        )

    def composition_keys_snapshot(self) -> tuple[tuple[int, int], ...]:
        """Return immutable integer IDs retained by the composition cache."""
        return tuple(self._compositions or ())


__all__ = ["ActionPowerArena", "ActionPowerMetrics"]
