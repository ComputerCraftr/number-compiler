"""Reverse/add queries owned by the shared source-bound tile scheduler.

The causal boundary evaluator is no longer a production fallback. Identity,
one-step, fused two-step and guarded no-growth consumers use the original source.
General temporal pullback remains a construction obligation; compact action
syntax alone is not execution.
"""

from __future__ import annotations

from collections.abc import Iterator
from math import ceil, log2
from typing import TYPE_CHECKING, Any

from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.radix import (
    bit_width,
    digits_lsd,
    value_from_lsd_digits,
)
from number_compiler.arithmetic.polynomials.twisted_observer import (
    TwistedCylinderProjection,
)
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.resources.metric_records import HashLifeBehaviorMetrics
    from number_compiler.resources.reverse_power_metrics import ReverseAddPowerMetrics
    from number_compiler.sequences.reverse_add.source_images import (
        ReverseSourceImageWorkspace,
    )


def pair_field_from_integer(value: int, base: int) -> tuple[int, ...]:
    """Original-source encoding retained for independent kernel consumers."""
    value = require_integer(value, "seed", 0)
    base = require_integer(base, "base", 2)
    digits = digits_lsd(value, base)
    return tuple(digits[i] + digits[-1 - i] for i in range(len(digits)))


class ReverseAddPoweredTerm:
    """Lazy source/action request; no successor or boundary replay backend."""

    __slots__ = (
        "__weakref__",
        "_binding",
        "_ledger",
        "_workspace",
        "_workspace_identity",
        "base",
        "generation",
        "seed",
    )

    def __init__(
        self,
        seed: int,
        generation: int,
        *,
        base: int = 10,
        max_context_nodes: int | None = None,
        max_cache_entries: int | None = None,
    ) -> None:
        self.seed = require_integer(seed, "seed", 0)
        self.generation = require_integer(generation, "generation", 0)
        self.base = require_integer(base, "base", 2)
        self._binding = (self.seed, self.generation, self.base)
        self._ledger = ResourceLedger(max_context_nodes, max_cache_entries)
        self._workspace: ReverseSourceImageWorkspace | None = None
        self._workspace_identity: ReverseSourceImageWorkspace | None = None
        self._ledger.register_execution_root(self)

    def _source_workspace(self) -> ReverseSourceImageWorkspace:
        from number_compiler.sequences.reverse_add.source_images import (
            ReverseSourceImageWorkspace,
        )

        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        found = self._workspace
        if found is None:
            found = ReverseSourceImageWorkspace(
                self._ledger, self.seed, self.generation, base=self.base
            )
            self._workspace = found
            self._workspace_identity = found
        elif found is not self._workspace_identity or found.ledger is not self._ledger:
            raise ValueError("reverse/add term workspace binding changed")
        return found

    @property
    def operator_nodes(self) -> int:
        return 0 if self._workspace is None else self._workspace.operator_nodes

    @property
    def compose_operations(self) -> int:
        return 0 if self._workspace is None else self._workspace.compose_operations

    @property
    def syntax_depth_bound(self) -> int:
        return 0 if self._workspace is None else self._workspace.syntax_depth_bound

    @property
    def descriptor_bits(self) -> int:
        return (
            bit_width(self.seed) + bit_width(self.base) + bit_width(self.generation) + 3
        )

    @property
    def maximum_width(self) -> int:
        return len(digits_lsd(self.seed, self.base)) + self.generation

    @source_reads_only
    def digit(self, position: int) -> int:
        position = require_integer(position, "digit coordinate")
        if position < 0:
            raise IndexError(position)
        return self._source_workspace().digit(position)

    def direct_powered_digit(self, position: int) -> int:
        """Compatibility alias; does not select another execution path."""
        return self.digit(position)

    @source_reads_only
    def width(self) -> int:
        return self._source_workspace().width()

    @property
    def estimated_bit_length(self) -> int:
        width = self.width()
        return width if self.base == 2 else max(1, ceil(width * log2(self.base)))

    def iter_digits(self) -> Iterator[int]:
        yield from self._source_workspace().iter_digits()

    def digits(self) -> tuple[int, ...]:
        return tuple(self.iter_digits())

    def is_palindrome(self) -> bool:
        from number_compiler.sequences.reverse_add.palindrome import mirror_palindrome

        return mirror_palindrome(self.width(), self.digit)

    def mirror_obstruction(
        self, *, first_width: int = 1
    ) -> TwistedCylinderProjection | None:
        from number_compiler.arithmetic.polynomials.twisted_observer import (
            first_mirror_obstruction,
        )

        return first_mirror_obstruction(
            self.width(), self.digit, first_width=first_width
        )

    def materialize(self, *, max_bits: int) -> int:
        max_bits = require_integer(max_bits, "output bit cap", 0)
        estimate = self.estimated_bit_length
        if estimate > max_bits:
            raise ValueError((estimate, max_bits))
        return value_from_lsd_digits(self.iter_digits(), self.base)

    def behavior_metrics(self) -> HashLifeBehaviorMetrics:
        from number_compiler.resources.reverse_behavior_metrics import (
            reverse_behavior_metrics,
        )

        return reverse_behavior_metrics(self)

    def metrics(self) -> ReverseAddPowerMetrics:
        from number_compiler.resources.metric_collection import (
            collect_unindexed_metrics,
        )
        from number_compiler.resources.powered_metrics import project_powered_metrics
        from number_compiler.resources.reverse_power_metrics import (
            ReverseAddPowerMetrics,
        )

        return project_powered_metrics(
            ReverseAddPowerMetrics,
            collect_unindexed_metrics(self._ledger),
            seed=self.seed,
            base=self.base,
            generation=self.generation,
            operator_nodes=self.operator_nodes,
            compose_operations=self.compose_operations,
            syntax_depth_bound=self.syntax_depth_bound,
            descriptor_bits=self.descriptor_bits,
            spacetime_carry_direction="lsd-to-msd",
        )


__all__ = ["ReverseAddPowerMetrics", "ReverseAddPoweredTerm", "pair_field_from_integer"]


def __getattr__(name: str) -> Any:
    from number_compiler.api.lazy_exports import resolve_export

    return resolve_export(
        name,
        {"ReverseAddPowerMetrics": "number_compiler.resources.reverse_power_metrics"},
        globals(),
    )
