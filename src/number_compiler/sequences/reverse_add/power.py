"""Compact binary-powered reverse/add term descriptors and random access.

The immutable temporal operator descriptor is constructed by binary
composition, so construction retains ``O(log n)`` syntax.  Production digit,
width, and materialization queries use that source-independent powered operator
directly through :class:`HashLifeBlockIndex`.  The retired whole-field and
forcing-occurrence temporal lifts are reference/oracle machinery only and are
not reachable from this descriptor.

The public index uses recursive field images and output-complete interfaces.
Runtime metrics include semantic observation work and query retention; compiler
node counts alone do not establish HashLife execution scaling.
"""

from __future__ import annotations

from collections.abc import Iterator
from math import ceil, log2
from typing import TYPE_CHECKING, Any

from number_compiler.arithmetic.contracts.block_effect import BlockEffect
from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
    source_reads_only,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.temporal_family import _issue_certificate
from number_compiler.arithmetic.fields.radix import (
    bit_width,
    digits_lsd,
    value_from_lsd_digits,
)
from number_compiler.arithmetic.polynomials.twisted_observer import (
    TwistedCylinderProjection,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.compilation import compile_reverse_pair_power

if TYPE_CHECKING:
    from number_compiler.resources.metric_records import HashLifeBehaviorMetrics
    from number_compiler.resources.reverse_power_metrics import ReverseAddPowerMetrics


def pair_field_from_integer(value: int, base: int) -> tuple[int, ...]:
    value = require_integer(value, "seed", 0)
    base = require_integer(base, "base", 2)
    digits = digits_lsd(value, base)
    return tuple(digits[i] + digits[-1 - i] for i in range(len(digits)))


class ReverseAddPoweredTerm:
    """Exact source-specialized ``reverse_add(seed)[generation]`` descriptor."""

    __slots__ = (
        "__weakref__",
        "_active_width",
        "_compiler",
        "_hashlife_max_cache_entries",
        "_hashlife_max_tile_nodes",
        "_index",
        "_ledger",
        "_source_construction",
        "base",
        "compose_operations",
        "effect",
        "generation",
        "pair_power",
        "seed",
        "seed_digits",
        "seed_pair",
        "syntax_depth_bound",
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
        seed = require_integer(seed, "seed", 0)
        generation = require_integer(generation, "generation", 0)
        base = require_integer(base, "base", 2)
        self.seed = seed
        self.base = base
        self.generation = generation
        self._ledger = ResourceLedger(max_context_nodes, max_cache_entries)
        self._ledger.register_execution_root(self)
        self._compiler = LazyCompiler(self._ledger)
        self._hashlife_max_tile_nodes = max_context_nodes
        self._hashlife_max_cache_entries = max_cache_entries
        self.seed_digits = tuple(map(int, digits_lsd(seed, base)))
        self.seed_pair = pair_field_from_integer(seed, base)
        self._source_construction = OriginalSourceConstruction(
            ExactSource(
                self.seed_pair,
                base,
                blank=2 * base - 1,
                extent=self.maximum_width,
                alphabet_size=2 * base - 1,
            ),
        )
        self._index: HashLifeBlockIndex | None = None
        self._active_width: int | None = None

        if generation == 0:
            self.pair_power = None
            self.effect: BlockEffect | None = None
            self.compose_operations = 0
            self.syntax_depth_bound = 0
            return

        terminal = self._compiler.atom(DigitNormalizeBlockEffect(base))
        if generation == 1:
            self.pair_power = None
            self.effect = terminal
            self.compose_operations = 0
            self.syntax_depth_bound = 1
            return

        power = compile_reverse_pair_power(self._compiler, base, generation - 1)
        if power.root is None:
            raise AssertionError("positive pair exponent without powered effect")
        effect = self._compiler.compose(power.root, terminal)
        self.pair_power = power
        self.effect = effect
        # Geometry is carried by ``maximum_width`` only.  The HashLife spatial
        # carrier represents the blank exterior as aligned dyadic tiles rather
        # than interning a generation-sized padding run.
        self.compose_operations = power.compose_operations + 1
        self.syntax_depth_bound = power.syntax_depth + 1

    @property
    def operator_nodes(self) -> int:
        if self.effect is None:
            return 0
        return int(self.effect.operator_nodes())

    @property
    def descriptor_bits(self) -> int:
        # The operator DAG is a deterministic function of these parameters; this
        # is the irreducible external descriptor, not an accounting dodge for
        # in-memory operator nodes (reported separately above).
        return (
            bit_width(self.seed) + bit_width(self.base) + bit_width(self.generation) + 3
        )

    @property
    def maximum_width(self) -> int:
        return len(self.seed_digits) + self.generation

    def _point_index(self) -> HashLifeBlockIndex:
        if self.generation == 0 or self.effect is None:
            raise ValueError("generation zero is a literal seed, not a powered block")
        found = self._index
        if found is None:
            found = HashLifeBlockIndex(
                self.effect,
                self.seed_pair,
                logical_length=self.maximum_width,
                source_construction=self._source_construction,
                certificate=_issue_certificate(
                    self.effect, "reverse-add", self.generation - 1, ledger=self._ledger
                ),
                max_tile_nodes=self._hashlife_max_tile_nodes,
                max_cache_entries=self._hashlife_max_cache_entries,
                ledger=self._ledger,
                compiler=self._compiler,
            )
            self._index = found
        return found

    @source_reads_only
    def digit(self, position: int) -> int:
        position = require_integer(position, "digit coordinate")
        if position < 0:
            raise IndexError(position)
        if self.generation == 0:
            if position >= len(self.seed_digits):
                raise IndexError(position)
            return self.seed_digits[position]
        if position >= self.maximum_width:
            raise IndexError(position)
        value = self._point_index().direct_powered_point(position)
        effect = self.effect
        if effect is None:
            raise AssertionError("positive reverse generation has no admitted effect")
        if value == int(effect.blank):
            raise IndexError(position)
        if not 0 <= value < self.base:
            raise AssertionError((value, self.base, self.generation, position))
        return value

    def direct_powered_digit(self, position: int) -> int:
        """Backward-compatible alias for the production direct powered path."""
        return self.digit(position)

    @source_reads_only
    def width(self) -> int:
        if self.generation == 0:
            return len(self.seed_digits)
        found = self._active_width
        if found is None:
            found = self._point_index().direct_active_width()
            self._active_width = found
        return found

    @property
    def estimated_bit_length(self) -> int:
        width = self.width()
        if self.base == 2:
            return width
        return max(1, ceil(width * log2(self.base)))

    def iter_digits(self) -> Iterator[int]:
        if self.generation == 0:
            yield from self.seed_digits
            return
        for value in self._point_index().iter_direct_active():
            if not 0 <= value < self.base:
                raise AssertionError((value, self.base))
            yield int(value)

    def digits(self) -> tuple[int, ...]:
        return tuple(self.iter_digits())

    def is_palindrome(self) -> bool:
        """Demand mirror equality, stopping at the first certified mismatch.

        The outer three comparisons cover the observed growth safety tube for
        196. Surviving those comparisons requires the full exact consumer;
        no finite observation is promoted to an all-future ray certificate.
        """
        from number_compiler.sequences.reverse_add.palindrome import mirror_palindrome

        return mirror_palindrome(self.width(), self.digit)

    def mirror_obstruction(
        self, *, first_width: int = 1
    ) -> TwistedCylinderProjection | None:
        """Demand a cyclic/negacyclic certificate for this powered target."""
        from number_compiler.arithmetic.polynomials.twisted_observer import (
            first_mirror_obstruction,
        )

        if self.generation == 0:
            return first_mirror_obstruction(
                self.width(), self.digit, first_width=first_width
            )
        return self._point_index().direct_mirror_obstruction(first_width=first_width)

    def materialize(self, *, max_bits: int) -> int:
        max_bits = require_integer(max_bits, "output bit cap", 0)
        if self.estimated_bit_length > max_bits:
            raise ValueError((self.estimated_bit_length, max_bits))
        return value_from_lsd_digits(self.iter_digits(), self.base)

    def behavior_metrics(self) -> HashLifeBehaviorMetrics:
        """Return the seed/function/application HashLife description split.

        This metric does not materialize the output word.  For positive powers it
        reports the compact source-independent jump function separately from the
        seed-specific causal state/action description created by point queries.
        """
        return self._point_index().behavior_metrics()

    def metrics(self) -> ReverseAddPowerMetrics:
        from number_compiler.resources.metric_collection import (
            collect_unindexed_metrics,
        )
        from number_compiler.resources.powered_metrics import project_powered_metrics
        from number_compiler.resources.reverse_power_metrics import (
            ReverseAddPowerMetrics,
        )

        if self._index is None:
            point = collect_unindexed_metrics(self._ledger)
        else:
            point = self._index.metrics()
        return project_powered_metrics(
            ReverseAddPowerMetrics,
            point,
            seed=self.seed,
            base=self.base,
            generation=self.generation,
            operator_nodes=self.operator_nodes,
            compose_operations=self.compose_operations,
            syntax_depth_bound=self.syntax_depth_bound,
            descriptor_bits=self.descriptor_bits,
            spacetime_carry_direction="lsd-to-msd",
        )


__all__ = [
    "ReverseAddPowerMetrics",
    "ReverseAddPoweredTerm",
    "pair_field_from_integer",
]


def __getattr__(name: str) -> Any:
    from number_compiler.api.lazy_exports import resolve_export

    return resolve_export(
        name,
        {"ReverseAddPowerMetrics": "number_compiler.resources.reverse_power_metrics"},
        globals(),
    )
