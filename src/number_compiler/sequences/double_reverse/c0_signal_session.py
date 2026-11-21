"""Source-bound C0 low-two carry signal and same-time event queries."""

from __future__ import annotations

from collections.abc import Callable
from typing import Self

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.periodic_slp import periodic_word
from number_compiler.arithmetic.carry.temporal_signal import TemporalSignalBank
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.resources.lifecycle import cleanup_all

from .boundary_cycles import CANDIDATE_COMPONENTS
from .temporal_digit_affine import seed196_low_four_digits_at_even_generation
from .temporal_hashlife import DoubleReverseTemporalHashlife
from .temporal_hashlife_borders import edge_phase
from .temporal_hashlife_types import DoubleReverseSourcePrefix
from .temporal_mixed_adic_consumer import certified_edge_action


def _mixed_period() -> tuple[int, ...]:
    """Compute phase outputs from every authenticated C0 boundary edge."""
    certified_edge_action()
    phases: list[int | None] = [None] * 4
    for edge in CANDIDATE_COMPONENTS[0]:
        phase = edge_phase(edge[:2], edge[2:])
        if phase is None:
            raise AssertionError("C0 edge lost its phase")
        low, high = edge[3], edge[2]
        low_value = int(low >= 5) + (5 - low if low < 5 else 0)
        high_value = int(high >= 5) + (5 - high if high < 5 else 0)
        value = low_value + 6 * high_value
        if phases[phase] is not None and phases[phase] != value:
            raise AssertionError("C0 phase does not determine the low mask")
        phases[phase] = value
    if any(value is None for value in phases):
        raise AssertionError("C0 low mask is missing a phase")
    return tuple(int(value) for value in phases if value is not None)


class C0SignalSession:
    """A query-owned compiler for one source's low-two mixed mask clock."""

    def __init__(
        self,
        arena: LedgerSLPArena,
        scratch_owner: int,
        engine: DoubleReverseTemporalHashlife,
        prefix: Callable[[], DoubleReverseSourcePrefix],
        validate_source: Callable[[], None],
        seed: int,
        horizon: int,
        transitions: tuple[tuple[tuple[int, int], ...], ...],
        required_events: int,
    ) -> None:
        self._arena = arena
        self._engine = engine
        self._prefix = prefix
        self._validate_source = validate_source
        self._seed = seed
        self._horizon = horizon
        self._generation = arena.node_id_generation
        self._closed = False
        self._failed = False
        self._bank = TemporalSignalBank(
            arena, scratch_owner, transitions, required_events
        )
        self._states = len(transitions[0])
        owner: int | None = None
        try:
            owner = arena.ledger.register(
                f"c0-signal-roots-{arena.ledger.owner_count}", "temporal_signal_root"
            )
            self._roots: OwnedMemo[tuple[str, int, int, int], int] = OwnedMemo(
                arena.ledger, owner, nodes_per_entry=1
            )
        except BaseException:
            if owner is None:
                self._bank.dispose()
            else:
                registered_owner = owner
                cleanup_all(
                    (
                        self._bank.dispose,
                        lambda: arena.ledger.mark_disposed(registered_owner),
                    )
                )
            raise

    def _claim(
        self, origin: int, samples: int, stride: int
    ) -> DoubleReverseSourcePrefix:
        """Validate the live source and physical sample interval."""
        if self._closed or self._failed:
            raise ValueError("C0 signal session is closed or failed")
        self._validate_source()
        if self._arena.node_id_generation != self._generation:
            raise ValueError("C0 signal session is stale")
        if (
            type(origin) is not int
            or type(samples) is not int
            or origin < 0
            or samples < 0
        ):
            raise ValueError("signal origin and sample count must be nonnegative")
        last = origin + (samples - 1) * stride if samples else origin - 1
        if last > self._horizon:
            raise ValueError("C0 signal extends beyond the query generation")
        issued = self._engine.source_prefix()
        entry = self._engine.validate_source_prefix(
            issued
            if issued is not None and issued.certified_phase is not None
            else self._prefix()
        )
        if entry.certified_phase is None or origin < entry.physical_steps:
            raise ValueError("C0 signal begins before its admitted source")
        return entry

    def _first_hit(self, root: int, inlet: int, origin: int, stride: int) -> int | None:
        found = self._bank.first_simultaneous(root, inlet)
        return None if found is None else origin + stride * found

    def first(
        self,
        origin: int,
        samples: int,
        inlet: int = 0,
        *,
        require_palindrome: bool = False,
    ) -> int | None:
        """Find a simultaneous event on the exact physical generation grid."""
        entry = self._claim(origin, samples, 1)
        if type(require_palindrome) is not bool:
            raise TypeError("palindrome event selector must be Boolean")
        if type(inlet) is not int or not 0 <= inlet < self._states:
            raise ValueError("signal inlet is outside its state alphabet")
        if require_palindrome:
            certified_edge_action()
            if any(edge[0] == edge[3] for edge in CANDIDATE_COMPONENTS[0]):
                raise AssertionError("C0 boundary permits a palindrome")
            return None
        assert entry.certified_phase is not None
        phase = (entry.certified_phase + origin - entry.physical_steps) % 4
        key = "mixed", 0, phase, samples
        root = self._root(
            key,
            lambda: periodic_word(self._arena, _mixed_period(), samples, phase=phase),
        )
        return self._first_hit(root, inlet, origin, 1)

    def _root(self, key: tuple[str, int, int, int], build: Callable[[], int]) -> int:
        root = self._roots.get(key)
        if root is None:
            checkpoint = len(self._arena.nodes)
            try:
                root = build()
                self._roots[key] = root
            except BaseException:
                self._failed = True
                cleanup_all(
                    (
                        self._roots.clear,
                        self._bank.dispose,
                        lambda: self._arena.rollback_unpublished_suffix(checkpoint),
                    )
                )
                raise
        return root

    def first_seed196_low_digit(
        self, origin: int, samples: int, column: int, inlet: int = 0
    ) -> int | None:
        """Search one certified low-four digit sampled every two generations."""
        if self._seed != 196:
            raise ValueError("low-four signal is certified only for seed 196")
        if type(origin) is not int or origin < 16 or origin % 2:
            raise ValueError("low-four signal needs an even origin at least 16")
        if type(column) is not int or not 0 <= column < 4:
            raise ValueError("low-four signal column must be between 0 and 3")
        self._claim(origin, samples, 2)
        if origin > self._horizon:
            raise ValueError("low-four signal extends beyond the query generation")
        phase = (origin - 20) // 2 if origin < 20 else ((origin - 20) // 2) % 6
        key = "seed196-low", column, phase, samples

        def build() -> int:
            transient = min(samples, max(0, (20 - origin) // 2))
            divisor: int = 10**column

            def digit(generation: int) -> int:
                return (
                    seed196_low_four_digits_at_even_generation(generation)
                    // divisor
                    % 10
                )

            head = self._arena.word(
                tuple(digit(origin + 2 * i) for i in range(transient))
            )
            remaining = samples - transient
            if not remaining:
                return head
            start = origin + 2 * transient
            period = tuple(digit(20 + 2 * i) for i in range(6))
            tail = periodic_word(
                self._arena, period, remaining, phase=(start - 20) // 2
            )
            return self._arena.concat(head, tail)

        root = self._root(key, build)
        return self._first_hit(root, inlet, origin, 2)

    def close(self) -> None:
        if not self._closed:
            cleanup_all((self._roots.dispose, self._bank.dispose))
            self._closed = True

    def __enter__(self) -> Self:
        if self._closed or self._failed:
            raise ValueError("C0 signal session is closed or failed")
        return self

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> None:
        self.close()
