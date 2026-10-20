"""Source-certified Moore-minimal innovation tapes for Collatz boundary macros.

A state here is a *modular phase for an observation-only transducer*, never
an endpoint/width Hashlife ActionID.  The regular core of each guarded
boundary macro is driven by a phase multiplication modulo an odd modulus.
Its emitted alphabet distinguishes SUB borrows, positive ADD carries and
negative ADD carries.  Exceptional entry/exit symbols are computed from
authenticated source residues and the exact valuation exit guard.

No whole trajectory, unbounded parity word, or leaf/carry tape is retained.
Moore minimization is exhaustive over every phase residue, including nonunits
and preperiodic states. Demand-selected automata and class orbits live only in
the active query ledger and are released with that observer scope.
"""

from __future__ import annotations

from collections.abc import Callable
from contextlib import AbstractContextManager
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Final, Self, TypeVar, cast

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.arithmetic.functions.finite_observer import (
    minimize_finite_observer,
    partition_representatives,
)
from number_compiler.resources.construction_scope import RuntimeConstruction
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.payload_cost import retained_payload_node_count
from number_compiler.sequences.collatz.border_identity import (
    ENTRY_89_AT_NINE,
    ENTRY_421,
    ENTRY_4721,
    PATH_630,
    CycleEntryPhase,
    GuardedBorderPath,
)
from number_compiler.sequences.collatz.innovation_carry_cocycle import (
    exact_source_symbol as _exact_source_symbol,
)

NORMALIZED_INNOVATION_TAPE_TAG: Final[str] = "normalized-innovation-v1"


if TYPE_CHECKING:
    from number_compiler.sequences.collatz.boundary_macros import (
        CollatzBoundaryMacro,
    )

# B is subtraction/borrow; A positive addition/carry; N negative addition/carry.
# Each letter always carries its actual zero/one modular flag.
_SYMBOLS = ("B0", "B1", "A0", "A1", "N0", "N1")
InnovationCoreIdentity = CycleEntryPhase | GuardedBorderPath
_INNOVATION_CORES: tuple[InnovationCoreIdentity, ...] = (
    ENTRY_421,
    ENTRY_4721,
    PATH_630,
    ENTRY_89_AT_NINE,
)
_COUNTER_PREFIX = "collatz_query_local_innovation_observer_"
_MISSING = object()
_MemoValue = TypeVar("_MemoValue")
_ISSUED_CLOCK = object()
_UNISSUED = object()


class InnovationObserverMemo:
    """Short-lived query-owned tables for one explicit innovation observer.

    These are finite observation automata, not endpoint actions.  The owner
    charges table cells and construction scratch to the request ledger; it is
    intentionally not retained in a module-global cache.
    """

    __slots__ = (
        "__weakref__",
        "_closed",
        "_memo",
        "_owner",
        "_scratch_owner",
        "ledger",
    )

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("innovation observer memo requires a query ledger")
        self.ledger = ledger
        prefix = f"collatz-innovation-observer-{ledger.owner_count}"
        ledger.require_fresh_owner_names((prefix + "-tables", prefix + "-scratch"))
        with RuntimeConstruction(ledger):
            self._owner = ledger.register(prefix + "-tables", "query_memo")
            self._scratch_owner = ledger.register(
                prefix + "-scratch", "temporary_workspace"
            )
            self._memo: OwnedMemo[tuple[object, ...], object] = OwnedMemo(
                ledger,
                self._owner,
                node_cost=lambda key, item: retained_payload_node_count((key, item)),
                evictable=True,
            )
            self._closed = False
            ledger.register_execution_root(self)
            for name in (
                "lookups",
                "hits",
                "misses",
                "publications",
                "bypasses",
                "failures",
                "refinement_levels",
                "refinement_state_visits",
            ):
                ledger.bump(_COUNTER_PREFIX + name, 0)

    def __enter__(self) -> Self:
        if self._closed:
            raise RuntimeError("innovation observer memo is closed")
        return self

    def __exit__(self, *_args: object) -> None:
        self.dispose()

    def check_open(self) -> None:
        if self._closed:
            raise RuntimeError("innovation observer memo is closed")
        # A caller may dispose an owner directly through the ledger. Validate
        # those scoped bindings before returning any memoized observation.
        self.ledger.registered_container(self._owner)
        self.ledger.registered_container(self._scratch_owner)

    def note_refinement(self, state_count: int) -> None:
        self.check_open()
        if type(state_count) is not int or state_count < 0:
            raise ValueError("refinement state count must be nonnegative")
        self.ledger.bump(_COUNTER_PREFIX + "refinement_levels")
        self.ledger.bump(_COUNTER_PREFIX + "refinement_state_visits", state_count)

    def reserve_scratch(self, *, entries: int = 0, nodes: int = 0) -> None:
        """Reserve temporary state through this memo's private ledger owner."""
        self.check_open()
        self.ledger.reserve(self._scratch_owner, entries=entries, nodes=nodes)

    def release_scratch(self, *, entries: int = 0, nodes: int = 0) -> None:
        """Release temporary state through this memo's private ledger owner."""
        self.check_open()
        self.ledger.release(self._scratch_owner, entries=entries, nodes=nodes)

    def scratch_reservation(self, *, nodes: int) -> AbstractContextManager[None]:
        """Return a reservation context tied to this live query owner."""
        self.check_open()
        return self.ledger.reservation(self._scratch_owner, nodes=nodes)

    @property
    def scratch_disposed(self) -> bool:
        """Expose only the scratch account's disposed state for audits."""
        return self.ledger.account_status(self._scratch_owner).disposed

    def get_or_build(
        self,
        layer: str,
        key: tuple[object, ...],
        build: Callable[[], _MemoValue],
        *,
        work_nodes: int,
    ) -> _MemoValue:
        self.check_open()
        if type(layer) is not str or not layer:
            raise ValueError("observer cache layer must be named")
        if type(key) is not tuple or any(
            type(part) not in (int, str, CycleEntryPhase, GuardedBorderPath)
            for part in key
        ):
            raise TypeError("observer memo key must use admitted exact fields")
        if type(work_nodes) is not int or work_nodes < 0:
            raise ValueError("observer construction work bound must be nonnegative")
        cache_key = (layer, *key)
        self.ledger.bump(_COUNTER_PREFIX + "lookups")
        cached = self._memo.get(cache_key, _MISSING)
        if cached is not _MISSING:
            self.ledger.bump(_COUNTER_PREFIX + "hits")
            return cast(_MemoValue, cached)
        self.ledger.bump(_COUNTER_PREFIX + "misses")
        try:
            with self.ledger.reservation(self._scratch_owner, nodes=work_nodes):
                value = build()
        except BaseException:
            self.ledger.bump(_COUNTER_PREFIX + "failures")
            raise
        try:
            self._memo[cache_key] = value
        except BlockContextBudgetExceeded:
            self.ledger.bump(_COUNTER_PREFIX + "bypasses")
        else:
            self.ledger.bump(_COUNTER_PREFIX + "publications")
        return value

    def dispose(self) -> None:
        if self._closed:
            return
        self._memo.dispose()
        self.ledger.mark_disposed(self._scratch_owner)
        self._closed = True


def _borrow(left: int, right: int, modulus: int) -> str:
    return "B" + str(int(left % modulus < right % modulus))


def _addition(left: int, right: int, modulus: int, *, negative: bool = False) -> str:
    return ("N" if negative else "A") + str(
        int(left % modulus + right % modulus >= modulus)
    )


def _core_symbols(
    identity: InnovationCoreIdentity, phase: int, modulus: int
) -> tuple[str, ...]:
    """One *interior* return of the authenticated source's normalized orbit."""
    two = pow(2, -1, modulus)
    four = two * two % modulus
    if identity == ENTRY_421:
        eight = four * two % modulus
        # C: 1+u (mod 4 = 1), then D: 2+3u/2 (mod 4 = 2).
        c = _addition(1 + two * phase, 1 + 3 * four * phase, modulus, negative=True)
        d = _addition(1 + 3 * four * phase, 1 + 3 * eight * phase, modulus)
        return c, d
    if identity == ENTRY_4721:
        # Pair of odd, mod-4=3 sources, with w and then 3w/2.
        second = 3 * two * phase % modulus
        return (
            _borrow(3 * phase, 2 * phase, modulus),
            _borrow(3 * second, 2 * second, modulus),
        )
    if identity == PATH_630:
        return (_borrow(2 * phase, phase, modulus),)
    if identity == ENTRY_89_AT_NINE:
        return (_borrow(3 * phase, 2 * phase, modulus),)
    raise ValueError("unsupported Collatz innovation border identity")


@dataclass(frozen=True, slots=True)
class InnovationMooreClock:
    """Minimum complete-future quotient of one certified modular CORE clock."""

    identity: InnovationCoreIdentity
    modulus: int
    multiplier: int
    classes: tuple[int, ...]  # residue -> Moore class
    outputs: tuple[tuple[str, ...], ...]  # Moore class -> emitted motif
    successors: tuple[int, ...]  # Moore class -> next class
    _authority: object = field(default=_UNISSUED, init=False, repr=False, compare=False)
    _seal: tuple[object, ...] = field(default=(), init=False, repr=False, compare=False)

    @property
    def producer_issued(self) -> bool:
        seal = self._seal
        return (
            self._authority is _ISSUED_CLOCK
            and len(seal) == 6
            and type(self.identity) in (CycleEntryPhase, GuardedBorderPath)
            and self.identity in _INNOVATION_CORES
            and type(self.modulus) is int
            and type(self.multiplier) is int
            and seal[0] == self.identity
            and type(seal[1]) is int
            and type(seal[2]) is int
            and seal[1] == self.modulus
            and seal[2] == self.multiplier
            and self.classes is seal[3]
            and self.outputs is seal[4]
            and self.successors is seal[5]
        )

    def _check_issued(self) -> None:
        if not self.producer_issued:
            raise ValueError("innovation Moore clock was not issued by its constructor")

    @property
    def class_count(self) -> int:
        return len(self.outputs)

    def class_id(self, phase: int) -> int:
        self._check_issued()
        phase = require_integer(phase, "innovation phase")
        return self.classes[phase % self.modulus]

    def advance(self, phase: int, returns: int) -> int:
        self._check_issued()
        phase = require_integer(phase, "innovation phase")
        returns = require_integer(returns, "Moore clock extent", 0)
        return (
            phase
            % self.modulus
            * pow(self.multiplier, returns, self.modulus)
            % self.modulus
        )

    def powered(
        self,
        phase: int,
        returns: int,
        *,
        memo: InnovationObserverMemo | None = None,
    ) -> dict[str, object]:
        """Power a *finite* Moore-minimal future, without expanding its tape.

        The horizon-qualified ID is the coarsest possible class for exactly
        ``returns`` core motifs; the global ID is its complete-core future
        state.  Neither can act as an endpoint or guarded-width identity.
        """
        self._check_issued()
        phase = require_integer(phase, "innovation phase")
        returns = require_integer(returns, "Moore clock extent", 0)
        from number_compiler.sequences.collatz.innovation_future_moore import (
            innovation_future_moore,
        )

        phase %= self.modulus
        root_class = self.class_id(phase)
        machine = innovation_future_moore(self.modulus, memo=memo)
        global_id = machine.global_id(self.identity, phase, memo=memo)
        finite_id = machine.finite_id(self.identity, phase, returns, memo=memo)
        finite_count = machine.finite_count(returns, memo=memo)
        orbit = global_class_orbit(self.modulus, global_id, memo=memo)
        prefix, period = orbit.prefix, orbit.period
        # One previously compiled finite future can be used by distinct
        # infinite-future classes whenever their requested prefixes agree.
        borrow_ones, carry_ones, sample = _finite_future_summary(
            self.modulus, returns, finite_id, memo=memo
        )
        motif_length = len(self.outputs[root_class])
        period_word = orbit.motifs[prefix : prefix + period]
        terminal_phase = self.advance(phase, returns)
        # The legacy period description remains sourced from the real global
        # phase, not the finite representative (which may diverge afterward).
        return {
            "modulus": self.modulus,
            "border": self.identity.observation(),
            "moore_class": root_class,
            "moore_classes": self.class_count,
            "global_future_control_id": global_id,
            "global_future_control_after": machine.advance(
                global_id, returns, memo=memo
            ),
            "global_future_classes": machine.class_count,
            "finite_future_control_id": finite_id,
            "finite_future_classes": finite_count,
            "finite_future_horizon": returns,
            "finite_future_stabilization_horizon": machine.stabilization_horizon,
            "phase": phase,
            "phase_after": terminal_phase,
            "motif_symbols": motif_length,
            "returns": returns,
            "normalized_symbols": returns * motif_length,
            "borrow_ones": borrow_ones,
            "carry_ones": carry_ones,
            "subtraction_events": returns
            * sum(s[0] == "B" for s in self.outputs[root_class]),
            "addition_events": returns
            * sum(s[0] != "B" for s in self.outputs[root_class]),
            "preperiod_returns": prefix,
            "period_returns": period,
            "cycle_word": (
                "".join(
                    str(_SYMBOLS.index(symbol))
                    for motif in period_word
                    for symbol in motif
                )
                if len(period_word) * motif_length <= 256
                else None
            ),
            "cycle_word_alphabet": "B0 B1 A0 A1 N0 N1",
            "cycle_word_omitted": len(period_word) * motif_length > 256,
            "sample": sample,
            "scope": "horizon-certified minimal observer action, not endpoint ActionID",
        }


def innovation_moore_clock(
    identity: InnovationCoreIdentity,
    modulus: int,
    *,
    memo: InnovationObserverMemo | None = None,
) -> InnovationMooreClock:
    """Exactly minimize the infinite output trace of each modular core phase.

    This is a genuine deterministic Moore refinement on ALL residues, not a
    sampled partition.  The stable equivalence respects emitted words and the
    successor congruence, including nonunit phase tails when m is divisible
    by three.  It is not a whole-Collatz Moore quotient.
    """
    if (
        type(identity) not in (CycleEntryPhase, GuardedBorderPath)
        or identity not in _INNOVATION_CORES
    ):
        raise ValueError("unrecognized guarded Collatz border identity")
    modulus = require_integer(modulus, "modular clock modulus", 3, 4096)
    if modulus % 2 == 0:
        raise ValueError("modular clock requires odd 3 <= modulus <= 4096")
    if memo is not None:
        if type(memo) is not InnovationObserverMemo:
            raise TypeError("innovation clock memo must be query-owned")
        memo.check_open()
    multipliers = {
        ENTRY_421: (3, 4),
        ENTRY_4721: (9, 4),
        PATH_630: (1, 2),
        ENTRY_89_AT_NINE: (3, 2),
    }
    numerator, denominator = multipliers[identity]
    multiplier = numerator * pow(denominator, -1, modulus) % modulus

    def build() -> InnovationMooreClock:
        outputs = tuple(_core_symbols(identity, s, modulus) for s in range(modulus))
        next_states = tuple((s * multiplier) % modulus for s in range(modulus))
        result = minimize_finite_observer(
            tuple((target,) for target in next_states),
            outputs,
            on_refinement=(None if memo is None else memo.note_refinement),
        )
        representatives = partition_representatives(result.class_ids, result.classes)
        class_outputs = tuple(outputs[i] for i in representatives)
        class_next = tuple(result.class_ids[next_states[i]] for i in representatives)
        clock = InnovationMooreClock(
            identity, modulus, multiplier, result.class_ids, class_outputs, class_next
        )

        object.__setattr__(clock, "_authority", _ISSUED_CLOCK)
        object.__setattr__(
            clock,
            "_seal",
            (
                identity,
                modulus,
                multiplier,
                clock.classes,
                clock.outputs,
                clock.successors,
            ),
        )
        return clock

    if memo is None:
        clock = build()
    else:
        clock = memo.get_or_build(
            "local-clock",
            (identity, modulus),
            build,
            work_nodes=max(1, 32 * modulus),
        )
    if (
        type(clock) is not InnovationMooreClock
        or not clock.producer_issued
        or clock.identity != identity
        or clock.modulus != modulus
        or clock.multiplier != multiplier
    ):
        raise ValueError("innovation clock memo returned a foreign quotient")
    return clock


@dataclass(frozen=True, slots=True)
class _GlobalClassOrbit:
    """An interned all-family Moore orbit with constant-time prefix counts."""

    prefix: int
    period: int
    ids: tuple[int, ...]
    motifs: tuple[tuple[str, ...], ...]
    borrow_prefix: tuple[int, ...]
    carry_prefix: tuple[int, ...]

    def counts(self, returns: int) -> tuple[int, int]:
        if returns < len(self.ids):
            return self.borrow_prefix[returns], self.carry_prefix[returns]
        q, tail = divmod(returns - self.prefix, self.period)
        b = (
            self.borrow_prefix[self.prefix]
            + q * (self.borrow_prefix[-1] - self.borrow_prefix[self.prefix])
            + self.borrow_prefix[self.prefix + tail]
            - self.borrow_prefix[self.prefix]
        )
        c = (
            self.carry_prefix[self.prefix]
            + q * (self.carry_prefix[-1] - self.carry_prefix[self.prefix])
            + self.carry_prefix[self.prefix + tail]
            - self.carry_prefix[self.prefix]
        )
        return b, c


def global_class_orbit(
    modulus: int,
    global_id: int,
    *,
    memo: InnovationObserverMemo | None = None,
) -> _GlobalClassOrbit:
    """Intern a minimal infinite-core orbit across *all four* families."""
    from number_compiler.sequences.collatz.innovation_future_moore import (
        innovation_future_moore,
    )

    machine = innovation_future_moore(modulus, memo=memo)
    if type(global_id) is not int or not 0 <= global_id < machine.class_count:
        raise ValueError("unknown all-family Collatz Moore class")

    def build() -> _GlobalClassOrbit:
        seen: dict[int, int] = {}
        ids: list[int] = []
        motifs: list[tuple[str, ...]] = []
        b = [0]
        c = [0]
        state = global_id
        while state not in seen:
            seen[state] = len(ids)
            motif = machine.global_outputs[state]
            ids.append(state)
            motifs.append(motif)
            b.append(b[-1] + sum(symbol == "B1" for symbol in motif))
            c.append(c[-1] + sum(symbol in ("A1", "N1") for symbol in motif))
            state = machine.successor(state)
        prefix = seen[state]
        return _GlobalClassOrbit(
            prefix, len(ids) - prefix, tuple(ids), tuple(motifs), tuple(b), tuple(c)
        )

    if memo is None:
        return build()
    return memo.get_or_build(
        "global-class-orbit",
        (modulus, global_id),
        build,
        work_nodes=max(1, 12 * machine.class_count),
    )


def _finite_future_summary(
    modulus: int,
    returns: int,
    finite_id: int,
    *,
    memo: InnovationObserverMemo | None = None,
) -> tuple[int, int, tuple[str, ...]]:
    """Share an exact finite word prefix across distinct infinite-future IDs.

    The cached payload has no raw source residue, phase-after, endpoint or
    terminal macro symbols. Those must be reconstructed from the caller's
    independently authenticated action.
    """
    from number_compiler.sequences.collatz.innovation_future_moore import (
        innovation_future_moore,
    )

    def build() -> tuple[int, int, tuple[str, ...]]:
        machine = innovation_future_moore(modulus, memo=memo)
        representative = machine.finite_representative(returns, finite_id, memo=memo)
        orbit = global_class_orbit(modulus, representative, memo=memo)
        b, c = orbit.counts(returns)
        sample: list[str] = []
        for tick in range(min(returns, 24)):
            if tick < len(orbit.ids):
                motif = orbit.motifs[tick]
            else:
                motif = orbit.motifs[
                    orbit.prefix + (tick - orbit.prefix) % orbit.period
                ]
            sample.extend(motif)
        return b, c, tuple(sample[:48])

    if memo is None:
        return build()
    return memo.get_or_build(
        "finite-summary",
        (modulus, returns, finite_id),
        build,
        work_nodes=96,
    )


def _aggregate_symbols(
    *parts: tuple[str, ...], core: dict[str, object]
) -> dict[str, int]:
    singles = tuple(s for part in parts for s in part)
    if any(s not in _SYMBOLS for s in singles):
        raise AssertionError("invalid innovation alphabet")
    count_b = sum(s[0] == "B" for s in singles)
    count_b1 = sum(s == "B1" for s in singles)
    count_c = sum(s[0] != "B" for s in singles)
    count_c1 = sum(s in ("A1", "N1") for s in singles)
    return {
        "normalized_steps": require_integer(
            core["normalized_symbols"], "normalized symbol count", 0
        )
        + len(singles),
        "subtraction_branch_events": require_integer(
            core["subtraction_events"], "subtraction event count", 0
        )
        + count_b,
        "borrow_ones": require_integer(core["borrow_ones"], "borrow count", 0)
        + count_b1,
        "addition_branch_events": require_integer(
            core["addition_events"], "addition event count", 0
        )
        + count_c,
        "carry_ones": require_integer(core["carry_ones"], "carry count", 0) + count_c1,
    }


def innovation_macro_tape(
    macro: CollatzBoundaryMacro,
    modulus: int = 49,
    *,
    memo: InnovationObserverMemo | None = None,
) -> dict[str, object]:
    """Exact compact normalized SECOND-INNOVATION tape for a witnessed macro.

    A period may be pumped only while the macro's independently authenticated
    valuation guard holds.  Exceptional entry and last-step ADD/SUB branches
    never get silently merged into the periodic core.  This produces actual
    normalized-orbit symbols, not a physical-return sampling clock.
    """
    from number_compiler.sequences.collatz.boundary_macros import (
        CollatzBoundaryMacro,
        validate_boundary_macro,
    )

    modulus = require_integer(modulus, "innovation tape modulus", 3, 4096)
    if modulus % 2 == 0:
        raise ValueError("innovation tape modulus must be odd")
    if memo is not None:
        if type(memo) is not InnovationObserverMemo:
            raise TypeError("innovation tape memo must be query-owned")
        memo.check_open()
    if type(macro) is not CollatzBoundaryMacro:
        raise ValueError("normalized innovation tape requires a certified macro")
    validate_boundary_macro(macro)
    identity = macro.identity
    clock = innovation_moore_clock(identity, modulus, memo=memo)
    r = macro.repetitions
    full = r == macro.maximum_repetitions
    entry: tuple[str, ...]
    exit_symbols: tuple[str, ...]
    if identity == ENTRY_421:
        entry = (
            _exact_source_symbol(macro.source, modulus),
            _exact_source_symbol(macro.source // 2, modulus),
        )
        u = (macro.source - 4) // 4 % modulus
        core = clock.powered(u, r - 1, memo=memo)
        last = require_integer(core["phase_after"], "powered phase", 0)
        odd_sub = full and v2_positive(macro.source - 4) % 2 == 1
        if odd_sub:
            w = (last + 2) * pow(4, -1, modulus) % modulus
            exit_symbols = (_borrow(3 * w, 2 * w, modulus),)
        else:
            exit_symbols = (_core_symbols(ENTRY_421, last, modulus)[0],)
    elif identity == ENTRY_4721:
        entry = (_exact_source_symbol(macro.source, modulus),)
        a = (macro.source + 2) // 8 % modulus
        core = clock.powered(a, r - 1, memo=memo)
        last = require_integer(core["phase_after"], "powered phase", 0)
        first = _borrow(3 * last, 2 * last, modulus)
        last_add = full and v2_positive(macro.source + 2) % 2 == 1
        if last_add:
            second = _addition(
                3 * last, (9 * last - 1) * pow(2, -1, modulus), modulus, negative=True
            )
        else:
            mid = 3 * pow(2, -1, modulus) * last % modulus
            second = _borrow(3 * mid, 2 * mid, modulus)
        exit_symbols = first, second
    elif identity == PATH_630:
        entry = (
            _exact_source_symbol(macro.source, modulus),
            _exact_source_symbol(macro.source // 2, modulus),
        )
        k = (macro.source - 6) // 20
        u = (3 * k + 1) >> macro.maximum_repetitions
        a = 5 * (u % modulus) * pow(2, macro.maximum_repetitions - 2, modulus) % modulus
        core = clock.powered(a, r - int(full), memo=memo)
        exit_symbols = (_exact_source_symbol(10 * u, modulus),) if full else ()
    elif identity == ENTRY_89_AT_NINE:
        entry = ()
        a = (macro.source + 1) // 4 % modulus
        core = clock.powered(a, r - int(full), memo=memo)
        if full:
            last_x = (2 * macro.endpoint - 1) // 3
            exit_symbols = (_exact_source_symbol(last_x, modulus),)
        else:
            exit_symbols = ()
    else:
        raise ValueError("boundary macro has no normalized innovation core")
    totals = _aggregate_symbols(entry, exit_symbols, core=core)
    if totals["normalized_steps"] != macro.normalized_symbols:
        raise AssertionError("powered innovation tape lost normalized clock")
    if (
        totals["subtraction_branch_events"] + totals["addition_branch_events"]
        != totals["normalized_steps"]
    ):
        raise AssertionError("powered innovation tape lost branch partition")
    # Explicitly retain the *placement* of exceptional symbols.  The full
    # regular word is: ENTRY ++ CORE^returns ++ EXIT, not a bit-only count.
    return {
        "border": identity.observation(run_parameters=(macro.repetitions,)),
        "modulus": modulus,
        "entry_symbols": entry,
        "core": core,
        "exit_symbols": exit_symbols,
        # Full signed word is ENTRY ++ CORE^returns ++ EXIT. This observer
        # program is canonical only within its witnessed extent; equality
        # never licenses endpoint, width, or accumulator action merging.
        "finite_future_action_id": (
            NORMALIZED_INNOVATION_TAPE_TAG,
            modulus,
            entry,
            require_integer(core["returns"], "powered return count", 0),
            require_integer(core["finite_future_control_id"], "finite future class", 0),
            exit_symbols,
        ),
        "normalized_second_innovation": totals,
        "scope": "certified normalized Collatz carry/borrow word with guarded exits",
        "cache_scope": (
            "query-local observer memo only; no cross-query retention or endpoint ActionID"
        ),
    }


def observed_innovation_macro_tape(
    macro: CollatzBoundaryMacro,
    modulus: int,
    *,
    ledger: ResourceLedger,
    memo: InnovationObserverMemo | None = None,
) -> dict[str, object]:
    """Build a tape using tables owned by the active query ledger.

    An explicit memo may be shared by observers in the same query. Otherwise a
    short-lived memo is released before this function returns.
    """
    if type(ledger) is not ResourceLedger:
        raise TypeError("Moore observer must charge its live resource ledger")
    if memo is not None:
        if type(memo) is not InnovationObserverMemo:
            raise TypeError("Moore observer memo must be query-owned")
        if memo.ledger is not ledger:
            raise ValueError("Moore observer memo belongs to another query ledger")
        memo.check_open()
        return innovation_macro_tape(macro, modulus, memo=memo)
    with InnovationObserverMemo(ledger) as scoped_memo:
        return innovation_macro_tape(macro, modulus, memo=scoped_memo)


__all__ = [
    "InnovationMooreClock",
    "InnovationObserverMemo",
    "innovation_macro_tape",
    "innovation_moore_clock",
    "observed_innovation_macro_tape",
]
