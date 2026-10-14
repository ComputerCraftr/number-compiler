"""Complete signed innovation Moore observer for authenticated Collatz tapes."""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.arithmetic.functions.finite_observer import (
    minimize_finite_observer,
    partition_representatives,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.innovation_carry_cocycle import (
    exact_source_symbol as _exact_source_symbol,
)
from number_compiler.sequences.collatz.innovation_input_tape import (
    NormalizedParityProgram,
    ParityFactor,
    _boundary_macro_specs,
)
from number_compiler.sequences.collatz.innovation_temporal_tape import (
    InnovationObserverMemo,
)

SIGNED_SYMBOLS = ("B0", "B1", "A0", "A1", "N0", "N1")
_PORTS = ("signed", "borrow", "carry")
_UNISSUED = object()
_MOORE_ISSUER = object()
_OBSERVATION_ISSUER = object()


@dataclass(frozen=True, slots=True)
class GlobalInnovationPortMoore:
    """Complete input-driven Moore quotient for one signed port contract."""

    modulus: int
    port: str
    class_ids: tuple[int, ...]
    outputs: tuple[tuple[str, str], ...]
    successors: tuple[tuple[int, int], ...]
    _authority: object = field(default=_UNISSUED, init=False, repr=False, compare=False)
    _seal: tuple[object, ...] = field(default=(), init=False, repr=False, compare=False)

    @property
    def producer_issued(self) -> bool:
        return self._authority is _MOORE_ISSUER and self._seal == (
            self.modulus,
            self.port,
            id(self.class_ids),
            id(self.outputs),
            id(self.successors),
        )

    @property
    def class_count(self) -> int:
        return len(self.outputs)

    def control(self, source: int) -> int:
        if not self.producer_issued:
            raise ValueError("global innovation Moore has foreign or altered authority")
        if type(source) is not int or source <= 0:
            raise ValueError("port control needs a positive exact source")
        return self.class_ids[2 * (source % self.modulus) + (source & 1)]


def _port_output(symbol: str, port: str) -> str:
    if port == "signed":
        return symbol
    if port == "borrow":
        return symbol if symbol == "B1" else "_"
    return symbol if symbol in ("A1", "N1") else "_"


def global_innovation_port_moore(
    modulus: int,
    port: str = "signed",
    *,
    memo: InnovationObserverMemo,
) -> GlobalInnovationPortMoore:
    """Minimize every source residue/parity with both certified next bits."""
    if type(modulus) is not int or modulus < 3 or modulus > 4096 or modulus % 2 == 0:
        raise ValueError("innovation port modulus must be odd in 3..4096")
    if type(port) is not str or port not in _PORTS:
        raise ValueError("unknown signed, borrow, or carry port")
    if type(memo) is not InnovationObserverMemo:
        raise TypeError("global port minimization requires a query-owned memo")
    memo._check_open()

    def build() -> GlobalInnovationPortMoore:
        states = 2 * modulus
        rows: list[tuple[int, int]] = []
        labels: list[tuple[str, str]] = []
        inverse2 = pow(2, -1, modulus)
        inverse4 = inverse2 * inverse2 % modulus
        for index in range(states):
            residue, bit = divmod(index, 2)
            next_row: list[int] = []
            label_row: list[str] = []
            for next_bit in (0, 1):
                branch4 = bit + 2 * next_bit
                source_residue = branch4 + 4 * (
                    (residue - branch4) * inverse4 % modulus
                )
                source_representative = source_residue or 4 * modulus
                symbol = _exact_source_symbol(source_representative, modulus)
                next_residue = (
                    (3 * residue + 1) * inverse2 if bit else residue * inverse2
                ) % modulus
                next_row.append(2 * next_residue + next_bit)
                label_row.append(_port_output(symbol, port))
            rows.append((next_row[0], next_row[1]))
            labels.append((label_row[0], label_row[1]))
        minimized = minimize_finite_observer(
            tuple(rows), tuple(labels), on_refinement=memo.note_refinement
        )
        representatives = partition_representatives(
            minimized.class_ids, minimized.classes
        )
        outputs = tuple(labels[state] for state in representatives)
        successors: tuple[tuple[int, int], ...] = tuple(
            (
                minimized.class_ids[rows[state][0]],
                minimized.class_ids[rows[state][1]],
            )
            for state in representatives
        )
        machine = GlobalInnovationPortMoore(
            modulus,
            port,
            minimized.class_ids,
            outputs,
            successors,
        )
        object.__setattr__(machine, "_authority", _MOORE_ISSUER)
        object.__setattr__(
            machine,
            "_seal",
            (
                modulus,
                port,
                id(machine.class_ids),
                id(machine.outputs),
                id(machine.successors),
            ),
        )
        return machine

    machine = memo._get_or_build(
        "global-input-port-moore",
        (modulus, port),
        build,
        work_nodes=64 * modulus,
    )
    if (
        type(machine) is not GlobalInnovationPortMoore
        or not machine.producer_issued
        or machine.modulus != modulus
        or machine.port != port
    ):
        raise ValueError("innovation Moore memo returned a foreign quotient")
    return machine


@dataclass(frozen=True, slots=True, init=False)
class InnovationTapeObservation:
    """Small root-bound summary; never a source/action semantic identity."""

    source: int
    endpoint: int
    physical_endpoint: int
    modulus: int
    physical_ticks: int
    phase: int
    normalized_steps: int
    one_symbols: int
    moore_classes: int
    symbol_counts: tuple[int, ...]
    borrow_f5: tuple[int, ...]
    carry_f5: tuple[int, ...]
    sample: tuple[str, ...]
    _authority: object = field(default=_UNISSUED, init=False, repr=False, compare=False)
    _seal: tuple[object, ...] = field(default=(), init=False, repr=False, compare=False)

    def __init__(self) -> None:
        raise TypeError("innovation tape observations are issued by a source run")

    @classmethod
    def _issue(
        cls,
        source: int,
        endpoint: int,
        physical_endpoint: int,
        modulus: int,
        physical_ticks: int,
        phase: int,
        normalized_steps: int,
        one_symbols: int,
        moore_classes: int,
        symbol_counts: tuple[int, ...],
        borrow_f5: tuple[int, ...],
        carry_f5: tuple[int, ...],
        sample: tuple[str, ...],
    ) -> InnovationTapeObservation:
        observation = object.__new__(cls)
        for name, value in (
            ("source", source),
            ("endpoint", endpoint),
            ("physical_endpoint", physical_endpoint),
            ("modulus", modulus),
            ("physical_ticks", physical_ticks),
            ("phase", phase),
            ("normalized_steps", normalized_steps),
            ("one_symbols", one_symbols),
            ("moore_classes", moore_classes),
            ("symbol_counts", symbol_counts),
            ("borrow_f5", borrow_f5),
            ("carry_f5", carry_f5),
            ("sample", sample),
        ):
            object.__setattr__(observation, name, value)
        observation._validate()
        object.__setattr__(observation, "_authority", _OBSERVATION_ISSUER)
        object.__setattr__(
            observation,
            "_seal",
            (
                source,
                endpoint,
                physical_endpoint,
                modulus,
                physical_ticks,
                phase,
                normalized_steps,
                one_symbols,
                moore_classes,
                id(symbol_counts),
                id(borrow_f5),
                id(carry_f5),
                id(sample),
            ),
        )
        return observation

    def _validate(self) -> None:
        values = (
            self.source,
            self.endpoint,
            self.physical_endpoint,
            self.modulus,
            self.physical_ticks,
            self.phase,
            self.normalized_steps,
            self.one_symbols,
            self.moore_classes,
        )
        if any(type(value) is not int for value in values):
            raise TypeError("innovation summary coordinates require exact integers")
        if (
            self.source <= 0
            or self.endpoint <= 0
            or self.physical_endpoint <= 0
            or self.modulus < 3
            or self.modulus % 2 == 0
            or self.physical_ticks < 0
            or self.phase not in (0, 1)
            or self.normalized_steps < 0
            or not 0 <= self.one_symbols <= self.normalized_steps
            or self.moore_classes < 1
            or type(self.symbol_counts) is not tuple
            or len(self.symbol_counts) != len(SIGNED_SYMBOLS)
            or any(type(value) is not int or value < 0 for value in self.symbol_counts)
            or sum(self.symbol_counts) != self.normalized_steps
            or type(self.borrow_f5) is not tuple
            or len(self.borrow_f5) != 6
            or any(
                type(value) is not int or not 0 <= value < 5 for value in self.borrow_f5
            )
            or type(self.carry_f5) is not tuple
            or len(self.carry_f5) != 6
            or any(
                type(value) is not int or not 0 <= value < 5 for value in self.carry_f5
            )
            or type(self.sample) is not tuple
            or len(self.sample) > 48
            or any(symbol not in SIGNED_SYMBOLS for symbol in self.sample)
            or self.physical_ticks
            != self.normalized_steps + self.one_symbols + self.phase
            or (
                self.physical_endpoint != self.endpoint
                if self.phase == 0
                else self.physical_endpoint != 3 * self.endpoint + 1
                or self.endpoint % 2 == 0
            )
        ):
            raise ValueError("innovation summary is malformed")

    @property
    def producer_issued(self) -> bool:
        return (
            self._authority is _OBSERVATION_ISSUER
            and self._seal
            == (
                self.source,
                self.endpoint,
                self.physical_endpoint,
                self.modulus,
                self.physical_ticks,
                self.phase,
                self.normalized_steps,
                self.one_symbols,
                self.moore_classes,
                id(self.symbol_counts),
                id(self.borrow_f5),
                id(self.carry_f5),
                id(self.sample),
            )
            and type(self.physical_endpoint) is int
            and type(self.physical_ticks) is int
            and type(self.phase) is int
            and type(self.symbol_counts) is tuple
            and len(self.symbol_counts) == len(SIGNED_SYMBOLS)
            and sum(self.symbol_counts) == self.normalized_steps
            and self.physical_ticks
            == self.normalized_steps + self.one_symbols + self.phase
        )

    def structural_payload(self) -> tuple[object, ...]:
        return (
            "collatz-global-signed-tape-v1",
            self.source,
            self.endpoint,
            self.physical_endpoint,
            self.modulus,
            self.physical_ticks,
            self.phase,
            self.normalized_steps,
            self.one_symbols,
            self.moore_classes,
            self.symbol_counts,
            self.borrow_f5,
            self.carry_f5,
            self.sample,
        )

    def packet(self) -> dict[str, object]:
        counts = dict(zip(SIGNED_SYMBOLS, self.symbol_counts, strict=True))
        return {
            "modulus": self.modulus,
            "source": self.source,
            "normalized_endpoint": self.endpoint,
            "physical_endpoint": self.physical_endpoint,
            "physical_ticks": self.physical_ticks,
            "pending_odd_half_step": bool(self.phase),
            "normalized_steps": self.normalized_steps,
            "one_symbols": self.one_symbols,
            "moore_classes": self.moore_classes,
            "signed_symbol_counts": counts,
            "subtraction_branch_events": counts["B0"] + counts["B1"],
            "addition_branch_events": counts["A0"]
            + counts["A1"]
            + counts["N0"]
            + counts["N1"],
            "borrow_ones": counts["B1"],
            "carry_ones": counts["A1"] + counts["N1"],
            "walsh64_f5": {"borrow": self.borrow_f5, "carry": self.carry_f5},
            "sample": self.sample,
            "scope": "exact source-certified finite normalized prefix; no future closure",
        }


def _emit_word(
    machine: GlobalInnovationPortMoore,
    control: int,
    bits: tuple[int, ...],
    totals: list[int],
    borrow: list[int],
    carry: list[int],
    sample: list[str],
    steps: int,
    ledger: ResourceLedger,
) -> tuple[int, int]:
    for bit in bits:
        symbol = machine.outputs[control][bit]
        control = machine.successors[control][bit]
        position = steps % 6
        totals[SIGNED_SYMBOLS.index(symbol)] += 1
        if symbol == "B1":
            borrow[position] = (borrow[position] + 1) % 5
        elif symbol in ("A1", "N1"):
            carry[position] = (carry[position] + 1) % 5
        if len(sample) < 48:
            sample.append(symbol)
        steps += 1
    ledger.bump("collatz_innovation_moore_input_symbols", len(bits))
    return control, steps


def _feed_factor(
    machine: GlobalInnovationPortMoore,
    control: int,
    factor: ParityFactor,
    *,
    skip_first: bool,
    state: tuple[list[int], list[int], list[int], list[str], int],
    ledger: ResourceLedger,
    memo: InnovationObserverMemo,
) -> tuple[int, tuple[list[int], list[int], list[int], list[str], int]]:
    if (
        not machine.producer_issued
        or type(factor) is not ParityFactor
        or type(factor.motif) is not tuple
    ):
        raise ValueError("innovation input factor has foreign graph authority")
    totals, borrow, carry, sample, steps = state
    prefix = factor.motif[1:] if skip_first else ()
    if prefix:
        control, steps = _emit_word(
            machine, control, prefix, totals, borrow, carry, sample, steps, ledger
        )
    repetitions = factor.repetitions - int(skip_first)
    if repetitions <= 0:
        return control, (totals, borrow, carry, sample, steps)
    seen: (
        dict[
            tuple[int, int],
            tuple[int, tuple[int, ...], tuple[int, ...], tuple[int, ...]],
        ]
        | None
    ) = None
    memo.ledger.reserve(memo._scratch_owner, nodes=1)
    retained_entries = 0
    retained_nodes = 1
    iteration = 0
    try:
        seen = {}
        assert seen is not None
        seen_table = seen
        while iteration < repetitions:
            key = control, steps % 6
            previous = seen_table.get(key)
            if previous is not None and len(sample) >= 48:
                old_iteration, old_totals, old_borrow, old_carry = previous
                cycle_repetitions = iteration - old_iteration
                if cycle_repetitions > 0:
                    cycles = (repetitions - iteration) // cycle_repetitions
                    if cycles:
                        for index in range(len(totals)):
                            totals[index] += cycles * (
                                totals[index] - old_totals[index]
                            )
                        for index in range(6):
                            borrow[index] = (
                                borrow[index]
                                + cycles * (borrow[index] - old_borrow[index])
                            ) % 5
                            carry[index] = (
                                carry[index]
                                + cycles * (carry[index] - old_carry[index])
                            ) % 5
                        skipped = cycles * cycle_repetitions
                        steps += skipped * len(factor.motif)
                        iteration += skipped
                        ledger.bump(
                            "collatz_innovation_moore_cycle_skipped_motif_repetitions",
                            skipped,
                        )
                        continue
            elif previous is None:
                cost = 24 + sum(
                    max(1, (value.bit_length() + 63) // 64)
                    for value in (iteration, steps, *totals, *borrow, *carry)
                )
                memo.ledger.reserve(memo._scratch_owner, entries=1, nodes=cost)
                try:
                    seen_table[key] = (
                        iteration,
                        tuple(totals),
                        tuple(borrow),
                        tuple(carry),
                    )
                except BaseException:
                    memo.ledger.release(memo._scratch_owner, entries=1, nodes=cost)
                    raise
                retained_entries += 1
                retained_nodes += cost
            control, steps = _emit_word(
                machine,
                control,
                factor.motif,
                totals,
                borrow,
                carry,
                sample,
                steps,
                ledger,
            )
            iteration += 1
    finally:
        if seen is not None:
            seen.clear()
        memo.ledger.release(
            memo._scratch_owner,
            entries=retained_entries,
            nodes=retained_nodes,
        )
    return control, (totals, borrow, carry, sample, steps)


def _observe_program_symbols(
    machine: GlobalInnovationPortMoore,
    program: NormalizedParityProgram,
    ledger: ResourceLedger,
    memo: InnovationObserverMemo,
) -> tuple[int, list[int], list[int], list[int], list[str], int]:
    with ledger.reservation(memo._scratch_owner, nodes=128):
        control = machine.control(program.source)
        totals = [0] * len(SIGNED_SYMBOLS)
        borrow = [0] * 6
        carry = [0] * 6
        sample: list[str] = []
        state = (totals, borrow, carry, sample, 0)
        for index, factor in enumerate(program.factors):
            control, state = _feed_factor(
                machine,
                control,
                factor,
                skip_first=index == 0,
                state=state,
                ledger=ledger,
                memo=memo,
            )
        totals, borrow, carry, sample, steps = state
        if program.steps:
            control, steps = _emit_word(
                machine,
                control,
                (program.endpoint & 1,),
                totals,
                borrow,
                carry,
                sample,
                steps,
                ledger,
            )
        return control, totals, borrow, carry, sample, steps


def observe_parity_program(
    program: NormalizedParityProgram,
    modulus: int,
    *,
    ledger: ResourceLedger,
    physical_endpoint: int,
    physical_ticks: int,
    phase: int,
    port: str = "signed",
) -> InnovationTapeObservation:
    """Evaluate an exact compact parity grammar on a complete input-driven graph."""
    if type(program) is not NormalizedParityProgram or not program.producer_issued:
        raise ValueError("observer needs a producer-issued parity program")
    if type(ledger) is not ResourceLedger:
        raise TypeError("observer program requires its production ledger")
    with InnovationObserverMemo(ledger) as memo:
        machine = global_innovation_port_moore(modulus, port, memo=memo)
        if port != "signed":
            raise ValueError(
                "the production tape packet requires the complete signed port"
            )
        control, totals, borrow, carry, sample, steps = _observe_program_symbols(
            machine, program, ledger, memo
        )
        endpoint_control = machine.control(program.endpoint)
        if steps != program.steps or control != endpoint_control:
            raise ValueError(
                "innovation tape disagrees with exact endpoint parity seam"
            )
        if (
            type(physical_endpoint) is not int
            or type(physical_ticks) is not int
            or type(phase) is not int
            or physical_ticks != program.steps + program.one_symbols + phase
            or (
                physical_endpoint != program.endpoint
                if phase == 0
                else physical_endpoint != 3 * program.endpoint + 1
                or program.endpoint % 2 == 0
            )
        ):
            raise ValueError("physical endpoint does not match the normalized tape")
        return InnovationTapeObservation._issue(
            program.source,
            program.endpoint,
            physical_endpoint,
            modulus,
            physical_ticks,
            phase,
            program.steps,
            program.one_symbols,
            machine.class_count,
            tuple(totals),
            tuple(borrow),
            tuple(carry),
            tuple(sample),
        )


def boundary_macro_factors(macro: object) -> tuple[ParityFactor, ...]:
    """Return the exact normalized-word grammar for an issued family macro."""
    from number_compiler.sequences.collatz.border_return_grammar import (
        BorderReturnMacro,
        validate_border_return_macro,
    )
    from number_compiler.sequences.collatz.boundary_macros import (
        CollatzBoundaryMacro,
        validate_boundary_macro,
    )

    specs: tuple[tuple[tuple[int, ...], int], ...]
    if type(macro) is BorderReturnMacro:
        validate_border_return_macro(macro)
        specs = tuple(((bit,), length) for bit, length in macro.parts)
    elif type(macro) is CollatzBoundaryMacro:
        validate_boundary_macro(macro)
        specs = _boundary_macro_specs(macro)
    else:
        raise TypeError("boundary parity grammar needs an exact macro")
    result = tuple(ParityFactor(motif, repetitions) for motif, repetitions in specs)
    if (
        sum(factor.steps for factor in result) != macro.normalized_symbols
        or sum(factor.ones for factor in result) != macro.odd_symbols
        or result[0].motif[0] != macro.source & 1
    ):
        raise ValueError("boundary macro parity grammar disagrees with its guard")
    return result


__all__ = [
    "GlobalInnovationPortMoore",
    "InnovationTapeObservation",
    "NormalizedParityProgram",
    "ParityFactor",
    "boundary_macro_factors",
    "global_innovation_port_moore",
    "observe_parity_program",
]
