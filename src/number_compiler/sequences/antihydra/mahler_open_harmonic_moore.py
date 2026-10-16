"""NC16 Mahler-specific conditional *open* multiradix Moore quotient.

Transfers the NC16 2rev10 *conditional action algorithm*, not its unrelated
reversal stencil. The high binary inlet is always a typed, source-certified
value. This finite bank neither wraps an unknown interior nor guesses a
periodic boundary from a repeated harmonic label.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.functions.finite_observer import (
    class_members,
    minimize_finite_observer,
    partition_quotient_rows,
    partition_representatives,
)
from number_compiler.arithmetic.functions.partial_count_action import (
    ActionUniverse,
    PartialCountAction,
)
from number_compiler.sequences.antihydra.mahler_harmonic_ring import (
    MahlerFixedOddHarmonicRing,
)


@dataclass(frozen=True, slots=True)
class MahlerOpenBankState:
    binary: int
    five: int
    phase: int


@dataclass(frozen=True, slots=True)
class MahlerOpenEmission:
    decimal_digit: int
    binary_xor: int
    decimal_borrow: int
    phase: int

    @property
    def phase_counts(self) -> tuple[int, ...]:
        """F5 six-phase / XOR / borrow channels, in three banks of six."""
        out = [0] * 18
        out[self.phase] = self.decimal_digit % 5
        out[6 + self.phase] = self.binary_xor
        out[12 + self.phase] = self.decimal_borrow
        return tuple(out)


def _entry(
    ring: MahlerFixedOddHarmonicRing,
    state: MahlerOpenBankState,
    inlet: int,
    *,
    bits: int,
    places: int,
    position: int,
) -> tuple[MahlerOpenBankState, MahlerOpenEmission] | None:
    a = ring.exponent
    if not 0 <= inlet < 1 << a:
        raise ValueError("open bank inlet has wrong width")
    source_mod = 1 << bits
    five_mod = 5**places
    odd_guard, guard_mod = MahlerFixedOddHarmonicRing.source_cylinder(a, 1)
    if state.binary % guard_mod != odd_guard:
        return None
    before = state.binary + (inlet << bits)
    numerator = ring.p * before + ring.j
    if numerator % ring.q:
        return None
    next_binary = (numerator // ring.q) % source_mod
    next_five = (ring.p * state.five + ring.j) * pow(ring.q, -1, five_mod) % five_mod
    two_mod = 1 << places
    old_dec = (state.binary % two_mod) + two_mod * (
        ((state.five - (state.binary % two_mod)) * pow(two_mod, -1, five_mod))
        % five_mod
    )
    new_dec = (next_binary % two_mod) + two_mod * (
        ((next_five - (next_binary % two_mod)) * pow(two_mod, -1, five_mod)) % five_mod
    )
    unit = 10**position
    decimal_digit = new_dec // unit % 10
    xor = (state.binary ^ next_binary) >> position & 1
    borrow = 0
    for j in range(position + 1):
        borrow = int(new_dec // (10**j) % 10 < old_dec // (10**j) % 10 + borrow)
    emission = MahlerOpenEmission(decimal_digit, xor, borrow, state.phase)
    return MahlerOpenBankState(next_binary, next_five, (state.phase + 1) % 6), emission


@dataclass(frozen=True, slots=True)
class MahlerConditionalOpenMoore:
    """Finite, future-output Moore quotient under every declared inlet letter."""

    source: int
    exponent: int
    binary_bits: int
    five_places: int
    position: int
    states: tuple[MahlerOpenBankState, ...]
    class_ids: tuple[int, ...]
    class_count: int
    initial_class: int
    transitions: tuple[tuple[int | None, ...], ...]
    outputs: tuple[tuple[MahlerOpenEmission | None, ...], ...]
    alphabet: tuple[int, ...]
    action_universe: ActionUniverse

    @classmethod
    def compile(
        cls,
        ring: MahlerFixedOddHarmonicRing,
        *,
        binary_bits: int,
        five_places: int,
        position: int = 0,
        max_states: int = 4096,
    ) -> MahlerConditionalOpenMoore:
        """Build the finite input graph for this source; no process cache."""
        if type(ring) is not MahlerFixedOddHarmonicRing:
            raise TypeError("conditional Moore construction requires an admitted ring")
        ring.__post_init__()
        return cls._compile_uncached(
            ring,
            binary_bits=binary_bits,
            five_places=five_places,
            position=position,
            max_states=max_states,
        )

    @classmethod
    def _compile_uncached(
        cls,
        ring: MahlerFixedOddHarmonicRing,
        *,
        binary_bits: int,
        five_places: int,
        position: int = 0,
        max_states: int = 4096,
    ) -> MahlerConditionalOpenMoore:
        if type(binary_bits) is not int or not ring.exponent + 1 <= binary_bits <= 12:
            raise ValueError(
                "open bank needs at least exponent+1 binary bits, at most 12"
            )
        if type(five_places) is not int or not 1 <= five_places <= min(binary_bits, 4):
            raise ValueError("open five-adic precision must be in 1..4")
        if type(position) is not int or not 0 <= position < five_places:
            raise ValueError("open bank digit position exceeds five-adic precision")
        if type(max_states) is not int or max_states < 1:
            raise ValueError("positive state budget required")
        if ring.exponent > 5:
            raise BlockContextBudgetExceeded("open bank input alphabet is too large")
        alphabet = tuple(range(1 << ring.exponent))
        initial = MahlerOpenBankState(
            ring.source % (1 << binary_bits), ring.source % (5**five_places), 0
        )
        states = [initial]
        locations = {initial: 0}
        rows: list[tuple[int | None, ...]] = []
        emissions: list[tuple[MahlerOpenEmission | None, ...]] = []
        queue: deque[MahlerOpenBankState] = deque((initial,))
        while queue:
            state = queue.popleft()
            dest_row: list[int | None] = []
            obs_row: list[MahlerOpenEmission | None] = []
            for letter in alphabet:
                result = _entry(
                    ring,
                    state,
                    letter,
                    bits=binary_bits,
                    places=five_places,
                    position=position,
                )
                if result is None:
                    dest_row.append(None)
                    obs_row.append(None)
                    continue
                target, observation = result
                if target not in locations:
                    if len(states) >= max_states:
                        raise BlockContextBudgetExceeded(
                            "open Mahler future graph exceeded state budget"
                        )
                    locations[target] = len(states)
                    states.append(target)
                    queue.append(target)
                dest_row.append(locations[target])
                obs_row.append(observation)
            rows.append(tuple(dest_row))
            emissions.append(tuple(obs_row))
        labels = tuple(
            tuple(
                None
                if emission is None
                else (
                    emission.decimal_digit,
                    emission.binary_xor,
                    emission.decimal_borrow,
                    emission.phase,
                )
                for emission in row
            )
            for row in emissions
        )
        minimized = minimize_finite_observer(rows, labels)
        ids = minimized.class_ids
        num_classes = minimized.classes
        reps = partition_representatives(ids, num_classes)
        reduced_rows = partition_quotient_rows(rows, ids, num_classes)
        groups = class_members(ids, num_classes)
        reduced_emissions: list[tuple[MahlerOpenEmission | None, ...]] = []
        for representative, group in zip(reps, groups, strict=True):
            representative_outputs = emissions[representative]
            if any(emissions[state] != representative_outputs for state in group):
                raise ArithmeticError("Moore class merges conflicting current outputs")
            reduced_emissions.append(representative_outputs)
        action_universe = ActionUniverse(num_classes, 18)
        return cls(
            ring.source,
            ring.exponent,
            binary_bits,
            five_places,
            position,
            tuple(states),
            ids,
            num_classes,
            ids[0],
            reduced_rows,
            tuple(reduced_emissions),
            alphabet,
            action_universe,
        )

    def letter(self, input_value: int) -> PartialCountAction:
        if type(input_value) is not int or input_value not in self.alphabet:
            raise ValueError("open input is not in declared source inlet alphabet")
        idx = input_value
        return PartialCountAction(
            steps=1,
            targets=tuple(row[idx] for row in self.transitions),
            counts=tuple(
                None if (emission := row[idx]) is None else emission.phase_counts
                for row in self.outputs
            ),
            owner=self.action_universe,
        )

    def word(self, letters: tuple[int, ...]) -> PartialCountAction:
        result = PartialCountAction.identity(self.action_universe)
        for letter in letters:
            result = result.then(self.letter(letter))
        return result

    def source_certified_path(
        self,
        ring: MahlerFixedOddHarmonicRing,
        repetitions: int,
        *,
        max_discovery: int = 64,
    ) -> tuple[int, tuple[int, ...], str]:
        """No repeated inlet is accepted unless source-wide cone proves it."""
        if (
            ring.exponent != self.exponent
            or ring.source % (1 << self.binary_bits) != self.states[0].binary
            or ring.source % (5**self.five_places) != self.states[0].five
            or not ring.admits(repetitions)
        ):
            raise ValueError("finite inlet program belongs to another source cylinder")
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("nonnegative event count needed")
        if (
            ring.defect_valuation
            >= ring.exponent * repetitions + self.binary_bits + ring.exponent
            and repetitions
        ):
            inlet = ring.inlet(0, self.binary_bits)
            action = self.letter(inlet).power(repetitions)
            mode = "constant-inlet-source-cone"
        elif repetitions <= max_discovery:
            letters = tuple(ring.inlet(i, self.binary_bits) for i in range(repetitions))
            action = self.word(letters)
            mode = "literal-source-certified-inlets"
        else:
            raise BlockContextBudgetExceeded(
                "nonperiodic open inlets require explicit source discovery"
            )
        target = action.targets[self.initial_class]
        counts = action.counts[self.initial_class]
        if target is None or counts is None:
            raise ArithmeticError(
                "source-certified open ring refused an admissible macro"
            )
        low = ring.binary_residue(self.binary_bits, repetitions)
        five = ring.odd_modulus_residue(5**self.five_places, repetitions)
        expected_state = MahlerOpenBankState(low, five, repetitions % 6)
        try:
            expected_index = self.states.index(expected_state)
        except ValueError as exc:
            raise ArithmeticError(
                "open-ring endpoint is outside its declared states"
            ) from exc
        if self.class_ids[expected_index] != target:
            raise ArithmeticError("open-ring Moore endpoint differs from source CRT")
        return target, counts, mode


__all__ = ("MahlerConditionalOpenMoore", "MahlerOpenBankState", "MahlerOpenEmission")
