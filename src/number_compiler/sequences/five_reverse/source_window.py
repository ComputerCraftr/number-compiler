"""Finite, source-specific certificate metadata for five-reversal observations.

This record is an immutable selector and bound declaration, not an execution
handle. Its finite transition facts and conservative state-bit bound are
separate proof obligations; neither grants authority beyond this bounded window.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from number_compiler.arithmetic.contracts.input_validation import require_integer

_SEED196_SOURCE_WINDOW_SEAL: Final = (
    196,
    180,
    184,
    ((348, 960), (348, 215), (256, 215), (256, 260), (311, 260)),
    (3, 4, 2, 1),
    8,
    6,
)


@dataclass(frozen=True, slots=True)
class FiveFiniteSourceWindow:
    """An exact finite source prefix used to select a family observation."""

    seed: int
    start_generation: int
    terminal_generation: int
    borders: tuple[tuple[int, int], ...]
    inlets: tuple[int, ...]
    initial_state_bits: int
    bits_added_per_step_bound: int

    def __post_init__(self) -> None:
        require_integer(self.seed, "finite-window seed", 0)
        require_integer(self.start_generation, "window start", 0)
        require_integer(self.terminal_generation, "window terminal", 0)
        require_integer(self.initial_state_bits, "initial state bits", 0)
        require_integer(self.bits_added_per_step_bound, "bit-growth bound", 0)
        if self.start_generation >= self.terminal_generation:
            raise ValueError("finite source window must contain a transition")
        if self.initial_state_bits != self.seed.bit_length():
            raise ValueError("finite source window has a mismatched seed bit length")
        if type(self.borders) is not tuple or len(self.borders) != (
            self.terminal_generation - self.start_generation + 1
        ):
            raise ValueError("finite source window needs every endpoint border")
        if any(
            type(border) is not tuple
            or len(border) != 2
            or any(type(value) is not int or value < 0 for value in border)
            for border in self.borders
        ):
            raise TypeError("finite source window borders must be exact integer pairs")
        if type(self.inlets) is not tuple or len(self.inlets) != (
            self.terminal_generation - self.start_generation
        ):
            raise ValueError("finite source window needs one inlet per transition")
        if any(type(inlet) is not int or not 0 <= inlet <= 4 for inlet in self.inlets):
            raise ValueError(
                "finite source window inlet is outside the radix-five port"
            )

    @property
    def initial_border(self) -> tuple[int, int]:
        return self.borders[0]

    def supports(self, seed: int, generation: int, through_generation: int) -> bool:
        return (
            type(seed) is int
            and type(generation) is int
            and type(through_generation) is int
            and seed == self.seed
            and self.start_generation <= generation <= through_generation
            and generation < self.terminal_generation
            and through_generation <= self.terminal_generation
        )

    def state_bits_bound_through(self, generation: int) -> int:
        generation = require_integer(
            generation, "finite-window state bound generation", 0
        )
        if generation > self.terminal_generation:
            raise ValueError("finite-window bit bound exceeds its certified horizon")
        return self.initial_state_bits + (self.bits_added_per_step_bound * generation)


def validates_seed196_source_window(window: object) -> bool:
    """Authenticate selector metadata against a separate immutable declaration."""
    if type(window) is not FiveFiniteSourceWindow:
        return False
    exact_fields = (
        window.seed,
        window.start_generation,
        window.terminal_generation,
        window.borders,
        window.inlets,
        window.initial_state_bits,
        window.bits_added_per_step_bound,
    )
    if any(
        type(value) is not int
        for value in (
            window.seed,
            window.start_generation,
            window.terminal_generation,
            window.initial_state_bits,
            window.bits_added_per_step_bound,
        )
    ):
        return False
    if type(window.borders) is not tuple or any(
        type(border) is not tuple
        or len(border) != 2
        or any(type(value) is not int for value in border)
        for border in window.borders
    ):
        return False
    if type(window.inlets) is not tuple or any(
        type(inlet) is not int for inlet in window.inlets
    ):
        return False
    return exact_fields == _SEED196_SOURCE_WINDOW_SEAL


SEED196_SOURCE_WINDOW = FiveFiniteSourceWindow(*_SEED196_SOURCE_WINDOW_SEAL)
