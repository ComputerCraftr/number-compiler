"""Verified immutable C^4 bimachine, with a complete fixed 50/90-port interface.

The checked-in artifact is generated offline from the exact four-fold physical
composition. Its tables describe all primitive states and symbols, not any
source field. Production never discovers this domain or advances four events.
"""

from __future__ import annotations

import hashlib
import zlib
from dataclasses import dataclass, field
from importlib.resources import files
from pathlib import Path
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import (
    _OPERATOR_IDS,
    BoundarySide,
    BoundaryState,
)
from number_compiler.arithmetic.contracts.block_power_types import BlockPower
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.diamond_actions import TemporalActionArena
    from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler


_HEADER = b"PC4KERN1" + bytes((2, 2, 4, 50, 90, 0, 0, 8, 7))
_RAW_SHA256 = "04f2a30ac31ed5de5542fa096475320bda6a3acdefeda922625795183b324dc3"
_PACKED_SHA256 = "681a6da9f9d5d6d125e4a9fab836e4ca43208a42aa9e51dd568d9a0c350ec494"


@dataclass(frozen=True, slots=True)
class PhysicalCollatzFourBlockEffect:
    base: int = field(default=2, init=False)
    blank: int = field(default=2, init=False)
    exponent: int = field(default=4, init=False)
    left_count: int = field(default=50, init=False)
    right_count: int = field(default=90, init=False)
    alphabet_size: int = field(default=3, init=False)
    blank_left_tail: int = field(default=8, init=False)
    blank_right_tail: int = field(default=7, init=False)
    stable_blank_output: bool = field(default=True, init=False)
    supports_predecessor_trace: bool = field(default=False, init=False)
    eager_boundary_quotient: bool = field(default=True, init=False)
    kernel_name: str = field(default="physical-collatz-four-50x90-v1", init=False)
    storage_bytes: int = field(default=866, init=False)
    uncompressed_bytes: int = field(default=13937, init=False)
    node_id: int = field(
        default_factory=lambda: next(_OPERATOR_IDS), init=False, compare=False
    )
    left_transitions: bytes = field(init=False, repr=False)
    right_transitions: bytes = field(init=False, repr=False)
    outputs: bytes = field(init=False, repr=False)

    def __post_init__(self) -> None:
        packed = (
            Path(str(files("number_compiler")))
            / "kernels"
            / "physical_collatz_four.zlib"
        ).read_bytes()
        if hashlib.sha256(packed).hexdigest() != _PACKED_SHA256:
            raise ValueError("physical C^4 artifact digest mismatch")
        raw = zlib.decompress(packed)
        if len(raw) != self.uncompressed_bytes or raw[:17] != _HEADER:
            raise ValueError("physical C^4 artifact header mismatch")
        object.__setattr__(self, "left_transitions", raw[17:167])
        object.__setattr__(self, "right_transitions", raw[167:437])
        object.__setattr__(self, "outputs", raw[437:])
        self.validate()

    def validate(self) -> None:
        integers = (
            self.base,
            self.blank,
            self.exponent,
            self.left_count,
            self.right_count,
            self.alphabet_size,
            self.blank_left_tail,
            self.blank_right_tail,
            self.storage_bytes,
            self.uncompressed_bytes,
        )
        flags = (
            self.stable_blank_output,
            self.supports_predecessor_trace,
            self.eager_boundary_quotient,
        )
        if (
            any(type(value) is not int for value in integers)
            or integers != (2, 2, 4, 50, 90, 3, 8, 7, 866, 13937)
            or any(type(value) is not bool for value in flags)
            or flags != (True, False, True)
            or type(self.kernel_name) is not str
            or self.kernel_name != "physical-collatz-four-50x90-v1"
            or type(self.node_id) is not int
            or self.node_id < 0
        ):
            raise ValueError("physical C^4 metadata does not match its certificate")
        tables = (self.left_transitions, self.right_transitions, self.outputs)
        if any(type(table) is not bytes for table in tables) or tuple(
            map(len, tables)
        ) != (150, 270, 13500):
            raise ValueError(
                "physical C^4 tables are not the verified finite interface"
            )
        if hashlib.sha256(_HEADER + b"".join(tables)).hexdigest() != _RAW_SHA256:
            raise ValueError("physical C^4 behavior does not match its certificate")

    @property
    def canonical_key(self) -> tuple[object, ...]:
        # Exact bytes remain in equality: digest collisions cannot alias kernels.
        return (
            "verified-physical-collatz-four-v1",
            self.base,
            self.blank,
            self.exponent,
            self.left_count,
            self.right_count,
            self.blank_left_tail,
            self.blank_right_tail,
            self.stable_blank_output,
            self.left_transitions,
            self.right_transitions,
            self.outputs,
        )

    @staticmethod
    def _side(side: BoundarySide) -> None:
        if type(side) is not BoundarySide:
            raise ValueError("invalid physical C^4 boundary side")

    @staticmethod
    def _state(state: BoundaryState, count: int) -> int:
        if type(state) is not int or not 0 <= state < count:
            raise ValueError("value outside physical C^4 boundary domain")
        return state

    def initial(self, side: BoundarySide) -> int:
        self._side(side)
        return 0

    def boundary_universe(
        self, side: BoundarySide, *, max_states: int | None = None
    ) -> tuple[int, ...] | None:
        self._side(side)
        count = self.left_count if side is BoundarySide.LEFT else self.right_count
        return (
            None
            if max_states is not None and max_states < count
            else tuple(range(count))
        )

    def advance(self, side: BoundarySide, state: BoundaryState, symbol: int) -> int:
        self._side(side)
        self._state(symbol, 3)
        table = (
            self.left_transitions
            if side is BoundarySide.LEFT
            else self.right_transitions
        )
        count = self.left_count if side is BoundarySide.LEFT else self.right_count
        return table[self._state(state, count) * 3 + symbol]

    def emit(self, left: BoundaryState, symbol: int, right: BoundaryState) -> int:
        self._state(symbol, 3)
        return self.outputs[
            (self._state(left, 50) * 3 + symbol) * 90 + self._state(right, 90)
        ]

    def predecessor(self, side: BoundarySide, state: BoundaryState) -> None:
        self._side(side)

    def operator_nodes(self) -> int:
        return 1

    def runtime_stats(self) -> dict[str, int]:
        return {"operator_nodes": 1}


def is_verified_physical_four(effect: object) -> bool:
    if type(effect) is not PhysicalCollatzFourBlockEffect:
        return False
    effect.validate()
    return True


def compile_physical_power(compiler: LazyCompiler, steps: int) -> BlockPower:
    """Compatibility facade for the production primitive-law compiler."""
    from number_compiler.sequences.collatz.compilation import (
        compile_collatz_physical_power,
    )

    return compile_collatz_physical_power(compiler, steps)


def compile_physical_diamond(
    compiler: LazyCompiler, actions: TemporalActionArena, steps: int
) -> ActionProgramID:
    """Import the same physical compiler DAG used by the public descriptor."""
    if actions.compiler is not compiler:
        raise ValueError("temporal actions belong to another compiler")
    power = compile_physical_power(compiler, steps)
    return actions.identity if power.root is None else actions.intern(power.root)
