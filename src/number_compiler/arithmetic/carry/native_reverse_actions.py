"""Bounded optional kernels. The receiving sequence owner issues the output."""

from __future__ import annotations

import os
from collections.abc import Callable
from contextlib import ExitStack
from dataclasses import dataclass
from functools import cache
from importlib import import_module
from typing import TYPE_CHECKING, Protocol, TypeVar, cast

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.radix import iter_digits_lsd
from number_compiler.resources.metric_keys import native_reverse as _keys

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger

_T = TypeVar("_T")
_MODULE = "number_compiler.kernels._reverse_quotients"
_TABLE_CAP = 4 * 1024 * 1024
_SCRATCH_CAP = 64 * 1024 * 1024
_MAX_GUARD_NODES = 8192


@dataclass(frozen=True, slots=True)
class DiagonalWork:
    tiles: int
    fringe_gates: int
    rows: int
    word_updates: int
    table_entries: int
    table_bytes: int
    setup_ms: float
    evaluation_ms: float


@dataclass(frozen=True, slots=True)
class PairWork:
    states: int
    bands: int
    joins: int
    pulls: int
    births: int
    table_bytes: int
    hinge_cells: int = 0
    joint_bands: int = 0
    joint_columns: int = 0
    joint_probes: int = 0
    joint_collar_cells: int = 0
    joint_clock_13: int = 0
    joint_clock_7: int = 0
    joint_clock_two_births: int = 0
    joint_clock_one_birth: int = 0
    join_bank_probes: int = 0
    join_bank_builds: int = 0
    join_bank_row_compares: int = 0
    join_bank_slots: int = 0


class _Kernels(Protocol):
    def multiply(
        self, source: str, multiplier: int, steps: int, side: int
    ) -> tuple[str, tuple[int, int, int, int, int, int, float, float]]: ...

    def add(
        self, source: bytes, steps: int, height: int, width: int, max_bytes: int
    ) -> tuple[bytes, tuple[int, int, int, int, int, int]]: ...

    def add_folded(
        self, half: bytes, center: int, steps: int, max_bytes: int
    ) -> tuple[bytes, int, tuple[int, ...]]: ...

    def guard98(
        self, interior: bytes, returns: int, endpoint: bool, node_cap: int
    ) -> tuple[int, int, int]: ...


@cache
def _load() -> _Kernels | None:
    try:
        return cast(
            _Kernels, import_module("number_compiler.kernels._reverse_quotients")
        )
    except ModuleNotFoundError as error:
        if error.name != _MODULE:
            raise
        return None


def _reserve(stack: ExitStack, ledger: ResourceLedger, owner: int, slots: int) -> bool:
    try:
        stack.enter_context(ledger.reservation(owner, nodes=slots, entries=slots))
    except BlockContextBudgetExceeded:
        return False
    return True


def _decimal(value: int) -> str:
    try:
        return str(value)
    except ValueError:
        digits = bytes(digit + 48 for digit in iter_digits_lsd(value, 10))
        return digits[::-1].decode("ascii")


def diagonal_endpoint(
    ledger: ResourceLedger,
    scratch_owner: int,
    value: int,
    multiplier: int,
    steps: int,
    max_state_bits: int,
    receive: Callable[[str, DiagonalWork], _T],
) -> _T | None:
    """Apply a bounded diagonal and give its result to the charged receiver."""
    if multiplier not in (2, 5) or value < 0:
        raise ValueError("invalid reflected diagonal source")
    minimum_steps = 128 if multiplier == 5 else 512
    if multiplier == 5 and value.bit_length() <= 512:
        minimum_steps = 64
    if multiplier == 2 and value.bit_length() >= 425:
        minimum_steps = 256
    if not minimum_steps <= steps <= 1_000_000 or value == 0:
        return None
    bits = value.bit_length()
    width = (bits * 30103 + 99999) // 100000
    if width > 32 * steps or (3322 * (width + steps) + 999) // 1000 > max_state_bits:
        return None
    if ledger.max_nodes is not None or ledger.max_cache_entries is not None:
        return None
    native = _load()
    if native is None:
        return None

    side = 3 if steps < 8192 else 4
    slots = 128 * 10**side + 256 * (width + steps + 256)
    if slots > _SCRATCH_CAP:
        return None
    with ExitStack() as stack:
        if not _reserve(stack, ledger, scratch_owner, slots):
            return None
        digits, counters = native.multiply(_decimal(value), multiplier, steps, side)
        work = DiagonalWork(*counters)
        if (
            not digits
            or not digits.isascii()
            or not digits.isdecimal()
            or (len(digits) > 1 and digits[0] == "0")
            or len(digits) > width + steps
            or work.rows
            or work.word_updates
            or work.table_bytes > slots
        ):
            raise RuntimeError("invalid native diagonal endpoint")
        ledger.bump(_keys.NATIVE_DIAGONAL_TILES, work.tiles)
        ledger.bump(_keys.NATIVE_DIAGONAL_FRINGE_GATES, work.fringe_gates)
        ledger.bump(_keys.NATIVE_DIAGONAL_TABLE_ENTRIES, work.table_entries)
        ledger.bump(_keys.NATIVE_DIAGONAL_TABLE_BYTES, work.table_bytes)
        return receive(digits, work)


def _pair_admission(
    ledger: ResourceLedger, width: int, steps: int
) -> tuple[_Kernels, int] | None:
    if not 512 <= steps <= 65536 or width <= 0:
        return None
    if ledger.max_nodes is not None or ledger.max_cache_entries is not None:
        return None
    slots = _TABLE_CAP + 128 * (width + steps + 16)
    if slots > _SCRATCH_CAP:
        return None
    native = _load()
    return None if native is None else (native, slots)


def _record_pair_work(ledger: ResourceLedger, work: PairWork) -> None:
    ledger.bump(_keys.NATIVE_PAIR_BANDS, work.bands)
    ledger.bump(_keys.NATIVE_PAIR_JOINS, work.joins)
    ledger.bump(_keys.NATIVE_PAIR_PULLS, work.pulls)
    ledger.bump(_keys.NATIVE_PAIR_TABLE_BYTES, work.table_bytes)
    if work.join_bank_probes or work.join_bank_row_compares:
        ledger.bump(_keys.NATIVE_PAIR_BANK_PROBES, work.join_bank_probes)
        ledger.bump(_keys.NATIVE_PAIR_BANK_BUILDS, work.join_bank_builds)
        ledger.bump(_keys.NATIVE_PAIR_BANK_ROW_COMPARES, work.join_bank_row_compares)
        ledger.bump(_keys.NATIVE_PAIR_BANK_SLOTS, work.join_bank_slots)
    if work.hinge_cells:
        ledger.bump(_keys.NATIVE_PAIR_HINGE_CELLS, work.hinge_cells)
    if work.joint_bands or work.joint_probes:
        ledger.bump(_keys.NATIVE_PAIR_JOINT_BANDS, work.joint_bands)
        ledger.bump(_keys.NATIVE_PAIR_JOINT_COLUMNS, work.joint_columns)
        ledger.bump(_keys.NATIVE_PAIR_JOINT_PROBES, work.joint_probes)
        ledger.bump(_keys.NATIVE_PAIR_JOINT_COLLAR_CELLS, work.joint_collar_cells)
        ledger.bump(_keys.NATIVE_PAIR_JOINT_CLOCK_13, work.joint_clock_13)
        ledger.bump(_keys.NATIVE_PAIR_JOINT_CLOCK_7, work.joint_clock_7)
        if work.joint_clock_one_birth:
            ledger.bump(
                _keys.NATIVE_PAIR_JOINT_CLOCK_ONE_BIRTH, work.joint_clock_one_birth
            )
        if work.joint_clock_two_births:
            ledger.bump(
                _keys.NATIVE_PAIR_JOINT_CLOCK_TWO_BIRTHS, work.joint_clock_two_births
            )


def native_pair_action(
    ledger: ResourceLedger,
    scratch_owner: int,
    source_pairs: bytes | Callable[[], bytes],
    steps: int,
    receive: Callable[[bytes, PairWork], _T],
    *,
    source_width: int | None = None,
) -> _T | None:
    """Run the finite causal kernel, keeping the exact pairs charged until use."""
    width = len(source_pairs) if isinstance(source_pairs, bytes) else source_width
    if width is None:
        raise ValueError("deferred Q19 pairs require an authenticated width")
    admitted = _pair_admission(ledger, width, steps)
    if admitted is None:
        return None
    native, slots = admitted
    with ExitStack() as stack:
        if not _reserve(stack, ledger, scratch_owner, slots):
            return None
        payload = source_pairs() if callable(source_pairs) else source_pairs
        if len(payload) != width:
            raise ValueError("native Q19 source width changed during admission")
        pairs, counters = native.add(
            payload, steps, 2, 2 if steps >= 32768 else 1, _TABLE_CAP
        )
        work = PairWork(*counters)
        if (
            not pairs
            or not 0 <= work.births <= steps
            or len(pairs) != width + work.births
            or pairs != pairs[::-1]
            or max(pairs) > 18
            or work.table_bytes > _TABLE_CAP
        ):
            raise RuntimeError("invalid native causal endpoint")
        _record_pair_work(ledger, work)
        return receive(pairs, work)


def native_folded_pair_action(
    ledger: ResourceLedger,
    scratch_owner: int,
    source_half: Callable[[], bytes],
    center: int | None,
    steps: int,
    receive: Callable[[bytes, int | None, PairWork], _T],
    *,
    source_width: int,
) -> _T | None:
    """Run an authenticated half-field and return its exact center and half."""
    admitted = _pair_admission(ledger, source_width, steps)
    if admitted is None:
        return None
    native, slots = admitted
    if not callable(getattr(native, "add_folded", None)):
        return None
    with ExitStack() as stack:
        if not _reserve(stack, ledger, scratch_owner, slots):
            return None
        half = source_half()
        if 2 * len(half) + (center is not None) != source_width:
            raise ValueError("native Q19 source width changed during admission")
        joint = getattr(native, "add_folded_joint4", None)
        if os.environ.get("NUMBER_COMPILER_ENABLE_Q19_JOINT4") == "1" and callable(
            joint
        ):
            apply_joint = cast(
                Callable[[bytes, int, int, int], tuple[bytes, int, tuple[int, ...]]],
                joint,
            )
            pairs, raw_center, counters = apply_joint(
                half, -1 if center is None else center, steps, _TABLE_CAP
            )
        else:
            pairs, raw_center, counters = native.add_folded(
                half, -1 if center is None else center, steps, _TABLE_CAP
            )
        work = PairWork(*counters)
        joint_births = (
            3 * (work.joint_clock_13 + work.joint_clock_7)
            + (2 * work.joint_clock_two_births)
            + work.joint_clock_one_birth
        )
        if (
            not -1 <= raw_center <= 9
            or not 0 <= work.births <= steps
            or 2 * len(pairs) + (raw_center >= 0) != source_width + work.births
            or (pairs and (not 0 < pairs[0] <= 18 or max(pairs) > 18))
            or (not pairs and raw_center < 0)
            or work.table_bytes > _TABLE_CAP
            or min(
                work.join_bank_probes,
                work.join_bank_builds,
                work.join_bank_row_compares,
                work.join_bank_slots,
            )
            < 0
            or work.join_bank_builds > work.join_bank_probes
            or work.join_bank_builds > work.join_bank_slots
            or 2 * work.join_bank_probes > work.joins
            or work.join_bank_slots > _TABLE_CAP // 4
            or (work.join_bank_slots == 0 and work.join_bank_probes != 0)
            or 4 * work.joint_bands > steps
            or not 0 <= work.joint_bands <= work.bands
            or min(
                work.joint_clock_13,
                work.joint_clock_7,
                work.joint_clock_two_births,
                work.joint_clock_one_birth,
            )
            < 0
            or not 0 <= work.births - joint_births <= steps - 4 * work.joint_bands
            or work.joint_probes < 0
            or work.joint_collar_cells < 0
            or work.joint_columns < 48 * work.joint_bands
            or work.joint_clock_13
            + work.joint_clock_7
            + work.joint_clock_two_births
            + work.joint_clock_one_birth
            != work.joint_bands
        ):
            raise RuntimeError("invalid native folded causal endpoint")
        _record_pair_work(ledger, work)
        return receive(pairs, None if raw_center < 0 else raw_center, work)


@dataclass(frozen=True, slots=True)
class GuardProjection:
    """Conditional border response before binding to the physical source."""

    mask: int
    nodes: int
    appends: int
    endpoint: bool

    @property
    def admitted(self) -> bool:
        return self.mask != 0 and not self.mask & 1

    @property
    def endpoint_sums(self) -> tuple[int, ...]:
        if not self.endpoint:
            raise ValueError("the endpoint projection was not requested")
        return tuple(value for value in range(19) if self.mask & (2 << value))

    def normalized_factors(
        self, returns: int, source_q: int
    ) -> tuple[tuple[tuple[int, int], tuple[int, int]], ...]:
        inverse = pow(2, -returns, 99)

        def lifted(value: int) -> tuple[int, int]:
            residue = value % 99
            return (residue, 0) if residue <= 49 else (0, 99 - residue)

        constant = lifted(17 * inverse - 17)
        return tuple(
            (constant, lifted((value - 17 * returns) * inverse - source_q))
            for value in self.endpoint_sums
        )


def guard_projection(
    ledger: ResourceLedger,
    scratch_owner: int,
    interior: bytes,
    returns: int,
    *,
    endpoint: bool = False,
    node_cap: int = _MAX_GUARD_NODES,
) -> GuardProjection | None:
    if not 1 <= returns <= 512 or not interior or not 1 <= node_cap <= _MAX_GUARD_NODES:
        return None
    if ledger.max_nodes is not None or ledger.max_cache_entries is not None:
        return None
    native = _load()
    if native is None:
        return None

    slots = 320 * node_cap + len(interior) + 128 * (2 * returns + 1)
    if slots > _SCRATCH_CAP:
        return None
    with ExitStack() as stack:
        if not _reserve(stack, ledger, scratch_owner, slots):
            return None
        mask, nodes, appends = native.guard98(interior, returns, endpoint, node_cap)
        if not 0 < mask < (1 << (20 if endpoint else 2)) or nodes + appends > node_cap:
            raise RuntimeError("invalid native conditional guard projection")
        return GuardProjection(mask, nodes, appends, endpoint)
