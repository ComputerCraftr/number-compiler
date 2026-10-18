"""Lazy weighted carry and endpoint moment ports over a 2rev10 SLP.

This module observes an authenticated source and endpoint grammar. It never
replays physical transitions or materializes a carry word as a digit tape.
Exact large integers are bounded by ``max_bits``; modular summaries use
binary geometric composition over SLP repeats.
"""

from __future__ import annotations

from contextlib import AbstractContextManager, nullcontext
from dataclasses import dataclass, replace

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import SLPArena, SLPNode
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    compose_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    edge_phase,
    growth_ports,
)


@dataclass(frozen=True, slots=True)
class DecimalCarryPort:
    """Weighted decimal and threshold-carry summaries for one SLP root."""

    width: int
    forward: int
    reversed: int
    carry_word: int
    transfer: CarryFn
    first: int | None
    last: int | None
    modulus: int | None


def _reduce(value: int, modulus: int | None) -> int:
    return value if modulus is None else value % modulus


def _geometric(base: int, repetitions: int, modulus: int | None) -> int:
    """Compute ``1 + base + ... + base**(repetitions-1)`` in logarithmic time."""
    if repetitions < 0:
        raise ValueError("negative spatial repeat count")
    result_sum = 0
    block_power, block_sum = base, 1
    count = repetitions
    while count:
        if count & 1:
            result_sum = _reduce(result_sum * block_power + block_sum, modulus)
        count >>= 1
        if count:
            block_sum = _reduce(block_sum * block_power + block_sum, modulus)
            block_power = _reduce(block_power * block_power, modulus)
    return result_sum


def _validate_projection(
    roots: tuple[int, ...], modulus: int | None, max_bits: int
) -> None:
    if not roots:
        raise ValueError("at least one SLP root is required")
    if any(type(root) is not int or root < 0 for root in roots):
        raise ValueError("invalid double-reverse source SLP root")
    if type(max_bits) is not int or max_bits < 1:
        raise ValueError("carry port requires a positive exact bit budget")
    if modulus is not None and (type(modulus) is not int or modulus < 1):
        raise ValueError("carry port modulus must be a positive integer")
    if modulus is not None and modulus.bit_length() > max_bits:
        raise BlockContextBudgetExceeded(
            "double-reverse modular port exceeds the requested bit budget"
        )


def _summary_nodes(width: int, modulus: int | None) -> int:
    bits = (
        max(1, (3322 * width + 999) // 1000)
        if modulus is None
        else max(1, modulus.bit_length())
    )
    return 1 + 3 * ((bits + 63) // 64)


def _charged_fold_ports(
    arena: SLPArena,
    roots: tuple[int, ...],
    *,
    modulus: int | None,
    max_bits: int,
    ledger: ResourceLedger | None,
    scratch_owner: int | None,
) -> tuple[DecimalCarryPort, ...]:
    if (ledger is None) != (scratch_owner is None):
        raise ValueError("carry projection requires both ledger and scratch owner")
    if ledger is None:
        return _fold_ports(arena, roots, modulus=modulus, max_bits=max_bits)
    if type(arena) is LedgerSLPArena and arena.ledger is not ledger:
        raise ValueError("carry projection ledger does not own the SLP arena")
    return _fold_ports(
        arena,
        roots,
        modulus=modulus,
        max_bits=max_bits,
        ledger=ledger,
        scratch_owner=scratch_owner,
    )


def _fold_ports(
    arena: SLPArena,
    roots: tuple[int, ...],
    *,
    modulus: int | None,
    max_bits: int,
    ledger: ResourceLedger | None = None,
    scratch_owner: int | None = None,
) -> tuple[DecimalCarryPort, ...]:
    _validate_projection(roots, modulus, max_bits)
    if (ledger is None) != (scratch_owner is None):
        raise ValueError("carry fold requires both ledger and scratch owner")
    if any(root >= len(arena.nodes) for root in roots):
        raise ValueError("invalid double-reverse source SLP root")
    for root in roots:
        width = arena.nodes[root].length
        if modulus is None and max(1, (3322 * width + 999) // 1000) > max_bits:
            raise BlockContextBudgetExceeded(
                "double-reverse exact carry port exceeds the requested bit budget"
            )

    memo: dict[int, DecimalCarryPort] = {}
    tasks: list[tuple[int, bool]] = []
    retained_tasks = 0
    retained_entries = 0
    retained_nodes = 0

    def push(node_id: int, resolve: bool) -> None:
        nonlocal retained_tasks
        if ledger is not None:
            assert scratch_owner is not None
            ledger.reserve(scratch_owner, entries=1, nodes=1)
        try:
            tasks.append((node_id, resolve))
        except BaseException as error:
            if ledger is not None:
                assert scratch_owner is not None
                try:
                    ledger.release(scratch_owner, entries=1, nodes=1)
                except BaseException as cleanup_error:
                    raise error from cleanup_error
            raise
        retained_tasks += 1

    try:
        for root in reversed(roots):
            push(root, False)
        while tasks:
            node_id, resolve = tasks.pop()
            retained_tasks -= 1
            if ledger is not None:
                assert scratch_owner is not None
                ledger.release(scratch_owner, entries=1, nodes=1)
            if node_id in memo:
                continue
            node = arena.nodes[node_id]
            if not resolve:
                push(node_id, True)
                if node.kind == "CONCAT":
                    if node.right not in memo:
                        push(node.right, False)
                    if node.left not in memo:
                        push(node.left, False)
                elif node.kind == "REPEAT" and node.child not in memo:
                    push(node.child, False)
                continue

            if ledger is None:
                workspace: AbstractContextManager[None] = nullcontext(None)
            else:
                assert scratch_owner is not None
                workspace = ledger.reservation(
                    scratch_owner,
                    entries=0,
                    nodes=2 * _summary_nodes(node.length, modulus),
                )
            with workspace:
                port = _make_port(node, memo, arena, modulus)
            if port.width != node.length:
                raise AssertionError("weighted carry fold changed the source width")
            cost = _summary_nodes(node.length, modulus)
            if ledger is not None:
                assert scratch_owner is not None
                ledger.reserve(scratch_owner, entries=1, nodes=cost)
            try:
                memo[node_id] = port
            except BaseException as error:
                if ledger is not None:
                    assert scratch_owner is not None
                    try:
                        ledger.release(scratch_owner, entries=1, nodes=cost)
                    except BaseException as cleanup_error:
                        raise error from cleanup_error
                raise
            retained_entries += 1
            retained_nodes += cost
        return tuple(memo[root] for root in roots)
    finally:
        if ledger is not None:
            assert scratch_owner is not None
            if retained_tasks:
                ledger.release(
                    scratch_owner, entries=retained_tasks, nodes=retained_tasks
                )
            if retained_entries:
                ledger.release(
                    scratch_owner,
                    entries=retained_entries,
                    nodes=retained_nodes,
                )


def _make_port(
    node: SLPNode,
    memo: dict[int, DecimalCarryPort],
    arena: SLPArena,
    modulus: int | None,
) -> DecimalCarryPort:
    if node.kind == "EMPTY":
        return DecimalCarryPort(0, 0, 0, 0, CarryFn.ID, None, None, modulus)
    if node.kind == "TERM":
        digit = node.symbol
        if not 0 <= digit <= 9:
            raise ValueError("2rev10 decimal SLP contains a non-digit")
        bit = int(digit >= 5)
        return DecimalCarryPort(
            1,
            _reduce(digit, modulus),
            _reduce(digit, modulus),
            _reduce(bit, modulus),
            value_carry_fn(2 * digit, 10),
            digit,
            digit,
            modulus,
        )
    if node.kind == "CONCAT":
        left, right = memo[node.left], memo[node.right]
        left_scale = pow(10, left.width, modulus) if modulus else 10**left.width
        right_scale = pow(10, right.width, modulus) if modulus else 10**right.width
        return DecimalCarryPort(
            left.width + right.width,
            _reduce(left.forward * right_scale + right.forward, modulus),
            _reduce(right.reversed * left_scale + left.reversed, modulus),
            _reduce(left.carry_word * right_scale + right.carry_word, modulus),
            compose_carry_fn(right.transfer, left.transfer),
            left.first if left.width else right.first,
            right.last if right.width else left.last,
            modulus,
        )
    if node.kind == "REPEAT":
        child = memo[node.child]
        if child.width < 1 or node.count < 1:
            raise AssertionError("invalid repeated SLP port")
        base = pow(10, child.width, modulus) if modulus else 10**child.width
        factor = _geometric(base, node.count, modulus)
        return DecimalCarryPort(
            child.width * node.count,
            _reduce(child.forward * factor, modulus),
            _reduce(child.reversed * factor, modulus),
            _reduce(child.carry_word * factor, modulus),
            child.transfer,
            child.first,
            child.last,
            modulus,
        )
    raise AssertionError("unrecognized SLP node kind")


def decimal_carry_port(
    arena: SLPArena,
    root: int,
    *,
    modulus: int | None = None,
    max_bits: int = 4096,
    ledger: ResourceLedger | None = None,
    scratch_owner: int | None = None,
) -> DecimalCarryPort:
    """Project one source word's carry and numeric ports without a carry tape.

    Production callers provide both ledger parameters, which bound temporary
    summary storage before the fold. The no-ledger form remains useful to
    callers already applying an external resource boundary.
    """
    return _charged_fold_ports(
        arena,
        (root,),
        modulus=modulus,
        max_bits=max_bits,
        ledger=ledger,
        scratch_owner=scratch_owner,
    )[0]


@dataclass(frozen=True, slots=True)
class DoubleReverseClosedForm:
    """Lazy endpoint moments and source carry projection for physical T steps."""

    steps: int
    source: int
    target: int
    source_reverse: int
    target_reverse: int
    U: int
    H: int
    carry_word: int
    carry_correction: int
    final_carry: int
    carry_transfer: CarryFn
    modulus: int | None
    phase_in: int | None
    phase_out: int | None
    left_births: int | None
    right_births: int | None
    affine_gain: int | None
    affine_shift: int | None
    # An original seed may enter a certified cylinder only after a transient.
    # These fields describe the *suffix*, without pretending its affine
    # action is source-universal across the uncertified prefix.
    prefix_steps: int | None = None
    suffix_steps: int | None = None
    entry_value: int | None = None
    suffix_phase_in: int | None = None
    suffix_phase_out: int | None = None
    suffix_affine_gain: int | None = None
    suffix_affine_shift: int | None = None

    @property
    def matrix(self) -> tuple[tuple[int, int, int], ...]:
        """Exact (or modular) 3-by-3 endpoint action on ``(X, rev(X), 1)``."""
        if self.steps == 0:
            one = 1 if self.modulus is None else 1 % self.modulus
            return ((one, 0, 0), (0, one, 0), (0, 0, one))
        one = 1 if self.modulus is None else 1 % self.modulus
        return (
            (0, _reduce(2, self.modulus), _reduce(2 * self.H, self.modulus)),
            (0, one, self.U),
            (0, 0, one),
        )

    def then(self, after: DoubleReverseClosedForm) -> DoubleReverseClosedForm:
        """Join numerically adjacent actions, with exact chronological checks."""
        if type(after) is not DoubleReverseClosedForm:
            raise TypeError("temporal action composition requires an action")
        if self.modulus is not None or after.modulus is not None:
            raise ValueError("modular packets cannot certify source seams")
        if self.target != after.source:
            raise ValueError("temporal action source/target seam mismatch")
        if (
            self.phase_out is not None
            and after.phase_in is not None
            and self.phase_out != after.phase_in
        ):
            raise ValueError("temporal action edge-phase seam mismatch")
        steps = self.steps + after.steps
        u = self.U + after.U
        if self.steps == 0:
            h = after.H
        elif after.steps == 0:
            h = self.H
        else:
            h = self.U + after.H
        if steps and (
            self.source_reverse + u != after.target_reverse
            or 2 * (self.source_reverse + h) != after.target
        ):
            raise AssertionError("composed two-moment matrix lost its endpoint")

        affine_complete = all(
            value is not None
            for value in (
                self.affine_gain,
                self.affine_shift,
                after.affine_gain,
                after.affine_shift,
                self.left_births,
                after.left_births,
                self.right_births,
                after.right_births,
            )
        )
        gain: int | None = None
        shift: int | None = None
        left: int | None = None
        right: int | None = None
        if affine_complete:
            assert self.affine_gain is not None and self.affine_shift is not None
            assert after.affine_gain is not None and after.affine_shift is not None
            assert self.left_births is not None and self.right_births is not None
            assert after.left_births is not None and after.right_births is not None
            gain = after.affine_gain * self.affine_gain
            shift = after.affine_gain * self.affine_shift + after.affine_shift
            if after.target != gain * self.source + shift:
                raise AssertionError("composed skew affine action lost its endpoint")
            left = self.left_births + after.left_births
            right = self.right_births + after.right_births
        return DoubleReverseClosedForm(
            steps,
            self.source,
            after.target,
            self.source_reverse,
            after.target_reverse,
            u,
            h,
            self.carry_word,
            self.carry_correction,
            self.final_carry,
            self.carry_transfer,
            None,
            self.phase_in if affine_complete else None,
            after.phase_out if affine_complete else None,
            left,
            right,
            gain,
            shift,
        )

    def power_cycle(self, copies: int) -> DoubleReverseClosedForm:
        """Power only a numeric return, never a repeated border motif alone."""
        if type(copies) is not int or copies < 1:
            raise ValueError("cycle repeat count must be positive")
        if self.modulus is not None or self.source != self.target:
            raise ValueError("a repeated edge clock is not a numerical cycle")
        if copies == 1:
            return self
        if self.U != 0:
            raise AssertionError("returning numeric cycle has nonzero U")
        return DoubleReverseClosedForm(
            copies * self.steps,
            self.source,
            self.target,
            self.source_reverse,
            self.target_reverse,
            0,
            self.H,
            self.carry_word,
            self.carry_correction,
            self.final_carry,
            self.carry_transfer,
            None,
            self.phase_in,
            self.phase_out,
            None,
            None,
            None,
            None,
        )


def closed_form_from_roots(
    arena: SLPArena,
    source_root: int,
    target_root: int,
    steps: int,
    *,
    modulus: int | None = None,
    max_bits: int = 4096,
    ledger: ResourceLedger | None = None,
    scratch_owner: int | None = None,
    entry_root: int | None = None,
    prefix_steps: int | None = None,
) -> DoubleReverseClosedForm:
    """Project moments from endpoint SLPs, optionally including one suffix entry.

    When ``entry_root`` is provided, source, entry, and target summaries share
    one SLP fold. The optional prefix metadata describes an already-authenticated
    owner cursor; these numeric projections do not issue or authenticate it.
    """
    if type(steps) is not int or steps < 0:
        raise ValueError("closed-form step count must be nonnegative")
    if modulus is not None and (type(modulus) is not int or modulus < 1):
        raise ValueError("closed-form modulus must be positive")
    if (ledger is None) != (scratch_owner is None):
        raise ValueError("closed-form projection requires ledger and scratch owner")
    if type(source_root) is not int or not 0 <= source_root < len(arena.nodes):
        raise ValueError("invalid double-reverse source SLP root")
    if type(target_root) is not int or not 0 <= target_root < len(arena.nodes):
        raise ValueError("invalid double-reverse target SLP root")
    if (entry_root is None) != (prefix_steps is None):
        raise ValueError("suffix projection requires both entry root and prefix")
    if entry_root is not None and (
        type(entry_root) is not int or not 0 <= entry_root < len(arena.nodes)
    ):
        raise ValueError("invalid double-reverse suffix entry SLP root")
    if prefix_steps is not None and (
        type(prefix_steps) is not int or not 0 <= prefix_steps <= steps
    ):
        raise ValueError("invalid double-reverse suffix prefix length")

    effective_modulus = None if modulus is None else 10 * modulus
    roots = (
        (source_root, target_root)
        if entry_root is None
        else (source_root, entry_root, target_root)
    )
    projections = _charged_fold_ports(
        arena,
        roots,
        modulus=effective_modulus if modulus is not None else None,
        max_bits=max_bits,
        ledger=ledger,
        scratch_owner=scratch_owner,
    )
    if entry_root is None:
        start, end = projections
        entry = None
    else:
        start, entry, end = projections
    if start.last is None:
        raise ValueError("a physical 2rev10 source must be nonempty")
    if steps == 0 and start.forward != end.forward:
        raise ValueError("zero-step moment action changed its endpoint")
    if modulus is None:
        x0, x1 = start.forward, end.forward
        r0, r1 = start.reversed, end.reversed
        u = r1 - r0 if steps else 0
        h = x1 // 2 - r0 if steps else 0
        correction = -99 * (start.carry_word // 10) - 10 * int(start.last >= 5)
    else:
        m = modulus
        x0, x1 = start.forward % m, end.forward % m
        r0, r1 = start.reversed % m, end.reversed % m
        u = (r1 - r0) % m if steps else 0
        h = (end.forward // 2 - r0) % m if steps else 0
        correction = (-99 * (start.carry_word // 10) - 10 * int(start.last >= 5)) % m
    final_carry = int(start.last >= 5)
    if steps and end.forward % 2:
        raise AssertionError("2rev10 produced an odd physical endpoint")
    if steps == 1 and x1 != _reduce(2 * r0, modulus):
        raise AssertionError("one-step reverse/double port disagrees with endpoint")
    if steps == 2 and start.last != 0 and start.first != 5:
        gain = 1 + 9 * final_carry
        predicted = 4 * gain * x0 + 2 * gain * correction + 2 * final_carry
        if x1 != _reduce(predicted, modulus):
            raise AssertionError("two-step carry correction disagrees with endpoint")
    if steps and (
        _reduce(r0 + u, modulus) != r1 or _reduce(2 * (r0 + h), modulus) != x1
    ):
        raise AssertionError("closed-form moments disagree with the endpoint")

    phase = None
    phase_out = None
    left = right = affine_gain = affine_shift = None
    source_width = arena.nodes[source_root].length
    if source_width >= 5:
        phase = edge_phase(
            (symbol_at(arena, source_root, 0), symbol_at(arena, source_root, 1)),
            (
                symbol_at(arena, source_root, source_width - 2),
                symbol_at(arena, source_root, source_width - 1),
            ),
        )
    if phase is not None:
        target_width = arena.nodes[target_root].length
        if target_width < 5:
            raise AssertionError("certified cylinder contracted")
        phase_out = edge_phase(
            (symbol_at(arena, target_root, 0), symbol_at(arena, target_root, 1)),
            (
                symbol_at(arena, target_root, target_width - 2),
                symbol_at(arena, target_root, target_width - 1),
            ),
        )
        if phase_out != (phase + steps) % 4:
            raise AssertionError("certified 2rev10 edge phase did not advance")
        if steps % 2 == 0:
            f_steps = steps // 2
            left, right = growth_ports(phase, f_steps)
            if target_width != source_width + left + right:
                raise AssertionError("certified 2rev10 growth clock disagrees")
            if modulus is None:
                gain_bound = 2 * f_steps + (3322 * right + 999) // 1000 + 2
                if gain_bound + max(1, x0.bit_length()) > max_bits:
                    raise BlockContextBudgetExceeded(
                        "double-reverse affine port exceeds the requested bit budget"
                    )
                affine_gain = 4**f_steps * 10**right
            else:
                affine_gain = pow(4, f_steps, modulus) * pow(10, right, modulus)
                affine_gain %= modulus
            affine_shift = _reduce(x1 - affine_gain * x0, modulus)
            if f_steps == 1 and affine_gain != _reduce(
                4 * (1 + 9 * final_carry), modulus
            ):
                raise AssertionError("growth and affine gain disagree")
    carry_word = (
        start.carry_word
        if effective_modulus is None
        else start.carry_word % effective_modulus
    )
    if modulus is None:
        exact_outputs = (u, h, 2 * h, correction, affine_gain, affine_shift)
        if any(
            value is not None and abs(value).bit_length() > max_bits
            for value in exact_outputs
        ):
            raise BlockContextBudgetExceeded(
                "double-reverse moment port exceeds the requested bit budget"
            )
    result = DoubleReverseClosedForm(
        steps,
        x0,
        x1,
        r0,
        r1,
        u,
        h,
        carry_word,
        correction,
        final_carry,
        start.transfer,
        modulus,
        phase,
        phase_out,
        left,
        right,
        affine_gain,
        affine_shift,
    )
    if entry is not None and prefix_steps is not None:
        assert entry_root is not None
        suffix = _suffix_affine_projection(
            arena,
            entry_root,
            target_root,
            entry,
            end,
            steps - prefix_steps,
            prefix_steps,
            modulus=modulus,
            max_bits=max_bits,
        )
        if suffix is not None:
            result = replace(
                result,
                prefix_steps=suffix[0],
                suffix_steps=suffix[1],
                entry_value=suffix[2],
                suffix_phase_in=suffix[3],
                suffix_phase_out=suffix[4],
                suffix_affine_gain=suffix[5],
                suffix_affine_shift=suffix[6],
            )
    return result


def _suffix_affine_projection(
    arena: SLPArena,
    entry_root: int,
    target_root: int,
    entry: DecimalCarryPort,
    target: DecimalCarryPort,
    suffix_steps: int,
    prefix_steps: int,
    *,
    modulus: int | None,
    max_bits: int,
) -> tuple[int, int, int, int, int, int, int] | None:
    """Derive a cylinder suffix from the already folded entry/target ports."""
    if suffix_steps % 2:
        return None
    entry_width = arena.nodes[entry_root].length
    if entry_width < 5:
        return None
    phase = edge_phase(
        (symbol_at(arena, entry_root, 0), symbol_at(arena, entry_root, 1)),
        (
            symbol_at(arena, entry_root, entry_width - 2),
            symbol_at(arena, entry_root, entry_width - 1),
        ),
    )
    if phase is None:
        return None
    target_width = arena.nodes[target_root].length
    if target_width < 5:
        raise AssertionError("certified suffix contracted below its border")
    phase_out = edge_phase(
        (symbol_at(arena, target_root, 0), symbol_at(arena, target_root, 1)),
        (
            symbol_at(arena, target_root, target_width - 2),
            symbol_at(arena, target_root, target_width - 1),
        ),
    )
    if phase_out is None:
        raise AssertionError("certified suffix endpoint has no edge phase")
    if phase_out != (phase + suffix_steps) % 4:
        raise AssertionError("certified suffix edge phase did not advance")
    f_steps = suffix_steps // 2
    left, right = growth_ports(phase, f_steps)
    if target_width != entry_width + left + right:
        raise AssertionError("certified suffix growth clock disagrees")
    if modulus is None:
        entry_value = entry.forward
        target_value = target.forward
        gain_bound = 2 * f_steps + (3322 * right + 999) // 1000 + 2
        if gain_bound + max(1, entry_value.bit_length()) > max_bits:
            raise BlockContextBudgetExceeded(
                "double-reverse affine suffix exceeds the requested bit budget"
            )
        gain = 4**f_steps * 10**right
        shift = target_value - gain * entry_value
        if max(abs(gain), abs(shift)).bit_length() > max_bits:
            raise BlockContextBudgetExceeded(
                "double-reverse affine suffix exceeds the requested bit budget"
            )
        if target_value != gain * entry_value + shift:
            raise AssertionError("suffix affine projection lost its endpoint")
    else:
        entry_value = entry.forward % modulus
        target_value = target.forward % modulus
        gain = (pow(4, f_steps, modulus) * pow(10, right, modulus)) % modulus
        shift = (target_value - gain * entry_value) % modulus
        if (gain * entry_value + shift) % modulus != target_value:
            raise AssertionError("modular suffix affine projection lost its endpoint")
    return (
        prefix_steps,
        suffix_steps,
        entry_value,
        phase,
        phase_out,
        gain,
        shift,
    )


__all__ = [
    "DecimalCarryPort",
    "DoubleReverseClosedForm",
    "closed_form_from_roots",
    "decimal_carry_port",
]
