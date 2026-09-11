"""Store-free collatz microblock projection operations."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
)
from number_compiler.projection.microblock_cache import (
    ExactMicroblock,
)

if TYPE_CHECKING:
    from devtools.proofs.lazy_collatz import LazyCollatzApplication


def _program_block(
    self: LazyCollatzApplication, program: ActionProgramID, block: int
) -> int:
    from devtools.proofs.lazy_collatz import Mul3Carry

    """Evaluate one aligned future microblock through the program DAG.

    The evaluator is iterative.  A multiplication block requests bounded
    blocks of its immediate provider and carries only the three-state
    ``Mul3Carry`` value while scanning them.  It never rebuilds the full
    earlier pipeline and never allocates a future word.
    """
    root_key = self._microblock_key(program, block)
    found = self._microblocks.get(root_key)
    if found is not None:
        return found.encoded
    pending: list[tuple[ActionProgramID, int, bool]] = [(program, block, False)]
    # Completion markers contain identities only. Exact block payloads live
    # exclusively in the capped MicroblockCache; retaining them in this
    # scheduler used to create an uncapped transient future-word prefix.
    built: set[tuple[int, int]] = set()
    while pending:
        current, current_block, _ready = pending.pop()
        local = current.local_id, current_block
        if local in built:
            retained = self._microblocks.get(
                self._microblock_key(current, current_block)
            )
            if retained is not None:
                continue
            built.remove(local)
        key = self._microblock_key(current, current_block)
        cached = self._microblocks.get(key)
        if cached is not None:
            built.add(local)
            continue
        node = self._programs[current.local_id]
        if node.kind == "identity":
            value = self._source_block(current_block)
        else:
            before = ActionProgramID(self.token, "program", 0)
            operation = node
            if node.kind == "compose":
                before = ActionProgramID(self.token, "program", node.left)
                operation = self._programs[node.right]
                if operation.kind == "compose":
                    raise ValueError("Collatz programs require an atomic right action")
            shift = operation.shift
            first_input = current_block * 64 + shift
            final_input = first_input + 63
            exact_before_width = self._known_program_width(before)
            dependency_last = (
                final_input
                if exact_before_width is None
                else min(final_input, exact_before_width - 1)
            )
            dependency_first = first_input // 64
            dependencies = (
                ()
                if dependency_last < first_input
                else tuple(
                    range(
                        dependency_first,
                        dependency_last // 64 + 1,
                    )
                )
            )
            missing: list[int] = []
            for dependency in dependencies:
                dependency_key = before.local_id, dependency
                retained = self._microblocks.get(
                    self._microblock_key(before, dependency)
                )
                if retained is None:
                    missing.append(dependency)
                else:
                    built.add(dependency_key)
            if missing:
                pending.append((current, current_block, True))
                pending.extend(
                    (before, dependency, False) for dependency in reversed(missing)
                )
                continue

            def input_bit(position: int) -> int:
                if exact_before_width is not None and position >= exact_before_width:
                    return 0
                provider_block = position // 64
                retained = self._microblocks.get(
                    self._microblock_key(before, provider_block)
                )
                if retained is None:
                    raise AssertionError("Collatz provider block was not built")
                provider = retained.encoded
                return (provider >> (position % 64)) & 1

            if operation.kind == "shift":
                value = sum(
                    input_bit(first_input + offset) << offset for offset in range(64)
                )
            elif operation.kind == "mul3":
                if first_input == 0:
                    carry = Mul3Carry.ONE
                elif (
                    exact_before_width is not None
                    and first_input >= exact_before_width + 2
                ):
                    carry = Mul3Carry.ZERO
                else:
                    prefix = self._range_evaluator.range_effect(
                        before,
                        0,
                        first_input,
                    )
                    carry = Mul3Carry(prefix.transfer.rows[1].exit_carry)
                    self.ledger.bump("collatz_microblock_prefix_summaries")
                output = 0
                for position in range(first_input, final_input + 1):
                    total = self.ledger.observe_arithmetic(
                        3 * input_bit(position) + int(carry)
                    )
                    carry = Mul3Carry(total >> 1)
                    self.maximum_carry = max(self.maximum_carry, int(carry))
                    self.carry_cell_evaluations += 1
                    if position >= first_input:
                        output |= (total & 1) << (position - first_input)
                value = output
            else:
                raise AssertionError(operation.kind)
        self._microblocks.put(key, ExactMicroblock(value, 64))
        self.ledger.bump("collatz_program_microblock_evaluations")
        built.add(local)
    result = self._microblocks.get(root_key)
    if result is None:
        raise AssertionError("Collatz root microblock was evicted during evaluation")
    return result.encoded


def _program_bit(
    self: LazyCollatzApplication, program: ActionProgramID, position: int
) -> int:
    if type(position) is not int or position < 0:
        raise ValueError("Collatz program coordinates must be nonnegative")
    block = position // 64
    return (self._program_block(program, block) >> (position % 64)) & 1
