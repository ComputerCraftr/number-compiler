"""Direct application of one admitted composed dyadic action to its source."""

from __future__ import annotations

from collections.abc import Hashable
from operator import add, mul
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.consumer_pullback import (
    compose_prefix_safety_values,
)
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicCycleSummary,
    DyadicImageSummary,
    DyadicReturnActionID,
    DyadicReturnSourceID,
    DyadicReturnSupportID,
    _ImageNode,
    _SupportNode,
)
from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageCandidate,
    SourceImageView,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_images import (
        DyadicReturnImageWorkspace,
    )


def _identity_transfer() -> SkewTransfer[int]:
    return SkewTransfer(1, 0, 1)


def complete_composite_candidate(
    self: DyadicReturnImageWorkspace, action: Hashable, source: SourceImageView
) -> SourceImageCandidate:
    """Scope finite arithmetic reuse to this one authenticated application."""
    from number_compiler.hashlife.execution.dyadic_return_transport import (
        _clear_finite_memo,
    )

    self._validate_law()
    if self._closed or self.macros or self.macro_stack or self.balanced_stack:
        raise RuntimeError("nested or disposed dyadic finite construction")
    try:
        return _complete_composite_candidate(self, action, source)
    finally:
        _clear_finite_memo(self)


def _complete_composite_candidate(
    self: DyadicReturnImageWorkspace, action: Hashable, source: SourceImageView
) -> SourceImageCandidate:
    """Apply one composed action directly to one admitted source cylinder.

    The public image is exact, but construction has two deliberately
    separate phases:

    * a *bounded* exact prefix may look for the family's pinned terminal
      cycle; and
    * every remaining source cylinder is compiled by balanced recursive
      substitution instead of left-deep 64-step accumulation.

    The second phase is the temporal cutover.  It keeps the exact fresh
    source-tail information required by Collatz while preventing affine
    coefficient sizes from being re-composed against the whole elapsed
    prefix at every chunk.  No temporal midpoint source image is published.
    """
    self.validate_action(action)
    self.validate_payload(source.payload)
    if type(action) is not DyadicReturnActionID:
        raise TypeError("dyadic composite application requires an action ID")
    if type(source.binding.source) is not DyadicReturnSourceID:
        raise TypeError("dyadic composite application requires a source ID")
    if source.binding.action != self.identity:
        raise ValueError(
            "dyadic composite application source is not an identity context"
        )

    action_node = self.action_node(action)
    source_id = source.binding.source
    source_node = self.source_node(source_id)
    width = action_node.width
    if width <= 0 or action_node.children is None:
        raise ValueError("complete composite application needs a nonempty composite")
    if source_node.precision != width:
        raise ValueError(
            "complete composite application received another source precision"
        )

    from number_compiler.hashlife.execution.dyadic_return_transport import (
        _low_bits as transport_low_bits,
        balanced_residue_effect,
        balanced_residue_macro,
        cycle_phase_summaries,
        residue_macro,
    )

    retain_support = self.retain_chronological_support()

    # Exact cycle discovery is an optimization, not semantic ownership.
    # Bound both its temporal extent and live integer size.  If either cap
    # is reached the remaining exact cylinder is handed to the balanced
    # source-only constructor.  This keeps a no-cycle query from paying a
    # quadratic sequence of ever-wider affine compositions.
    MAX_CYCLE_DISCOVERY_STEPS = 4096
    MAX_CYCLE_TRACK_BITS = 1024
    tracked_value = self._source_value(source_node) if source_node.exact else None
    track_cycle = (
        tracked_value is not None
        and tracked_value.bit_length() <= MAX_CYCLE_TRACK_BITS
        and self.law.cycle is not None
        # Cycle discovery is an optimization for long time / small-source
        # queries.  When the source already carries roughly as many bits as
        # the requested temporal extent, serial exact tracking only turns a
        # cold cylinder into quadratic big-integer work.  The balanced
        # source-cylinder constructor is exact in that regime.
        and width > 2 * max(1, tracked_value.bit_length())
    )

    remaining = width
    transfer = _identity_transfer()
    odd_steps = 0
    delta = 0
    minimum = 0
    support: DyadicReturnSupportID | None = None
    published_cycle: DyadicCycleSummary | None = None
    discovered = 0

    while remaining and track_cycle and discovered < MAX_CYCLE_DISCOVERY_STEPS:
        assert tracked_value is not None
        cycle = self.law.cycle
        assert cycle is not None
        if (support is not None or discovered > 0) and tracked_value in cycle.states:
            entry_phase = cycle.states.index(tracked_value)
            cycle_length = len(cycle.states)
            cycles, remainder = divmod(remaining, cycle_length)
            cycle_safety, cycle_odd, remainder_safety, remainder_odd = (
                cycle_phase_summaries(self.law, entry_phase, remainder)
            )
            tail_safety = cycle_safety.repeat(cycles).then(remainder_safety)
            self._bump("cycle_safety_transformer_applications")
            tail_delta, tail_minimum = tail_safety.delta, tail_safety.minimum
            tail_odd = cycles * cycle_odd + remainder_odd
            terminal_phase = (entry_phase + remainder) % cycle_length
            terminal = cycle.states[terminal_phase]
            local_cycle = DyadicCycleSummary(
                0,
                entry_phase,
                cycles,
                remainder,
                terminal_phase,
                tail_odd,
                tail_delta,
                tail_minimum,
            )
            tail_transfer = SkewTransfer(0, terminal, 1)
            tail_support = None
            if retain_support:
                tail_support = self._append_support(
                    _SupportNode(
                        remaining,
                        transport_low_bits(tracked_value, remaining),
                        tail_transfer,
                        tail_odd,
                        tail_delta,
                        tail_minimum,
                        None,
                        None,
                        local_cycle,
                    )
                )
            transfer = transfer.then(tail_transfer, multiply=mul, add=add)
            odd_steps += tail_odd
            delta, minimum = compose_prefix_safety_values(
                delta, minimum, tail_delta, tail_minimum
            )
            published_cycle = DyadicCycleSummary(
                width - remaining,
                entry_phase,
                cycles,
                remainder,
                terminal_phase,
                tail_odd,
                tail_delta,
                tail_minimum,
            )
            if retain_support:
                assert support is not None and tail_support is not None
                support = self._append_support(
                    _SupportNode(
                        width,
                        source_node.residue,
                        transfer,
                        odd_steps,
                        delta,
                        minimum,
                        None,
                        (support, tail_support),
                        published_cycle,
                    )
                )
            self._bump("cycle_compressions")
            self._bump(
                "cycle_repeat_operand_bits",
                max(
                    1,
                    cycles.bit_length(),
                    remaining.bit_length(),
                    cycle_length.bit_length(),
                ),
            )
            remaining = 0
            break

        chunk_width = min(
            self.MAX_LEAF_STEPS,
            remaining,
            MAX_CYCLE_DISCOVERY_STEPS - discovered,
        )
        chunk_residue = transport_low_bits(tracked_value, chunk_width)
        if retain_support:
            chunk_support = residue_macro(
                self, chunk_width, chunk_residue, _keep_memo=True
            )
            chunk = self.support_node(chunk_support)
        else:
            chunk_support = None
            chunk = balanced_residue_effect(
                self, chunk_width, chunk_residue, _keep_memo=True
            )

        before_transfer = transfer
        transfer = before_transfer.then(chunk.transfer, multiply=mul, add=add)
        self._bump(
            "composition_operand_bits",
            max(
                1,
                before_transfer.upper.bit_length(),
                before_transfer.offset.bit_length(),
                before_transfer.lower.bit_length(),
                chunk.transfer.upper.bit_length(),
                chunk.transfer.offset.bit_length(),
                chunk.transfer.lower.bit_length(),
            ),
        )
        odd_steps += chunk.odd_steps
        delta, minimum = compose_prefix_safety_values(
            delta, minimum, chunk.delta, chunk.minimum
        )
        total_width = width - remaining + chunk_width
        if retain_support:
            assert chunk_support is not None
            support = (
                chunk_support
                if support is None
                else self._append_support(
                    _SupportNode(
                        total_width,
                        transport_low_bits(source_node.residue, total_width),
                        transfer,
                        odd_steps,
                        delta,
                        minimum,
                        None,
                        (support, chunk_support),
                    )
                )
            )

        numerator = chunk.transfer.upper * tracked_value + chunk.transfer.offset
        if numerator % chunk.transfer.lower:
            raise ArithmeticError(
                "dyadic composite exact chunk transport was not integral"
            )
        tracked_value = numerator // chunk.transfer.lower
        self._bump(
            "transport_exact_operand_bits",
            max(
                1,
                tracked_value.bit_length(),
                chunk.transfer.upper.bit_length(),
                chunk.transfer.offset.bit_length(),
                chunk.transfer.lower.bit_length(),
                numerator.bit_length(),
            ),
        )
        self._bump("composite_cutover_chunks")
        self._bump("leaf_steps", chunk_width)
        discovered += chunk_width
        remaining -= chunk_width
        if tracked_value.bit_length() > MAX_CYCLE_TRACK_BITS:
            track_cycle = False

    if remaining:
        # If a bounded exact prefix was consumed, ``tracked_value`` is the
        # exact current occurrence at this seam.  Otherwise the original
        # source cylinder is still the tail source.
        if discovered:
            assert tracked_value is not None
            tail_residue = transport_low_bits(tracked_value, remaining)
        else:
            tail_residue = transport_low_bits(source_node.residue, remaining)
        if retain_support:
            tail_support = balanced_residue_macro(
                self, remaining, tail_residue, _keep_memo=True
            )
            tail = self.support_node(tail_support)
        else:
            tail_support = None
            tail = balanced_residue_effect(
                self, remaining, tail_residue, _keep_memo=True
            )
        before_transfer = transfer
        transfer = before_transfer.then(tail.transfer, multiply=mul, add=add)
        odd_steps += tail.odd_steps
        delta, minimum = compose_prefix_safety_values(
            delta, minimum, tail.delta, tail.minimum
        )
        if retain_support:
            assert tail_support is not None
            if support is None:
                support = tail_support
            else:
                support = self._append_support(
                    _SupportNode(
                        width,
                        source_node.residue,
                        transfer,
                        odd_steps,
                        delta,
                        minimum,
                        None,
                        (support, tail_support),
                    )
                )
        self._bump("balanced_composite_tails")
        self._bump(
            "composition_operand_bits",
            max(
                1,
                before_transfer.upper.bit_length(),
                before_transfer.offset.bit_length(),
                before_transfer.lower.bit_length(),
                tail.transfer.upper.bit_length(),
                tail.transfer.offset.bit_length(),
                tail.transfer.lower.bit_length(),
            ),
        )
        remaining = 0

    if not retain_support:
        support = self._append_support(
            _SupportNode(
                width,
                source_node.residue,
                transfer,
                odd_steps,
                delta,
                minimum,
                None,
                None,
                published_cycle,
                True,
            )
        )
        self._bump("saturated_support_publications")
    if support is None:
        raise AssertionError("nonempty composite published no support")
    summary = DyadicImageSummary(
        width,
        source_node.residue,
        transfer,
        delta,
        minimum,
        odd_steps,
        support,
        published_cycle,
    )
    payload = self._append_image(_ImageNode(source_id, action, summary))
    self._bump("composite_cutover_publications")
    return SourceImageCandidate(
        payload,
        width,
        (
            self.law.descriptor,
            transfer.upper,
            transfer.offset,
            transfer.lower,
            odd_steps,
        ),
        precision=source_node.precision,
    )
