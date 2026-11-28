"""Publish a source-bound binary or ternary endpoint to the existing scheduler."""

from __future__ import annotations

from collections.abc import Sequence
from contextlib import nullcontext
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageCandidate,
)

from .small_radix import SmallRadixImage
from .small_radix import advance as small_radix_advance
from .source_actions import ReverseActionID

if TYPE_CHECKING:
    from .source_images import ReverseImagePayload, ReverseSourceImageAdapter


def radix_candidate(
    self: ReverseSourceImageAdapter,
    action: ReverseActionID,
    origin: ExactSource,
    payload: ReverseImagePayload,
) -> SourceImageCandidate:
    from .source_images import ReverseImagePayload

    prior = self.actions.node(payload.action).steps
    additional = self.actions.node(action).steps
    total = prior + additional
    output_store = self.radix_output_store(origin)
    target = output_store.get(total)
    if target is None:

        def receive(output: SmallRadixImage) -> SmallRadixImage:
            output_store[total] = output
            return output

        staging = (
            self.ledger.reservation(
                output_store.owner, nodes=1 + (len(origin.digits) + prior + 7) // 8
            )
            if prior and payload.radix_output is None
            else nullcontext()
        )
        with staging:
            physical: SmallRadixImage | Sequence[int]
            if payload.radix_output is not None:
                physical = payload.radix_output
            elif prior == 0:
                physical = origin.digits
            else:
                # A legacy completed image can hand over its exact endpoint;
                # the new executor never starts again from the original seed.
                if prior == 1:
                    digits = self.iter_primitive_digits(origin)
                elif prior == 2:
                    digits = self.iter_second_digits(origin)
                else:
                    completed = self.recursive_for_steps(prior)
                    digits = (
                        completed[0].iter_digits(completed[1])
                        if completed
                        else self.iter_same_carry_digits(origin, prior)
                    )
                physical = bytes(digits)
            target = small_radix_advance(
                physical,
                origin.base,
                additional,
                self.ledger,
                output_store.owner,
                receive,
            )
    cumulative = self.actions.compose(payload.action, action)
    return SourceImageCandidate(
        ReverseImagePayload(cumulative, radix_output=target),
        total,
        radix=origin.base,
        precision=None,
    )
