"""Publish exact run contractions through the shared source-image owner.

Run selection is family arithmetic. Publication, immutable source/action binding,
resource limits, and optional chronological support remain scheduler contracts.
"""

from __future__ import annotations

from collections.abc import Generator
from contextlib import contextmanager
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicCycleSummary,
    DyadicImageSummary,
    DyadicReturnActionID,
    DyadicReturnImageRecord,
    DyadicReturnSourceID,
    DyadicReturnSupportRecord,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageCandidate,
    SourceImageView,
)
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_images import (
        DyadicReturnImageWorkspace,
    )


class RunArithmeticWorkspace:
    """Reserve transient integer limbs before run arithmetic, never an itinerary.

    The bound includes simultaneous input, power, product and result integers.
    These are construction temporaries, not retained semantic action fields.
    """

    def __init__(self, ledger: ResourceLedger, prefix: str) -> None:
        self.ledger, self.prefix, self.nodes = ledger, prefix, 0
        self.active = False
        self.owner = ledger.register(
            f"{prefix}-run-scratch", "run_arithmetic_workspace"
        )
        ledger.register_container(
            self.owner, self, node_count=lambda: self.nodes, payloads=lambda: ()
        )

    @classmethod
    def for_ledger(cls, ledger: ResourceLedger, prefix: str) -> RunArithmeticWorkspace:
        owner = ledger.register(f"{prefix}-run-scratch", "run_arithmetic_workspace")
        retained = ledger.registered_container(owner)
        if retained is None:
            return cls(ledger, prefix)
        if (
            type(retained) is not cls
            or retained.ledger is not ledger
            or retained.prefix != prefix
            or retained.owner != owner
        ):
            raise ValueError("run workspace has another owner")
        return retained

    def __len__(self) -> int:
        return 0

    @contextmanager
    def scope(self) -> Generator[RunArithmeticWorkspace, None, None]:
        if self.active:
            raise RuntimeError("run arithmetic workspace is already active")
        self.active = True
        try:
            yield self
        finally:
            self.ledger.release(self.owner, nodes=self.nodes)
            self.nodes = 0
            self.active = False

    def require_bits(self, bits: int) -> None:
        if not self.active:
            raise RuntimeError("run arithmetic requires an active workspace")
        if type(bits) is not int or bits < 0:
            raise ValueError("run arithmetic needs a nonnegative bit bound")
        nodes = 16 + (bits + 63) // 64
        if nodes > self.nodes:
            self.ledger.reserve(self.owner, nodes=nodes - self.nodes)
            self.nodes = nodes
        name = f"{self.prefix}_temporal_scratch_peak_bits"
        previous = self.ledger.counters.get(name, 0)
        if bits > previous:
            self.ledger.bump(name, bits - previous)


def publish_exact_run_candidate(
    workspace: DyadicReturnImageWorkspace,
    action: DyadicReturnActionID,
    source: SourceImageView,
    transfer: SkewTransfer[int],
    odd_steps: int,
    delta: int,
    minimum: int,
    cycle: DyadicCycleSummary | None = None,
) -> SourceImageCandidate:
    """Contract a pinned exact source; do not generalize to its residue class."""
    workspace.validate_action(action)
    workspace.validate_payload(source.payload)
    source_id = source.binding.source
    if type(source_id) is not DyadicReturnSourceID:
        raise TypeError("run contraction requires a source ID")
    admitted = workspace.source_node(source_id)
    width = workspace.action_node(action).width
    if (
        not admitted.exact
        or source.binding.action != workspace.identity
        or admitted.precision != width
        or width <= 0
    ):
        raise ValueError("run contraction requires an exact identity source")
    with workspace.composite_transaction():
        support = workspace._append_support(
            DyadicReturnSupportRecord(
                width,
                admitted.residue,
                transfer,
                odd_steps,
                delta,
                minimum,
                None,
                None,
                cycle,
                True,
            )
        )
        summary = DyadicImageSummary(
            width,
            admitted.residue,
            transfer,
            delta,
            minimum,
            odd_steps,
            support,
            cycle,
        )
        payload = workspace._append_image(
            DyadicReturnImageRecord(source_id, action, summary)
        )
        workspace.bump_metric("saturated_support_publications")
        workspace.bump_metric("run_contraction_publications")
        return SourceImageCandidate(
            payload,
            width,
            (
                workspace.law.descriptor,
                transfer.upper,
                transfer.offset,
                transfer.lower,
                odd_steps,
            ),
            precision=admitted.precision,
        )
