"""Bounded closed-form observation assembled from an admitted source owner."""

from __future__ import annotations

from collections.abc import Callable
from typing import Protocol

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import double_reverse as _double_reverse_keys
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    DoubleReverseTemporalHashlife,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
    DoubleReverseSourcePrefix,
    UncertifiedPointedStencilError,
)
from number_compiler.sequences.double_reverse.temporal_ports import (
    DoubleReverseClosedForm,
    closed_form_from_roots,
)


class _PrefixEntryProvider(Protocol):
    def __call__(
        self, *, max_prefix: int, require_even_remainder: bool
    ) -> DoubleReverseSourcePrefix: ...


def publish_temporal_closed_form(
    source_root: int,
    generation: int,
    endpoint_root: Callable[[], int],
    prefix_entry: _PrefixEntryProvider,
    temporal_hashlife: DoubleReverseTemporalHashlife,
    arena: LedgerSLPArena,
    ledger: ResourceLedger,
    scratch_owner: int,
    *,
    modulus: int | None,
    max_bits: int,
) -> DoubleReverseClosedForm:
    """Publish exact moments and source-relative certified suffix data."""

    entry_root: int | None = None
    prefix_steps: int | None = None
    source_phase = temporal_hashlife.certify(source_root)
    if generation >= 2 and (source_phase is None or generation % 2 != 0):
        try:
            entry = prefix_entry(
                max_prefix=min(32, generation - 2),
                require_even_remainder=True,
            )
        except UncertifiedPointedStencilError:
            pass
        else:
            entry_root = temporal_hashlife.root_of(entry.target)
            prefix_steps = entry.physical_steps
    endpoint = endpoint_root()
    result = closed_form_from_roots(
        arena,
        source_root,
        endpoint,
        generation,
        modulus=modulus,
        max_bits=max_bits,
        ledger=ledger,
        scratch_owner=scratch_owner,
        entry_root=entry_root,
        prefix_steps=prefix_steps,
    )
    if result.suffix_affine_gain is not None:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_CERTIFIED_SUFFIX_PUBLICATIONS
        )
    ledger.bump(_double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_MOMENT_PORT_PUBLICATIONS)
    if result.affine_gain is not None or result.suffix_affine_gain is not None:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_AFFINE_PORT_PUBLICATIONS
        )
    return result
