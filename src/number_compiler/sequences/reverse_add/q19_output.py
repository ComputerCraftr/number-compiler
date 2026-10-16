"""Ledger-owned decimal pair output grammar and Q19 summaries.

This owner contains spatial pair-step work only.  Temporal powers are still
driven by ``TileScheduler`` through source-image primitive and composition
callbacks; a published occurrence is the completed SLP root plus its exact
Q19/width metadata.
"""

from __future__ import annotations

from collections.abc import Callable, Generator, Iterator
from contextlib import ExitStack, closing
from typing import TYPE_CHECKING

from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.resources.metric_keys import shared as _shared_keys

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.q19_border_control import (
        CertifiedBorderGrowth,
    )
    from number_compiler.sequences.reverse_add.q19_controlled_gt_bank import (
        SourceGuardedGTBankAction,
    )
    from number_compiler.sequences.reverse_add.q19_periodic_cone import (
        CertifiedUniformizingCone,
    )
    from number_compiler.sequences.reverse_add.q19_spatial_bank_morphism import (
        ReverseAddSpatialBankMorphism,
    )
    from number_compiler.sequences.reverse_add.q19_uniform_cone import (
        CertifiedUniformCone,
    )
    from number_compiler.sequences.reverse_add.radix19_cochain import (
        Radix19CarryBlock,
    )

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import (
    BimachineSLPProjector,
)
from number_compiler.arithmetic.automata.slp_walks import iter_symbols, symbol_at
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.resources.construction_scope import RuntimeConstruction
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all, cleanup_on_error
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.reverse_add._q19_issuance import (
    Q19IssuanceRegistry,
)
from number_compiler.sequences.reverse_add.q19_occurrence import (
    ReversePairOutputOccurrence,
    _occurrence_publication_binding,
)
from number_compiler.sequences.reverse_add.q19_punctured_producer import (
    PuncturedPairProducer,
)
from number_compiler.sequences.reverse_add.q19_word_summary import (
    _Q19,
    _UPPER,
    _pair_step_law,
    _WordSummary,
)

_LedgerSLPArena = LedgerSLPArena


class ReversePairQ19OutputOwner:
    """One exact decimal pair transducer owned by a source-image adapter."""

    def __init__(
        self,
        ledger: ResourceLedger,
        digits_lsd: tuple[int, ...],
        *,
        base: int,
    ) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("Q19 output owner requires a resource ledger")
        if type(digits_lsd) is not tuple or not digits_lsd:
            raise ValueError("Q19 output owner requires original source digits")
        if type(base) is not int or base != 10:
            raise ValueError("the Q19 pair transducer is decimal-only")
        if any(type(value) is not int or not 0 <= value < base for value in digits_lsd):
            raise ValueError("Q19 source contains a digit outside its radix")
        self.ledger = ledger
        self.base = base
        self._digits = digits_lsd
        self._authority = ArenaToken("reverse-pair-q19-output")
        prefix = f"reverse-pair-q19-{ledger.owner_count}"

        # A construction scope records each ledger owner and weak root as it is
        # registered, so failure in any intermediate account/store constructor
        # retires exactly the resources created by this unpublished owner.
        with RuntimeConstruction(ledger):
            self.arena = LedgerSLPArena(
                ledger, prefix, owner_kind="reverse_pair_output"
            )
            self.machine = _pair_step_law()
            self.projector = BimachineSLPProjector(self.machine, self.arena)

            forward_owner = ledger.register(
                prefix + "-projector-forward", "reverse_pair_projector_memo"
            )
            forward: OwnedMemo[tuple[int, int], int | None] = OwnedMemo(
                ledger, forward_owner, nodes_per_entry=1
            )
            reverse_owner = ledger.register(
                prefix + "-projector-reverse", "reverse_pair_projector_memo"
            )
            backward: OwnedMemo[tuple[int, int], int | None] = OwnedMemo(
                ledger, reverse_owner, nodes_per_entry=1
            )
            block_owner = ledger.register(
                prefix + "-projector-block", "reverse_pair_projector_memo"
            )
            block: OwnedMemo[tuple[int, int, int], int] = OwnedMemo(
                ledger, block_owner, nodes_per_entry=1
            )
            forward_power_owner = ledger.register(
                prefix + "-projector-forward-power",
                "reverse_pair_projector_memo",
            )
            forward_power: OwnedMemo[tuple[int, int, int], int | None] = OwnedMemo(
                ledger, forward_power_owner, nodes_per_entry=1
            )
            backward_power_owner = ledger.register(
                prefix + "-projector-reverse-power",
                "reverse_pair_projector_memo",
            )
            backward_power: OwnedMemo[tuple[int, int, int], int | None] = OwnedMemo(
                ledger, backward_power_owner, nodes_per_entry=1
            )
            self._projector_owners = (
                forward_owner,
                reverse_owner,
                block_owner,
                forward_power_owner,
                backward_power_owner,
            )
            self._projector_memos = (
                forward,
                backward,
                block,
                forward_power,
                backward_power,
            )
            (
                self.projector._fwd,
                self.projector._rev,
                self.projector._block,
                self.projector._fwd_power,
                self.projector._rev_power,
            ) = self._projector_memos
            self._summary_owner = ledger.register(
                prefix + "-q19-summaries", "reverse_pair_q19_summary"
            )
            self._summaries = OwnedMemo[int, _WordSummary](
                ledger, self._summary_owner, nodes_per_entry=1
            )
            self._issued_owner = ledger.register(
                prefix + "-issued-occurrences", "reverse_pair_output_occurrence"
            )
            self._issued = OwnedMemo[tuple[int, int], ReversePairOutputOccurrence](
                ledger, self._issued_owner, nodes_per_entry=1
            )
            self._issuance_registry = Q19IssuanceRegistry(self, ledger, prefix)
            self._border_certificates_owner = (
                self._issuance_registry.border_certificates.owner
            )
            self._border_certificates = self._issuance_registry.border_certificates
            self._controlled_gt_banks_owner = (
                self._issuance_registry.controlled_gt_banks.owner
            )
            self._controlled_gt_banks = self._issuance_registry.controlled_gt_banks
            self._spatial_bank_windows_owner = (
                self._issuance_registry.spatial_bank_windows.owner
            )
            self._spatial_bank_windows = self._issuance_registry.spatial_bank_windows
            self._scratch_owner = ledger.register(
                prefix + "-workspace", "reverse_pair_output_workspace"
            )
            self._active_symbol_walks = 0
            self._disposed = False
            self._cleanup_complete = False
            self._dispose_resources_complete = False
            self._binding = (
                ledger,
                digits_lsd,
                base,
                self._authority,
                self.arena,
                self.projector,
                self.machine,
                self._border_certificates,
                self._controlled_gt_banks,
                self._issuance_registry,
                self._spatial_bank_windows,
            )
        with ExitStack() as rollback:
            rollback.enter_context(cleanup_on_error(self.dispose))
            ledger.register_execution_root(self)
            self.initial = self._make_initial()
            self._register_payload_audit_contract()

    def _register_payload_audit_contract(self) -> None:
        self._audit_nodes = self.arena.nodes
        self._audit_terms = self.arena._term._data
        self._audit_concats = self.arena._cat._data
        self._audit_repeats = self.arena._rep._data
        self._audit_summaries = self._summaries._data
        self._audit_issued = self._issued._data
        self._audit_border_certificates = self._border_certificates._data
        self._audit_controlled_gt_banks = self._controlled_gt_banks._data
        self._audit_spatial_bank_windows = self._spatial_bank_windows._data
        (
            self._audit_projector_forward,
            self._audit_projector_reverse,
            self._audit_projector_block,
            self._audit_projector_forward_power,
            self._audit_projector_reverse_power,
        ) = tuple(memo._data for memo in self._projector_memos)
        from number_compiler.resources.payload_contracts import (
            PayloadAuditStoreBinding,
        )
        from number_compiler.sequences.reverse_add.q19_payload_audit import (
            audit_reverse_pair_output_owner,
        )

        self.ledger.register_payload_audit_contract(
            self,
            "reverse_add",
            (
                PayloadAuditStoreBinding(
                    self.arena.owners[0],
                    "_audit_nodes",
                    "reverse_pair_output_grammar",
                ),
                PayloadAuditStoreBinding(
                    self.arena.owners[1],
                    "_audit_terms",
                    "reverse_pair_output_interner",
                ),
                PayloadAuditStoreBinding(
                    self.arena.owners[2],
                    "_audit_concats",
                    "reverse_pair_output_interner",
                ),
                PayloadAuditStoreBinding(
                    self.arena.owners[3],
                    "_audit_repeats",
                    "reverse_pair_output_interner",
                ),
                PayloadAuditStoreBinding(
                    self._summary_owner,
                    "_audit_summaries",
                    "reverse_pair_q19_summary",
                ),
                PayloadAuditStoreBinding(
                    self._issued_owner,
                    "_audit_issued",
                    "reverse_pair_output_occurrence",
                ),
                PayloadAuditStoreBinding(
                    self._border_certificates_owner,
                    "_audit_border_certificates",
                    "reverse_pair_q19_border_certificate",
                ),
                PayloadAuditStoreBinding(
                    self._controlled_gt_banks_owner,
                    "_audit_controlled_gt_banks",
                    "reverse_pair_q19_conditional_gt_bank",
                ),
                PayloadAuditStoreBinding(
                    self._spatial_bank_windows_owner,
                    "_audit_spatial_bank_windows",
                    "reverse_pair_q19_spatial_bank_window",
                ),
                *(
                    PayloadAuditStoreBinding(
                        owner,
                        attribute,
                        "reverse_pair_projector_memo",
                    )
                    for owner, attribute in zip(
                        self._projector_owners,
                        (
                            "_audit_projector_forward",
                            "_audit_projector_reverse",
                            "_audit_projector_block",
                            "_audit_projector_forward_power",
                            "_audit_projector_reverse_power",
                        ),
                        strict=True,
                    )
                ),
            ),
            audit_reverse_pair_output_owner,
        )

    def _check_open(self) -> None:
        if self._disposed:
            raise ValueError("disposed Q19 pair output owner")
        if self.base != 10 or type(self._digits) is not tuple or not self._digits:
            raise ValueError("Q19 pair output source binding changed")
        current = (
            self.ledger,
            self._digits,
            self.base,
            self._authority,
            self.arena,
            self.projector,
            self.machine,
            self._border_certificates,
            self._controlled_gt_banks,
            self._issuance_registry,
            self._spatial_bank_windows,
        )
        if len(self._binding) != len(current) or any(
            original is not bound
            for original, bound in zip(self._binding, current, strict=True)
        ):
            raise ValueError("Q19 output owner or finite law binding changed")
        if self._issuance_registry.controlled_gt_bank_next != len(
            self._controlled_gt_banks
        ):
            raise ValueError("Q19 controlled bank registry changed")
        if self._issuance_registry.spatial_bank_window_next != len(
            self._spatial_bank_windows
        ):
            raise ValueError("Q19 spatial bank window registry changed")

    def _append_word_symbol(self, blocks: list[tuple[int, int]], symbol: int) -> None:
        node = self.arena.terminal(symbol)
        level = 0
        while blocks and blocks[-1][0] == level:
            left = blocks.pop()[1]
            node = self.arena.concat(left, node)
            level += 1
        blocks.append((level, node))

    def _word(self, symbols: Iterator[int]) -> int:
        blocks: list[tuple[int, int]] = []
        for symbol in symbols:
            self._append_word_symbol(blocks, symbol)
        root = self.arena.empty()
        for _level, block in blocks:
            root = self.arena.concat(root, block)
        return root

    def _make_initial(self) -> ReversePairOutputOccurrence:
        width = len(self._digits)
        parity = width & 1
        half_width = (width + 1) // 2

        def encoded() -> Iterator[int]:
            yield 2 * self.base - 1 + parity
            for index in range(half_width):
                yield self._digits[index] + self._digits[width - 1 - index]
            yield 2 * self.base + 1

        with self.ledger.reservation(
            self._scratch_owner, nodes=8 * (width.bit_length() + 1)
        ):
            root = self._word(encoded())
        summary = self._full_summary(root)
        if summary.length != width:
            raise AssertionError("initial Q19 grammar changed pair-field width")
        return self._issue(root, 1)

    def _symbol_at(self, root: int, index: int) -> int:
        return symbol_at(self.arena, root, index)

    def _word_summary(self, root: int) -> _WordSummary:
        found = self._summaries.get(root)
        if found is not None:
            return found
        with self.ledger.reservation(
            self._scratch_owner, nodes=8 * (len(self.arena.nodes) + 1)
        ):
            return self._build_word_summary(root)

    def _build_word_summary(self, root: int) -> _WordSummary:
        found = self._summaries.get(root)
        if found is not None:
            self.ledger.bump(_reverse_add_keys.REVERSE_PAIR_Q19_SUMMARY_CACHE_HITS)
            return found
        self.ledger.bump(_reverse_add_keys.REVERSE_PAIR_Q19_SUMMARY_CACHE_MISSES)
        stack: list[tuple[int, bool]] = [(root, False)]
        identity = _Q19.identity()
        while stack:
            node_id, expanded = stack.pop()
            if self._summaries.get(node_id) is not None:
                continue
            node = self.arena.nodes[node_id]
            if node.kind == "EMPTY":
                value = _WordSummary(
                    0, identity, identity, identity, identity, None, None, 0
                )
            elif node.kind == "TERM":
                if 0 <= node.symbol <= 18:
                    atom = _Q19.atom(node.symbol)
                    value = _WordSummary(
                        1, atom, atom, identity, identity, node.symbol, node.symbol, 1
                    )
                else:
                    value = _WordSummary(
                        0, identity, identity, identity, identity, None, None, 0
                    )
            elif node.kind == "CONCAT":
                if not expanded:
                    stack.append((node_id, True))
                    stack.append((node.right, False))
                    stack.append((node.left, False))
                    continue
                left = self._summaries[node.left]
                right = self._summaries[node.right]
                if right.symbols:
                    prefix_forward = left.forward.then(right.prefix_forward)
                    prefix_reverse = right.prefix_reverse.then(left.reverse)
                else:
                    prefix_forward, prefix_reverse = (
                        left.prefix_forward,
                        left.prefix_reverse,
                    )
                value = _WordSummary(
                    left.symbols + right.symbols,
                    left.forward.then(right.forward),
                    right.reverse.then(left.reverse),
                    prefix_forward,
                    prefix_reverse,
                    left.first_symbol if left.symbols else right.first_symbol,
                    right.last_symbol if right.symbols else left.last_symbol,
                    left.runs
                    + right.runs
                    - int(
                        left.last_symbol is not None
                        and left.last_symbol == right.first_symbol
                    ),
                )
            elif node.kind == "REPEAT":
                if not expanded:
                    stack.append((node_id, True))
                    stack.append((node.child, False))
                    continue
                child = self._summaries[node.child]
                if not child.symbols:
                    value = _WordSummary(
                        0, identity, identity, identity, identity, None, None, 0
                    )
                else:
                    whole_forward = child.forward.repeat(node.count)
                    whole_reverse = child.reverse.repeat(node.count)
                    if node.count == 1:
                        prefix_forward = child.prefix_forward
                        prefix_reverse = child.prefix_reverse
                    else:
                        prefix_forward = child.forward.repeat(node.count - 1).then(
                            child.prefix_forward
                        )
                        prefix_reverse = child.prefix_reverse.then(
                            child.reverse.repeat(node.count - 1)
                        )
                    value = _WordSummary(
                        child.symbols * node.count,
                        whole_forward,
                        whole_reverse,
                        prefix_forward,
                        prefix_reverse,
                        child.first_symbol,
                        child.last_symbol,
                        child.runs * node.count
                        - (
                            node.count - 1
                            if child.first_symbol == child.last_symbol
                            else 0
                        ),
                    )
            else:  # pragma: no cover - guarded by SLPArena
                raise AssertionError(node.kind)
            self._summaries[node_id] = value
        result = self._summaries.get(root)
        if result is None:
            raise AssertionError("Q19 summary construction lost its root")
        return result

    def _full_summary(self, root: int) -> _Q19:
        encoded_summary = self._word_summary(root)
        first = self._symbol_at(root, 0)
        parity = first - (2 * self.base - 1)
        if parity not in (0, 1):
            raise ValueError("pair output grammar has an invalid parity tag")
        half = encoded_summary.forward
        mirror = encoded_summary.prefix_reverse if parity else encoded_summary.reverse
        result = half.then(mirror)
        expected = 2 * encoded_summary.symbols - parity
        if result.length != expected:
            raise AssertionError("Q19 full-field fold lost its symmetric extent")
        result.validate_symmetric()
        return result

    def _candidate(self, root: int, temporal_steps: int) -> ReversePairOutputOccurrence:
        self._check_open()
        summary = self._full_summary(root)
        pair_width = summary.length
        output_width = pair_width + int(summary.domain == _UPPER)
        growth = output_width - len(self._digits)
        if growth < 0 or growth > temporal_steps:
            raise AssertionError("Q19 width growth escaped the one-cell-per-step bound")
        return ReversePairOutputOccurrence(
            self._authority,
            root,
            temporal_steps,
            pair_width,
            output_width,
            growth,
            summary.domain,
            summary.f9,
        )

    def _publish(
        self, occurrence: ReversePairOutputOccurrence
    ) -> ReversePairOutputOccurrence:
        self._check_open()
        occurrence.__post_init__()
        key = occurrence.root, occurrence.temporal_steps
        binding = _occurrence_publication_binding(occurrence)
        published_binding = occurrence._publication_binding
        if published_binding is not None and published_binding != binding:
            raise ValueError("published Q19 occurrence metadata was altered")
        existing = self._issued.get(key)
        if existing is not None:
            # SLP interning can make repeated application of the same source
            # land on the same (root, temporal_steps) key. Keep the first
            # owner-issued handle so certificates and downstream records that
            # retain it remain valid, but validate that record and compare all
            # exact occurrence metadata before reusing it.
            self.validate(existing)
            if _occurrence_publication_binding(existing) != binding:
                raise ValueError("Q19 occurrence key collides with different metadata")
            return existing
        if published_binding is None:
            object.__setattr__(occurrence, "_publication_binding", binding)
        self._issued[key] = occurrence
        return occurrence

    def _issue(self, root: int, temporal_steps: int) -> ReversePairOutputOccurrence:
        return self._publish(self._candidate(root, temporal_steps))

    def _validate_occurrence_handle(
        self, occurrence: ReversePairOutputOccurrence
    ) -> None:
        self._check_open()
        if type(occurrence) is not ReversePairOutputOccurrence:
            raise TypeError("expected an exact Q19 output occurrence")
        occurrence.__post_init__()
        if occurrence.owner is not self._authority:
            raise ValueError("Q19 output occurrence belongs to another request")
        if not 0 <= occurrence.root < len(self.arena.nodes):
            raise ValueError("Q19 output root is outside its grammar")
        if (
            self._issued.get((occurrence.root, occurrence.temporal_steps))
            is not occurrence
        ):
            raise ValueError("Q19 output occurrence was not issued by this owner")
        if occurrence._publication_binding != _occurrence_publication_binding(
            occurrence
        ):
            raise ValueError("published Q19 occurrence metadata was altered")

    def validate(self, occurrence: ReversePairOutputOccurrence) -> None:
        self._validate_occurrence_handle(occurrence)
        summary = self._full_summary(occurrence.root)
        if (
            summary.length != occurrence.pair_width
            or summary.domain != occurrence.q19_domain
            or summary.f9 != occurrence.q19_f9
            or occurrence.output_width != summary.length + int(summary.domain == _UPPER)
            or occurrence.growth != occurrence.output_width - len(self._digits)
        ):
            raise ValueError("Q19 output metadata disagrees with its grammar")

    def validate_issued_occurrence(
        self, occurrence: ReversePairOutputOccurrence
    ) -> None:
        """Check a previously issued immutable handle without re-folding its SLP."""
        self._validate_occurrence_handle(occurrence)

    def apply_pair_step(
        self, occurrence: ReversePairOutputOccurrence
    ) -> ReversePairOutputOccurrence:
        self.validate(occurrence)
        before = self.projector.section_calls
        with self.ledger.reservation(
            self._scratch_owner,
            nodes=64 * (len(self.arena.nodes) + 1),
        ):
            target = self.projector.apply(occurrence.root)
        candidate = self._candidate(target, occurrence.temporal_steps + 1)
        step_growth = candidate.output_width - occurrence.output_width
        if step_growth not in (0, 1):
            raise AssertionError("one reverse/add step changed width by more than one")
        result = self._publish(candidate)
        self.ledger.bump(_reverse_add_keys.REVERSE_Q19_PRIMITIVE_PAIR_APPLICATIONS)
        self.ledger.bump(
            _reverse_add_keys.REVERSE_Q19_PAIR_OUTPUT_NODES_VISITED,
            self.projector.section_calls - before,
        )
        return result

    def _pair_value_at(
        self, occurrence: ReversePairOutputOccurrence, index: int
    ) -> int:
        from .q19_source_authority import pair_value_at

        return pair_value_at(self, occurrence, index)

    def apply_punctured_pair_block(
        self, occurrence: ReversePairOutputOccurrence, *, steps: int
    ) -> ReversePairOutputOccurrence:
        """Apply one source-independent T2/T4 pullback to an issued Q19 field.

        The output is a completed occurrence in this same ledger-owned SLP
        owner. This is a bounded temporal law, not an arbitrary-depth Moore
        quotient.
        """
        return PuncturedPairProducer(self).apply(occurrence, steps=steps)

    def radix19_cochain(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        z: int = 2,
        modulus: int = 5,
    ) -> Radix19CarryBlock:
        """Project an issued Q19 source through decimal normalization."""
        from .q19_source_authority import radix19_cochain

        return radix19_cochain(self, occurrence, z=z, modulus=modulus)

    def radix19_walsh64_mod5(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        channel: str,
        start: int = 0,
    ) -> tuple[int, ...]:
        """Read 64 source-bound pair ports and transform them over F5."""
        from .q19_source_authority import radix19_walsh64_mod5

        return radix19_walsh64_mod5(self, occurrence, channel=channel, start=start)

    def authorize_radix19_gt_bank(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        steps: int,
        coordinate: int,
        period_sizes: tuple[int, ...] = (1, 2, 3, 4, 5, 6, 7, 8),
        window_digits: int = 6,
        max_states: int = 8192,
    ) -> SourceGuardedGTBankAction:
        """Join exact border growth with a source-guarded conditional bank."""
        from .q19_source_authority import authorize_radix19_gt_bank

        return authorize_radix19_gt_bank(
            self,
            occurrence,
            steps=steps,
            coordinate=coordinate,
            period_sizes=period_sizes,
            window_digits=window_digits,
            max_states=max_states,
        )

    def authorize_temporal_cell(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        steps: int,
        coordinate: int,
    ) -> CertifiedUniformCone:
        """Authorize one protected interior coefficient from its source."""
        from .q19_source_authority import authorize_temporal_cell

        return authorize_temporal_cell(
            self, occurrence, steps=steps, coordinate=coordinate
        )

    def authorize_mixed_temporal_cell(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        steps: int,
        coordinate: int,
        period_size: int = 2,
    ) -> CertifiedUniformizingCone:
        """Authorize a mixed periodic source core that closes to uniform."""
        from .q19_source_authority import authorize_mixed_temporal_cell

        return authorize_mixed_temporal_cell(
            self,
            occurrence,
            steps=steps,
            coordinate=coordinate,
            period_size=period_size,
        )

    def certify_border_growth(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        steps: int,
        window_digits: int = 2,
        max_states: int = 8192,
    ) -> CertifiedBorderGrowth:
        """Certify a finite growth tape from the exact source root."""
        from .q19_source_authority import certify_border_growth

        return certify_border_growth(
            self,
            occurrence,
            steps=steps,
            window_digits=window_digits,
            max_states=max_states,
        )

    def authorize_controlled_gt_bank(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        steps: int,
        coordinate: int,
        growth_control: tuple[int, ...] | CertifiedBorderGrowth,
        period_size: int = 2,
        max_states: int = 10000,
    ) -> SourceGuardedGTBankAction:
        """Authorize a conditional source-protected GT/F5 bank."""
        from .q19_source_authority import authorize_controlled_gt_bank

        return authorize_controlled_gt_bank(
            self,
            occurrence,
            steps=steps,
            coordinate=coordinate,
            growth_control=growth_control,
            period_size=period_size,
            max_states=max_states,
        )

    def authorize_spatial_bank_morphism(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        steps: int,
        start: int,
        count: int,
        growth_control: tuple[int, ...] | CertifiedBorderGrowth,
        period_size: int = 2,
        max_states: int = 10000,
    ) -> ReverseAddSpatialBankMorphism:
        """Issue a protected multi-cell GT/EQ/LT output morphism."""
        from .q19_spatial_bank_morphism import authorize_spatial_bank_morphism

        return authorize_spatial_bank_morphism(
            self,
            occurrence,
            steps=steps,
            start=start,
            count=count,
            growth_control=growth_control,
            period_size=period_size,
            max_states=max_states,
        )

    def _range_summary(
        self, root: int, begin: int, end: int, *, reverse: bool = False
    ) -> _Q19:
        from .q19_source_authority import range_summary

        return range_summary(self, root, begin, end, reverse=reverse)

    def digit(self, occurrence: ReversePairOutputOccurrence, position: int) -> int:
        from .q19_source_authority import digit

        return digit(self, occurrence, position)

    def _iter_symbols(
        self, root: int, *, reverse: bool = False
    ) -> Generator[int, None, None]:
        def walk() -> Generator[int, None, None]:
            self._active_symbol_walks += 1
            try:
                yield from iter_symbols(
                    self.arena,
                    root,
                    reverse=reverse,
                    on_task=lambda _is_node: self.ledger.bump(
                        _shared_keys.RECURSIVE_OUTPUT_STREAM_NODE_VISITS
                    ),
                    reserve_task=lambda: self.ledger.reserve(
                        self._scratch_owner, nodes=1
                    ),
                    release_tasks=lambda count: self.ledger.release(
                        self._scratch_owner, nodes=count
                    ),
                    check_open=self._check_open,
                )
            finally:
                self._active_symbol_walks -= 1
                if self._disposed and self._active_symbol_walks == 0:
                    self._mark_scratch_disposed()
                    if self._dispose_resources_complete:
                        self._cleanup_complete = True

        return walk()

    def iter_pair_values(
        self, occurrence: ReversePairOutputOccurrence
    ) -> Generator[int, None, None]:
        self.validate(occurrence)
        yield from self._stream_pair_values(occurrence)

    def _stream_pair_values(
        self, occurrence: ReversePairOutputOccurrence
    ) -> Iterator[int]:
        self.validate(occurrence)
        encoded_length = self.arena.nodes[occurrence.root].length
        parity = self._symbol_at(occurrence.root, 0) - (2 * self.base - 1)
        if parity not in (0, 1):
            raise ValueError("pair output grammar has an invalid parity tag")
        emitted = 0
        with closing(self._iter_symbols(occurrence.root)) as forward:
            for index, symbol in enumerate(forward):
                if 0 < index < encoded_length - 1:
                    emitted += 1
                    yield symbol
        reverse_seen = 0
        with closing(self._iter_symbols(occurrence.root, reverse=True)) as backward:
            for index, symbol in enumerate(backward):
                if not 0 < index < encoded_length - 1:
                    continue
                if parity and reverse_seen == 0:
                    reverse_seen += 1
                    continue
                reverse_seen += 1
                emitted += 1
                yield symbol
        if emitted != occurrence.pair_width:
            raise AssertionError("Q19 output grammar stream changed its pair width")

    def iter_digits(self, occurrence: ReversePairOutputOccurrence) -> Iterator[int]:
        self.validate(occurrence)
        carry = 0
        emitted = 0
        with closing(self.iter_pair_values(occurrence)) as pairs:
            for pair in pairs:
                total = pair + carry
                carry, digit = divmod(total, self.base)
                emitted += 1
                self.ledger.bump(_shared_keys.RECURSIVE_OUTPUT_STREAM_EMITTED_DIGITS)
                yield digit
        if carry:
            emitted += 1
            self.ledger.bump(_shared_keys.RECURSIVE_OUTPUT_STREAM_EMITTED_DIGITS)
            yield carry
        if emitted != occurrence.output_width:
            raise AssertionError("Q19 output stream disagrees with exact width")

    def dispose(self) -> None:
        if self._cleanup_complete:
            return
        self._disposed = True
        if not self._dispose_resources_complete:
            cleanup: list[Callable[[], object]] = [
                self._unregister_payload_audit_contract,
                self._issued.dispose,
                self._spatial_bank_windows.dispose,
                self._controlled_gt_banks.dispose,
                self._border_certificates.dispose,
                self._summaries.dispose,
                *(memo.dispose for memo in self._projector_memos),
            ]

            def dispose_arena() -> None:
                nodes = self.arena.nodes
                if type(nodes) is not LedgerList:
                    raise TypeError("pair grammar lost its ledger node store")
                self.arena.dispose()

            def dispose_scratch() -> None:
                if self._active_symbol_walks == 0:
                    self._mark_scratch_disposed()

            cleanup.append(dispose_arena)
            cleanup.append(dispose_scratch)
            cleanup_all(cleanup)
            self._dispose_resources_complete = True
        if self._active_symbol_walks == 0:
            self._mark_scratch_disposed()
            self._cleanup_complete = True

    def _mark_scratch_disposed(self) -> None:
        self.ledger.mark_disposed(self._scratch_owner)

    def _unregister_payload_audit_contract(self) -> None:
        self.ledger.remove_payload_audit_contract(self, "reverse_add")


__all__ = ["ReversePairOutputOccurrence", "ReversePairQ19OutputOwner"]
