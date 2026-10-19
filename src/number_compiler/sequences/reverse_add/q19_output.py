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
    from number_compiler.sequences.reverse_add.temporal_ring_harmonics import (
        ReverseAddTemporalRingBank,
    )
    from number_compiler.sequences.reverse_add.temporal_seed_morphism import (
        Q19WordFiber,
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
    occurrence_publication_snapshot,
)
from number_compiler.sequences.reverse_add.q19_output_contracts import (
    ReversePairQ19OutputAuditSnapshot,
)
from number_compiler.sequences.reverse_add.q19_punctured_producer import (
    PuncturedPairProducer,
)
from number_compiler.sequences.reverse_add.q19_summary_builder import (
    build_word_summary,
)
from number_compiler.sequences.reverse_add.q19_word_summary import (
    Q19_UPPER,
    Q19Summary,
    WordSummary,
    pair_step_law,
)


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
            self.machine = pair_step_law()
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
            self.projector.bind_cache_stores(
                forward=forward,
                reverse=backward,
                block=block,
                forward_power=forward_power,
                reverse_power=backward_power,
            )
            self._summary_owner = ledger.register(
                prefix + "-q19-summaries", "reverse_pair_q19_summary"
            )
            self._summaries = OwnedMemo[int, WordSummary](
                ledger, self._summary_owner, nodes_per_entry=1
            )
            self._issued_owner = ledger.register(
                prefix + "-issued-occurrences", "reverse_pair_output_occurrence"
            )
            self._issued = OwnedMemo[tuple[int, int], ReversePairOutputOccurrence](
                ledger, self._issued_owner, nodes_per_entry=1
            )
            self._word_fibers_owner = ledger.register(
                prefix + "-word-fibers", "observation_memo"
            )
            self._word_fibers: OwnedMemo[
                tuple[int, int, int], tuple[Q19WordFiber, tuple[object, ...]]
            ] = OwnedMemo(
                ledger, self._word_fibers_owner, nodes_per_entry=32, evictable=True
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
            self._temporal_ring_banks_owner = (
                self._issuance_registry.temporal_ring_banks.owner
            )
            self._temporal_ring_banks = self._issuance_registry.temporal_ring_banks
            self._diagonal_comparisons_owner = (
                self._issuance_registry.diagonal_comparisons.owner
            )
            self._diagonal_comparisons = self._issuance_registry.diagonal_comparisons
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
                self._temporal_ring_banks,
                self._diagonal_comparisons,
                self._word_fibers,
            )
        with ExitStack() as rollback:
            rollback.enter_context(cleanup_on_error(self.dispose))
            ledger.register_execution_root(self)
            self.initial = self._make_initial()
            self._register_payload_audit_contract()

    def _register_payload_audit_contract(self) -> None:
        self._audit_nodes = self.arena.nodes
        (
            self._audit_terms,
            self._audit_concats,
            self._audit_repeats,
        ) = self.arena.audit_interner_stores
        self._audit_summaries = self._summaries.audit_container
        self._audit_issued = self._issued.audit_container
        self._audit_word_fibers = self._word_fibers.audit_container
        self._audit_border_certificates = self._border_certificates.audit_container
        self._audit_controlled_gt_banks = self._controlled_gt_banks.audit_container
        self._audit_spatial_bank_windows = self._spatial_bank_windows.audit_container
        self._audit_temporal_ring_banks = self._temporal_ring_banks.audit_container
        self._audit_diagonal_comparisons = self._diagonal_comparisons.audit_container
        (
            self._audit_projector_forward,
            self._audit_projector_reverse,
            self._audit_projector_block,
            self._audit_projector_forward_power,
            self._audit_projector_reverse_power,
        ) = tuple(memo.audit_container for memo in self._projector_memos)
        from .q19_payload_audit_registration import (
            register_reverse_pair_output_contract,
        )

        register_reverse_pair_output_contract(
            self.ledger,
            self,
            arena_owners=self.arena.owners,
            summary_owner=self._summary_owner,
            issued_owner=self._issued_owner,
            word_fibers_owner=self._word_fibers_owner,
            border_owner=self._border_certificates_owner,
            controlled_gt_owner=self._controlled_gt_banks_owner,
            spatial_owner=self._spatial_bank_windows_owner,
            ring_owner=self._temporal_ring_banks_owner,
            diagonal_owner=self._diagonal_comparisons_owner,
            projector_owners=self._projector_owners,
        )

    def audit_snapshot(self) -> ReversePairQ19OutputAuditSnapshot:
        """Expose exact backing identities to independent, read-only audits."""
        (
            projector_forward,
            projector_reverse,
            projector_block,
            projector_forward_power,
            projector_reverse_power,
        ) = self._projector_memos
        return ReversePairQ19OutputAuditSnapshot(
            ledger=self.ledger,
            digits=self._digits,
            base=self.base,
            authority=self._authority,
            disposed=self._disposed,
            cleanup_complete=self._cleanup_complete,
            dispose_resources_complete=self._dispose_resources_complete,
            active_symbol_walks=self._active_symbol_walks,
            binding=self._binding,
            arena=self.arena,
            projector=self.projector,
            machine=self.machine,
            issuance_registry=self._issuance_registry,
            initial=self.initial,
            summary_owner=self._summary_owner,
            summaries=self._summaries.audit_snapshot(),
            issued_owner=self._issued_owner,
            issued=self._issued.audit_snapshot(),
            word_fibers_owner=self._word_fibers_owner,
            word_fibers=self._word_fibers.audit_snapshot(),
            word_fibers_binding=self._word_fibers,
            border_certificates_owner=self._border_certificates_owner,
            border_certificates=self._border_certificates.audit_snapshot(),
            border_certificates_binding=self._border_certificates,
            controlled_gt_banks_owner=self._controlled_gt_banks_owner,
            controlled_gt_banks=self._controlled_gt_banks.audit_snapshot(),
            controlled_gt_banks_binding=self._controlled_gt_banks,
            spatial_bank_windows_owner=self._spatial_bank_windows_owner,
            spatial_bank_windows=self._spatial_bank_windows.audit_snapshot(),
            spatial_bank_windows_binding=self._spatial_bank_windows,
            temporal_ring_banks_owner=self._temporal_ring_banks_owner,
            temporal_ring_banks=self._temporal_ring_banks.audit_snapshot(),
            temporal_ring_banks_binding=self._temporal_ring_banks,
            diagonal_comparisons_owner=self._diagonal_comparisons_owner,
            diagonal_comparisons=self._diagonal_comparisons.audit_snapshot(),
            diagonal_comparisons_binding=self._diagonal_comparisons,
            projector_owners=self._projector_owners,
            projector_forward=projector_forward.audit_snapshot(),
            projector_reverse=projector_reverse.audit_snapshot(),
            projector_block=projector_block.audit_snapshot(),
            projector_forward_power=projector_forward_power.audit_snapshot(),
            projector_reverse_power=projector_reverse_power.audit_snapshot(),
            projector_cache_stores=self.projector.audit_cache_stores,
            audit_bindings=(
                self._audit_nodes,
                self._audit_terms,
                self._audit_concats,
                self._audit_repeats,
                self._audit_summaries,
                self._audit_issued,
                self._audit_word_fibers,
                self._audit_border_certificates,
                self._audit_controlled_gt_banks,
                self._audit_spatial_bank_windows,
                self._audit_temporal_ring_banks,
                self._audit_diagonal_comparisons,
                self._audit_projector_forward,
                self._audit_projector_reverse,
                self._audit_projector_block,
                self._audit_projector_forward_power,
                self._audit_projector_reverse_power,
            ),
        )

    def validate_open(self) -> None:
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
            self._temporal_ring_banks,
            self._diagonal_comparisons,
            self._word_fibers,
        )
        if len(self._binding) != len(current) or any(
            original is not bound
            for original, bound in zip(self._binding, current, strict=True)
        ):
            raise ValueError("Q19 output owner or finite law binding changed")
        self._issuance_registry.validate_stores(
            border_certificates=self._border_certificates,
            controlled_gt_banks=self._controlled_gt_banks,
            spatial_bank_windows=self._spatial_bank_windows,
            temporal_ring_banks=self._temporal_ring_banks,
            diagonal_comparisons=self._diagonal_comparisons,
        )

    @property
    def is_disposed(self) -> bool:
        """Expose the owner's lifecycle state to its issuance registry."""
        return self._disposed

    def validate_issuance_registry(self, registry: Q19IssuanceRegistry) -> None:
        """Authenticate the exact registry and its retained mirrors."""
        self.validate_open()
        if self._issuance_registry is not registry:
            raise ValueError("Q19 issuance registry binding changed")

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

    def _word_summary(self, root: int) -> WordSummary:
        found = self._summaries.get(root)
        if found is not None:
            return found
        with self.ledger.reservation(
            self._scratch_owner, nodes=8 * (len(self.arena.nodes) + 1)
        ):
            return self._build_word_summary(root)

    def _build_word_summary(self, root: int) -> WordSummary:
        return build_word_summary(self.arena, self._summaries, self.ledger, root)

    def _full_summary(self, root: int) -> Q19Summary:
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
        self.validate_open()
        summary = self._full_summary(root)
        pair_width = summary.length
        output_width = pair_width + int(summary.domain == Q19_UPPER)
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
        self.validate_open()
        occurrence.__post_init__()
        key = occurrence.root, occurrence.temporal_steps
        binding = occurrence_publication_snapshot(occurrence)
        published_binding = occurrence.publication_binding
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
            if occurrence_publication_snapshot(existing) != binding:
                raise ValueError("Q19 occurrence key collides with different metadata")
            return existing
        if published_binding is None:
            occurrence.bind_publication(binding)
        self._issued[key] = occurrence
        return occurrence

    def _issue(self, root: int, temporal_steps: int) -> ReversePairOutputOccurrence:
        return self._publish(self._candidate(root, temporal_steps))

    def validate_occurrence(self, occurrence: ReversePairOutputOccurrence) -> None:
        self.validate_open()
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
        if occurrence.publication_binding != occurrence_publication_snapshot(
            occurrence
        ):
            raise ValueError("published Q19 occurrence metadata was altered")

    def validate(self, occurrence: ReversePairOutputOccurrence) -> None:
        self.validate_occurrence(occurrence)
        summary = self._full_summary(occurrence.root)
        if (
            summary.length != occurrence.pair_width
            or summary.domain != occurrence.q19_domain
            or summary.f9 != occurrence.q19_f9
            or occurrence.output_width
            != summary.length + int(summary.domain == Q19_UPPER)
            or occurrence.growth != occurrence.output_width - len(self._digits)
        ):
            raise ValueError("Q19 output metadata disagrees with its grammar")

    def validate_issued_occurrence(
        self, occurrence: ReversePairOutputOccurrence
    ) -> None:
        """Check a previously issued immutable handle without re-folding its SLP."""
        self.validate_occurrence(occurrence)

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

    def authorize_temporal_ring_bank(
        self,
        occurrence: ReversePairOutputOccurrence,
        *,
        steps: int,
        start: int = 0,
        duration: int | None = None,
        positions: tuple[int, ...] = (0,),
        source_pair_prefix: int = 0,
        window_digits: int = 3,
        max_states: int = 8192,
        max_cells: int = 16384,
        include_source_digits: bool = False,
    ) -> ReverseAddTemporalRingBank:
        """Build a *finite*, source-certified reverse/add macro ring bank.

        No 2rev10 periods are imported and no full-root REPEAT is authorized.
        """
        cert = self.certify_border_growth(
            occurrence,
            steps=steps,
            window_digits=window_digits,
            max_states=max_states,
        )
        return self.authorize_certified_temporal_ring_bank(
            cert,
            start=start,
            duration=duration,
            positions=positions,
            source_pair_prefix=source_pair_prefix,
            max_cells=max_cells,
            include_source_digits=include_source_digits,
        )

    def authorize_certified_temporal_ring_bank(
        self,
        certificate: CertifiedBorderGrowth,
        *,
        start: int = 0,
        duration: int | None = None,
        positions: tuple[int, ...] = (0,),
        source_pair_prefix: int = 0,
        include_source_digits: bool = False,
        max_cells: int = 16384,
        bank_action: SourceGuardedGTBankAction | None = None,
    ) -> ReverseAddTemporalRingBank:
        """Build and issue only from an authenticated Q19 certificate."""
        self.validate_open()
        from .q19_border_control import CertifiedBorderGrowth

        if type(certificate) is not CertifiedBorderGrowth:
            raise TypeError("temporal ring requires an exact border certificate")
        if certificate.owner is not self:
            raise ValueError("temporal ring certificate belongs to another Q19 owner")
        certificate.validate(self, certificate.source)
        from .temporal_ring_harmonics import issue_temporal_ring_bank_from_source

        return issue_temporal_ring_bank_from_source(
            certificate,
            self._issuance_registry,
            start=start,
            duration=duration,
            positions=positions,
            source_pair_prefix=source_pair_prefix,
            include_source_digits=include_source_digits,
            max_cells=max_cells,
            bank_action=bank_action,
        )

    def compose_temporal_ring_banks(
        self,
        first: ReverseAddTemporalRingBank,
        later: ReverseAddTemporalRingBank,
    ) -> ReverseAddTemporalRingBank:
        """Join adjacent issued children and publish through this Q19 owner."""
        self.validate_open()
        from .temporal_ring_harmonics import compose_issued_temporal_ring_banks

        return compose_issued_temporal_ring_banks(first, later, self._issuance_registry)

    def validate_temporal_ring_bank(self, bank: ReverseAddTemporalRingBank) -> None:
        """Validate a retained ring through its owning Q19 registry."""
        self.validate_open()
        if bank.certificate.owner is not self:
            raise ValueError("temporal ring belongs to another Q19 owner")
        self._issuance_registry.validate_temporal_ring_bank(bank)

    def _range_summary(
        self, root: int, begin: int, end: int, *, reverse: bool = False
    ) -> Q19Summary:
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
                    check_open=self.validate_open,
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
                self._word_fibers.dispose,
                self._issued.dispose,
                self._diagonal_comparisons.dispose,
                self._temporal_ring_banks.dispose,
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
