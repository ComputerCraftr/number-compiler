"""Source-bound temporal reuse, distinct from equality of F5 observations."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
)
from number_compiler.hashlife.execution.dyadic_return_records import DyadicReturnLaw
from number_compiler.hashlife.execution.dyadic_return_transport import (
    residue_macro,
    transport_low,
)
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundSchedulerCore,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageView,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.arithmetic_images import (
    ANTIHYDRA_ARITHMETIC_LAW,
)
from number_compiler.sequences.collatz.physical_images import (
    COLLATZ_PHYSICAL_LAW,
    CollatzPhysicalImageWorkspace,
)
from tests.support.reference_arithmetic import literal_dyadic_orbit


def test_short_residue_transport_charges_operands_not_requested_precision() -> None:
    ledger = ResourceLedger()
    workspace = DyadicReturnImageWorkspace(ledger, 1, 0, COLLATZ_PHYSICAL_LAW)
    prefix = workspace.counter_prefix
    before = ledger.counters.get(prefix + "_transport_operand_bits", 0)
    assert transport_low(workspace, SkewTransfer(3, 1, 2), 9, 10**12) == 14
    assert transport_low(workspace, SkewTransfer(3, -1, 2), 9, 10**12) == 13
    assert ledger.counters[prefix + "_transport_operand_bits"] - before <= 16
    assert ledger.counters[prefix + "_transport_short_numerator_demands"] == 2
    assert transport_low(workspace, SkewTransfer(0, -2, 2), 9, 8) == 255
    assert transport_low(workspace, SkewTransfer(0, -2, 2), 9, 0) == 0
    # Canonical modular transport must still apply when the numerator is wide
    # or negative. A short-numerator optimization must not replace that semantics.
    for width in range(9):
        for source in (1, 3, 9, (1 << 100) + 1):
            for offset in (-1, 1):
                assert transport_low(
                    workspace, SkewTransfer(3, offset, 2), source, width
                ) == ((3 * source + offset) // 2) % (1 << width)
    with pytest.raises(ArithmeticError, match="integral"):
        transport_low(workspace, SkewTransfer(3, 1, 2), 2, 10**12)
    workspace.dispose()
    assert ledger.entries == ledger.nodes == 0


@pytest.mark.parametrize("law", (COLLATZ_PHYSICAL_LAW, ANTIHYDRA_ARITHMETIC_LAW))
@pytest.mark.parametrize("width", (4, 8, 16))
def test_source_only_macro_squares_without_endpoint_access(
    law: DyadicReturnLaw, width: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    # A cycle is an exact-state shortcut, not part of the universal cylinder.
    law = replace(law, cycle=None)

    def forbidden(*args: object) -> int:
        raise AssertionError("macro construction requested an exact endpoint")

    monkeypatch.setattr(DyadicReturnImageWorkspace, "source_value", forbidden)
    monkeypatch.setattr(DyadicReturnImageWorkspace, "endpoint", forbidden)
    workspace = DyadicReturnImageWorkspace(ResourceLedger(), 0, width, law)
    for residue in range(min(1 << width, 256)):
        handle = residue_macro(workspace, width, residue)
        macro = workspace.support_node(handle)
        # Same macro on several arbitrarily large high fibers, without using
        # the production operation to generate the expected orbit or weights.
        for high in (0, 1, (1 << 127) + 3):
            source = residue + (high << width)
            value, word, _odd, delta, minimum = literal_dyadic_orbit(source, width, law)
            transfer = macro.transfer
            assert (
                transfer.upper * source + transfer.offset
            ) // transfer.lower == value
            assert (macro.branch_word, macro.delta, macro.minimum) == (
                word,
                delta,
                minimum,
            )
        half = width // 2
        left = workspace.support_node(
            residue_macro(workspace, half, residue % (1 << half))
        )
        right_residue = (
            (left.transfer.upper * residue + left.transfer.offset)
            // left.transfer.lower
        ) % (1 << half)
        right = workspace.support_node(residue_macro(workspace, half, right_residue))
        assert left.branch_word is not None and right.branch_word is not None
        assert macro.branch_word == left.branch_word | (right.branch_word << half)
        assert macro.minimum == min(left.minimum, left.delta + right.minimum)
    prefix = workspace.counter_prefix
    assert (
        workspace.ledger.counters[prefix + "_macro_generator_admissions"]
        == (workspace.ledger.counters[prefix + "_macro_bounded_base_steps"])
    )
    assert workspace.ledger.counters[prefix + "_macro_bounded_base_steps"] <= (
        4 * workspace.ledger.counters[prefix + "_macro_bounded_base_calls"]
    )
    assert workspace.ledger.counters[prefix + "_macro_bounded_base_calls"] > 0
    assert workspace.ledger.counters[prefix + "_macro_bounded_base_steps"] > 0
    if width > 4:
        assert workspace.ledger.counters[prefix + "_macro_compositions"] > 0
    assert not workspace.macros and not workspace.macro_stack
    workspace.dispose()
    assert workspace.ledger.nodes == workspace.ledger.entries == 0


def test_macro_rejects_invalid_cylinders_and_disposed_workspaces() -> None:
    workspace = DyadicReturnImageWorkspace(
        ResourceLedger(), 8, 8, ANTIHYDRA_ARITHMETIC_LAW
    )
    for width, residue in ((0, 0), (65, 0), (4, -1), (4, 16), (True, 0)):
        with pytest.raises(ValueError):
            residue_macro(workspace, width, residue)
    assert not workspace.macros and not workspace.macro_stack
    macro = residue_macro(workspace, 4, 8)
    node = workspace.support_node(macro)
    offset = node.transfer.offset
    object.__setattr__(node.transfer, "offset", offset + 1)
    with pytest.raises(ValueError):
        workspace.support_node(macro)
    object.__setattr__(node.transfer, "offset", offset)
    workspace.dispose()
    with pytest.raises(ValueError):
        residue_macro(workspace, 4, 8)


def test_macro_failed_stack_publication_releases_its_reservation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    workspace = DyadicReturnImageWorkspace(ledger, 8, 8, ANTIHYDRA_ARITHMETIC_LAW)
    before = ledger.nodes, ledger.entries

    def reject(*args: object) -> None:
        raise MemoryError("injected stack publication failure")

    with monkeypatch.context() as patch:
        patch.setattr(type(workspace.macro_stack), "append", reject)
        with pytest.raises(MemoryError, match="injected"):
            residue_macro(workspace, 8, 8)
    assert (ledger.nodes, ledger.entries) == before
    assert not workspace.macro_stack and not workspace.macros
    residue_macro(workspace, 8, 8)
    workspace.dispose()
    assert ledger.nodes == ledger.entries == 0


def test_macro_partial_budget_refusal_cleans_up_without_publication() -> None:
    ledger = ResourceLedger()
    workspace = DyadicReturnImageWorkspace(ledger, 8, 8, ANTIHYDRA_ARITHMETIC_LAW)
    before = ledger.nodes, ledger.entries
    supports = len(workspace.support)
    ledger.max_nodes = ledger.nodes + 1
    with pytest.raises(BlockContextBudgetExceeded):
        residue_macro(workspace, 8, 8)
    assert (ledger.nodes, ledger.entries) == before
    assert len(workspace.support) == supports
    assert not workspace.macro_stack and not workspace.macros
    workspace.dispose()
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize("law", (COLLATZ_PHYSICAL_LAW, ANTIHYDRA_ARITHMETIC_LAW))
def test_temporal_squares_reuse_complete_high_fiber_effects(
    law: DyadicReturnLaw,
) -> None:
    ledger = ResourceLedger()
    steps, source = 1024, 1 << 4096
    workspace = DyadicReturnImageWorkspace(ledger, source, steps, law)
    expected = (source >> steps) * law.gains[0] ** steps
    assert workspace.endpoint() == expected
    assert workspace.delta() == steps * law.weights[0]
    assert workspace.minimum() == min(0, steps * law.weights[0])
    assert ledger.counters[workspace.counter_prefix + "_leaf_steps"] == 64
    assert (
        ledger.counters[workspace.counter_prefix + "_reused_temporal_extent"]
        == steps - 64
    )
    assert ledger.counters["source_image_relative_transfer_hits"] > 0
    assert len(workspace.support) <= steps.bit_length()
    # Sharing effects does not identify distinct chronological source occurrences.
    images = [node for node in workspace.images if node.summary.support is not None]
    assert any(
        a.source != b.source and a.summary.support == b.summary.support
        for a in images
        for b in images
    )
    workspace.validate()


@pytest.mark.parametrize("retain_chronology", (False, True))
def test_direct_composite_reuses_exact_homogeneous_subcylinders(
    retain_chronology: bool,
) -> None:
    """The production constructor shares effects, not source occurrences."""
    ledger = ResourceLedger()
    steps, source = 1024, 1 << 4096
    workspace = CollatzPhysicalImageWorkspace(
        ledger, source, steps, retain_chronology=retain_chronology
    )
    prefix = workspace.counter_prefix + "_"
    assert workspace.endpoint() == source >> steps
    classified = ledger.counters.get(
        prefix + "transient_leaf_steps", 0
    ) + ledger.counters.get(prefix + "macro_bounded_base_steps", 0)
    if retain_chronology:
        assert ledger.counters[prefix + "balanced_effect_memo_hits"] > 0
        assert ledger.counters[prefix + "reused_temporal_extent"] == steps - 64
        assert 0 < classified <= 64
    else:
        assert ledger.counters[prefix + "temporal_run_actions"] == 1
        assert ledger.counters[prefix + "temporal_zero_run_symbols"] == steps
        assert ledger.counters.get(prefix + "balanced_effect_memo_hits", 0) == 0
        assert classified == 0
    assert len(workspace.images) == 2
    assert len(workspace.support) <= steps.bit_length()
    assert not workspace.balanced_stack
    workspace.validate()
    workspace.dispose()
    assert ledger.nodes == ledger.entries == 0


def test_direct_composite_memo_does_not_merge_changed_source_or_duration() -> None:
    """Same zero-heavy high fiber cannot authorize a different low cylinder."""
    for steps, low in ((128, 5), (256, 7)):
        source = (1 << 4096) + low
        expected = source
        for _ in range(steps):
            expected = 3 * expected + 1 if expected & 1 else expected // 2
        ledger = ResourceLedger()
        workspace = CollatzPhysicalImageWorkspace(
            ledger, source, steps, retain_chronology=False
        )
        assert workspace.endpoint() == expected
        workspace.validate()
        workspace.dispose()
        assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize(
    "law,seed",
    ((COLLATZ_PHYSICAL_LAW, 931386509544713451), (ANTIHYDRA_ARITHMETIC_LAW, 8)),
)
def test_unmatched_sources_keep_exact_branches_and_ledger(
    law: DyadicReturnLaw, seed: int
) -> None:
    value, delta, minimum = seed, 0, 0
    for _ in range(1024):
        bit = value % 2
        value = (law.gains[bit] * value + law.offsets[bit]) // 2
        delta += law.weights[bit]
        minimum = min(minimum, delta)
    workspace = DyadicReturnImageWorkspace(ResourceLedger(), seed, 1024, law)
    assert (workspace.endpoint(), workspace.delta(), workspace.minimum()) == (
        value,
        delta,
        minimum,
    )
    workspace.validate()


def test_collatz_cycle_shortcut_cannot_leak_to_a_different_high_fiber() -> None:
    # The low precision residue 1 can mean the cycle state 1 or a very large
    # source. Only the exact singleton may use the absorbing cycle descriptor.
    from number_compiler.hashlife.execution.dyadic_return_actions import (
        append_source,
    )
    from number_compiler.hashlife.execution.dyadic_return_records import (
        DyadicReturnSourceRecord,
    )
    from number_compiler.hashlife.execution.dyadic_return_reuse import (
        admitted_input_key,
    )

    workspace = DyadicReturnImageWorkspace(ResourceLedger(), 1, 4, COLLATZ_PHYSICAL_LAW)
    core = workspace.scheduler.source_image_core()
    small = core.view(core.origin(workspace, workspace.root_source))
    large_id = append_source(
        workspace, DyadicReturnSourceRecord(1, 4, 100, None, None, None, 0, True)
    )
    large = core.view(core.origin(workspace, large_id))
    assert admitted_input_key(
        workspace, workspace.root_action, small
    ) != admitted_input_key(workspace, workspace.root_action, large)
    with pytest.raises(ValueError, match="same admitted cylinder"):
        workspace.transport_reuse(
            workspace.root_action, small, core.view(workspace.root_image), large
        )


def test_reuse_rejects_foreign_and_stale_sources() -> None:
    a = DyadicReturnImageWorkspace(ResourceLedger(), 8, 4, ANTIHYDRA_ARITHMETIC_LAW)
    _unused_b_binding, _unused_core_binding, foreign = _origin_fixture(
        8, 4, ANTIHYDRA_ARITHMETIC_LAW
    )
    with pytest.raises(ValueError):
        a.admitted_input_key(a.root_action, foreign)
    own_core = a.scheduler.source_image_core()
    own = own_core.view(own_core.origin(a, a.root_source))
    action = a.root_action
    a.dispose()
    with pytest.raises(ValueError):
        a.admitted_input_key(action, own)


def test_shared_negative_macro_preserves_first_failure_and_total_output() -> None:
    steps, source = 1024, (1 << 4096) + 1
    workspace = DyadicReturnImageWorkspace(
        ResourceLedger(), source, steps, ANTIHYDRA_ARITHMETIC_LAW
    )
    assert workspace.endpoint() == (1 << (4096 - steps)) * 3**steps + 1
    assert workspace.minimum() == workspace.delta() == -steps
    assert workspace.first_failure_index() == 0
    assert (
        workspace.ledger.counters["antihydra_arithmetic_reused_temporal_extent"] == 960
    )
    workspace.validate()


def test_reuse_construction_budget_refusal_cleans_all_partial_publications() -> None:
    ledger = ResourceLedger(max_cache_entries=80)
    with pytest.raises(BlockContextBudgetExceeded):
        DyadicReturnImageWorkspace(ledger, 1 << 4096, 1024, ANTIHYDRA_ARITHMETIC_LAW)
    assert ledger.nodes == ledger.entries == 0


def test_reuse_rejects_a_forged_source_view_even_with_valid_local_handles() -> None:
    workspace, _unused_core_binding, original = _origin_fixture(
        8, 4, ANTIHYDRA_ARITHMETIC_LAW
    )
    from number_compiler.hashlife.execution.dyadic_return_actions import (
        append_source,
    )

    another = append_source(workspace, workspace.source_node(workspace.root_source))
    forged = replace(original, binding=replace(original.binding, source=another))
    with pytest.raises(ValueError, match="differs from its publication"):
        workspace.admitted_input_key(workspace.root_action, forged)


def test_reuse_rejects_forged_view_metadata_and_cached_result() -> None:
    workspace, core, source = _origin_fixture(1 << 128, 64, COLLATZ_PHYSICAL_LAW)
    result = core.view(workspace.root_image)
    forged_views = (
        replace(source, identity=result.identity),
        replace(source, binding=replace(source.binding, precision=65)),
        replace(source, binding=replace(source.binding, boundary_ports=(999,))),
        replace(source, failure_prefix=0),
    )
    for forged in forged_views:
        with pytest.raises(ValueError, match="differs from its publication"):
            workspace.admitted_input_key(workspace.root_action, forged)
    forged_result = replace(result, binding=replace(result.binding, radix=5))
    with pytest.raises(ValueError, match="differs from its publication"):
        workspace.transport_reuse(workspace.root_action, source, forged_result, source)


@pytest.mark.parametrize("alias", (True, 0.0))
def test_reuse_rejects_integer_aliases_and_disposed_epoch(alias: object) -> None:
    workspace, _unused_core_binding, source = _origin_fixture(
        1 << 128, 64, COLLATZ_PHYSICAL_LAW
    )
    forged_action = replace(workspace.root_action)
    object.__setattr__(forged_action, "local_id", alias)
    with pytest.raises(ValueError, match="malformed scoped handle"):
        workspace.admitted_input_key(forged_action, source)

    # Numeric equality admits True/1 and 2.0/2 aliases. The publication's
    # object identity rejects a copied view with a mutated integer field.
    forged_binding = replace(source.binding)
    object.__setattr__(forged_binding, "orientation", True)
    with pytest.raises(ValueError, match="differs from its publication"):
        workspace.admitted_input_key(
            workspace.root_action, replace(source, binding=forged_binding)
        )

    old_action, old_source = workspace.root_action, source
    workspace.dispose()
    replacement = DyadicReturnImageWorkspace(
        ResourceLedger(), 1 << 128, 64, COLLATZ_PHYSICAL_LAW
    )
    assert old_action.local_id == replacement.root_action.local_id
    with pytest.raises(ValueError):
        replacement.admitted_input_key(old_action, old_source)


def _origin_fixture(
    source: int, steps: int, law: DyadicReturnLaw
) -> tuple[DyadicReturnImageWorkspace, SourceBoundSchedulerCore, SourceImageView]:
    workspace = DyadicReturnImageWorkspace(ResourceLedger(), source, steps, law)
    core = workspace.scheduler.source_image_core()
    view = core.view(core.origin(workspace, workspace.root_source))
    return workspace, core, view
