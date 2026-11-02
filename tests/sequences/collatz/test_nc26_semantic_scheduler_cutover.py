"""Regression for the source-independent border table and exact exit punctures."""

from __future__ import annotations

import json
import random
from contextlib import redirect_stdout
from io import StringIO

import pytest

from number_compiler.api.cli import main
from number_compiler.api.cli_requests import parse_request
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.border_identity import (
    CYCLE_421,
    ENTRY_421,
    ENTRY_4721,
    CycleEntryPhase,
    MixedParityMotif,
    selector_guard_for,
)
from number_compiler.sequences.collatz.boundary_macros import (
    admit_boundary_macro_plan,
)
from number_compiler.sequences.collatz.boundary_templates import (
    BoundaryActionTemplateMemo,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.joint_radix_border import (
    JointRadix6Source,
    candidate_family_for_residue160,
)
from number_compiler.sequences.collatz.skew_cylinder_repeat import (
    RepeatedWordMooreCylinder,
)
from number_compiler.sequences.collatz.temporal_unified_skew_execution import (
    has_unified_source_parent,
)
from tests.support.collatz_finite_trace import normalized_trace


def test_necessary_parent_gate_never_refuses_an_issued_named_parent() -> None:
    for source in range(1, 10_001):
        state = JointRadix6Source.from_source(source)
        plan = admit_boundary_macro_plan(
            source, 1024, minimum_repetitions=1, radix_state=state
        )
        if plan is not None or state.border_parent_candidate:
            assert has_unified_source_parent(source, 1024)
        if source > 1 and source & 1:
            numerator = 3 * source + 1
            if numerator & (numerator - 1) == 0:
                assert has_unified_source_parent(source, 1024)


def test_registry_lookup_is_source_free_and_rejects_forged_guard() -> None:
    guard = selector_guard_for(ENTRY_421)
    assert candidate_family_for_residue160(guard.residue) is ENTRY_421
    original = CYCLE_421.digits
    try:
        object.__setattr__(CYCLE_421, "digits", tuple(reversed(original)))
        with pytest.raises(ValueError, match="changed"):
            candidate_family_for_residue160(guard.residue)
    finally:
        object.__setattr__(CYCLE_421, "digits", original)
    assert candidate_family_for_residue160(guard.residue) is ENTRY_421


def test_templates_use_only_semantic_border_keys() -> None:
    ledger = ResourceLedger()
    with BoundaryActionTemplateMemo(ledger) as memo:
        first = memo.get(ENTRY_421, 3)
        equivalent = CycleEntryPhase(ENTRY_421.cycle, ENTRY_421.phase)
        assert equivalent is not ENTRY_421
        assert memo.get(equivalent, 3) is first
        for identity in (ENTRY_4721, MixedParityMotif((1, 0))):
            first = memo.get(identity, 3)
            assert memo.get(identity, 3) is first
    assert ledger.counters["collatz_boundary_template_publications"] == 3
    assert ledger.counters["collatz_boundary_template_hits"] == 3


def test_reused_parser_does_not_retain_previous_information() -> None:
    first = parse_request(
        ["collatz", "--nth", "2", "--seed", "27", "--info", "metrics"]
    )
    second = parse_request(
        ["collatz", "--nth", "3", "--seed", "27", "--info", "temporal.clock"]
    )
    assert first is not None and second is not None
    assert tuple(first.observations.info) == ("metrics",)
    assert tuple(second.observations.info) == ("temporal.clock",)


def test_exit_guard_and_first_changed_bit_against_scalar_words() -> None:
    rng = random.Random(626)
    for _ in range(450):
        source = rng.randrange(2, 1 << 15)
        length = rng.randrange(1, 8)
        starts, _endpoint = normalized_trace(source, length)
        word = tuple(value & 1 for value in starts)
        action = DyadicTerminalFieldAction.zero_run(0)
        for bit in word:
            action = action.then(
                DyadicTerminalFieldAction.one_run(1)
                if bit
                else DyadicTerminalFieldAction.zero_run(1)
            )
        cylinder = RepeatedWordMooreCylinder.from_action(
            action, source, preflight=lambda _bits: None
        )
        if cylinder.defect == 0:
            assert cylinder.remaining_repetitions is None
            assert cylinder.exit_offset is None
            assert cylinder.exact_exit_source_guard() is None
            continue
        assert cylinder.remaining_repetitions is not None
        guard = cylinder.exact_exit_source_guard()
        assert guard is not None and guard.admits(source)
        exit_offset = cylinder.exit_offset
        assert exit_offset is not None
        assert guard.modulus & (guard.modulus - 1) == 0
        assert not guard.admits(source + guard.modulus // 2)
        # Independent scalar chronology through the complete certified word.
        repetitions = cylinder.remaining_repetitions
        assert repetitions is not None
        current_starts, _endpoint = normalized_trace(
            source, repetitions * len(word) + exit_offset + 1
        )
        observed = tuple(value & 1 for value in current_starts)
        assert observed[: repetitions * len(word)] == word * repetitions
        exit_start = repetitions * len(word)
        assert observed[exit_start : exit_start + exit_offset] == word[:exit_offset]
        assert observed[exit_start + exit_offset] != word[exit_offset]


def test_public_cli_endpoint_matches_scalar_after_cutover() -> None:
    rng = random.Random(26017)
    for _ in range(35):
        seed = rng.randrange(1, 1 << 28)
        ticks = rng.randrange(0, 120)
        current = seed
        for _ in range(ticks):
            current = 3 * current + 1 if current & 1 else current // 2
        captured = StringIO()
        with redirect_stdout(captured):
            code = main(
                [
                    "collatz",
                    "--nth",
                    str(ticks),
                    "--seed",
                    str(seed),
                    "--format",
                    "json",
                ],
                shared_cache=False,
            )
        assert code == 0
        output = json.loads(captured.getvalue())
        assert int(output["value"]) == current
