"""Powered mixed words retain exact cylinders and physical width extrema."""

from dataclasses import fields

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.border_identity import MixedParityMotif
from number_compiler.sequences.collatz.boundary_templates import (
    BoundaryActionTemplateMemo,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.mixed_clock_macros import (
    MixedClockMacro,
    select_mixed_clock_macro,
    validate_mixed_clock_macro,
)
from number_compiler.sequences.collatz.temporal_dyadic import D8TemporalTable
from tests.support.reference_arithmetic import collatz_literal


@pytest.mark.parametrize(("horizon", "preview_limit"), [(108, 96), (256, 32)])
def test_complete_or_bounded_root_probe_stops_at_first_preview(
    horizon: int, preview_limit: int
) -> None:
    seed = (1 << 160) + 48_233_076_155_686_138_603
    ledger = ResourceLedger()
    table = D8TemporalTable.for_ledger(ledger)
    with BoundaryActionTemplateMemo(ledger) as memo:
        macro = select_mixed_clock_macro(
            seed,
            horizon,
            templates=memo,
            d8_table=table,
            max_preview_bits=preview_limit,
        )
        assert macro is not None
        assert macro.normalized_symbols == 68
        assert macro.physical_ticks == 108
        assert macro.endpoint == collatz_literal(seed, 108)
        # A complete action needs no later preview. A speculative root probe
        # may also stop early while retaining its exact, shorter action.
        assert ledger.counters["collatz_mixed_clock_classifications"] == 32


@pytest.mark.parametrize("motif", [(0, 1), (1, 0, 0), (1, 1, 0), (0, 1, 0, 1, 1)])
@pytest.mark.parametrize("copies", [8, 32])
def test_mixed_cylinder_matches_literal_endpoint_and_all_widths(
    motif: tuple[int, ...],
    copies: int,
) -> None:
    ledger = ResourceLedger()
    with BoundaryActionTemplateMemo(ledger) as memo:
        action = memo.get(MixedParityMotif(motif), copies)[0]
        seed = action.source_residue + (5 << action.steps)
        ticks = (len(motif) + sum(motif)) * copies
        macro = select_mixed_clock_macro(seed, ticks, templates=memo)
        assert macro is not None
        validate_mixed_clock_macro(macro)
        assert macro.width_blank is not None
        assert macro.physical_ticks == ticks
        assert macro.endpoint == collatz_literal(seed, ticks)
        value = seed
        widths = [value.bit_length()]
        for _ in range(ticks):
            value = 3 * value + 1 if value & 1 else value // 2
            widths.append(value.bit_length())
        assert macro.width_blank.as_tuple() == (
            widths[-1] - widths[0],
            min(widths) - widths[0],
            max(widths) - widths[0],
        )
        before = ledger.counters.get("collatz_mixed_clock_coefficient_constructions", 0)
        again = select_mixed_clock_macro(seed, ticks, templates=memo)
        assert again is not None and again.fields == macro.fields
        assert (
            ledger.counters.get("collatz_mixed_clock_coefficient_constructions", 0)
            == before
        )
        assert ledger.counters["collatz_mixed_clock_width_prefixes"] == 4 * len(motif)
    assert ledger.entries == ledger.nodes == 0


def test_mixed_authority_and_short_requests() -> None:
    with pytest.raises(TypeError):
        MixedClockMacro()
    with pytest.raises(ValueError, match="authority"):
        validate_mixed_clock_macro(object.__new__(MixedClockMacro))
    with BoundaryActionTemplateMemo(ResourceLedger()) as memo:
        assert select_mixed_clock_macro(27, 15, templates=memo) is None
        action = memo.get(MixedParityMotif((1, 0, 0)), 8)[0]
        seed = action.source_residue + (5 << action.steps)
        macro = select_mixed_clock_macro(seed, 32, templates=memo)
        assert macro is not None
        forged = object.__new__(MixedClockMacro)
        for item in fields(macro):
            object.__setattr__(forged, item.name, getattr(macro, item.name))
        object.__setattr__(forged, "source", seed + 1)
        with pytest.raises(ValueError, match="changed"):
            validate_mixed_clock_macro(forged)


def test_warm_mixed_guard_does_not_recompute_modular_inverse(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with BoundaryActionTemplateMemo(ResourceLedger()) as memo:
        action = memo.get(MixedParityMotif((1, 0, 0)), 8)[0]
        seed = action.source_residue + (5 << action.steps)
        assert select_mixed_clock_macro(seed, 32, templates=memo) is not None

        def forbidden(_self: DyadicTerminalFieldAction) -> int:
            raise AssertionError("warm guard recomputed its modular inverse")

        monkeypatch.setattr(
            DyadicTerminalFieldAction, "source_residue", property(forbidden)
        )
        assert select_mixed_clock_macro(seed, 32, templates=memo) is not None
        assert action.certifies(seed)
        assert not action.certifies(seed + 1)


@pytest.mark.parametrize("seed", [True, 0, -1])
def test_mixed_selector_rejects_invalid_external_source(seed: int) -> None:
    with (
        BoundaryActionTemplateMemo(ResourceLedger()) as memo,
        pytest.raises(ValueError, match="positive exact integer"),
    ):
        select_mixed_clock_macro(seed, 100, templates=memo)
