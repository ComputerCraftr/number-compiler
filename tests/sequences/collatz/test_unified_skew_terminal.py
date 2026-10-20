"""Regression: border exits, quadratic helix and skew action share one join."""

from __future__ import annotations

import unittest
from collections.abc import Generator
from contextlib import contextmanager
from typing import Protocol, cast
from unittest.mock import patch

from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.border_identity import (
    ENTRY_0563,
    BoundaryPathKind,
    CollatzSegmentIdentity,
    GuardedBorderPath,
    NonBorderSegment,
)
from number_compiler.sequences.collatz.boundary_macros import BoundaryActionTemplateMemo
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.innovation_carry_cocycle import (
    exact_source_symbol,
)
from number_compiler.sequences.collatz.innovation_port_moore import SIGNED_SYMBOLS
from number_compiler.sequences.collatz.radial_boundary_coupling import (
    CollatzRadialBoundarySeam,
)
from number_compiler.sequences.collatz.skew_cylinder_repeat import (
    RepeatedWordMooreCylinder,
)
from number_compiler.sequences.collatz.temporal_run_quotient import (
    CollatzTemporalRunQuotient,
    compile_collatz_temporal_run_quotient,
)
from number_compiler.sequences.collatz.unified_skew_chain import (
    BoundaryWitness,
    FactorSpecs,
    UnifiedSkewChain,
    select_unified_skew_chain,
)
from number_compiler.sequences.collatz.unified_skew_clock import SkewQuadraticClock
from tests.support.collatz_finite_trace import normalized_trace, physical_values


class _UnifiedChainFactory(Protocol):
    def __call__(
        self,
        source: int,
        endpoint: int,
        fields: DyadicTerminalFieldAction,
        width_blank: BlankLedger,
        clock: SkewQuadraticClock | None,
        odd_symbols: int,
        factors: FactorSpecs,
        segment_identities: tuple[CollatzSegmentIdentity, ...],
        first_boundary: tuple[int, BoundaryWitness] | None,
        seams: tuple[CollatzRadialBoundarySeam, ...],
        repeat_cylinder: RepeatedWordMooreCylinder | None = None,
    ) -> UnifiedSkewChain: ...


def _issue_unified_chain(
    source: int,
    endpoint: int,
    fields: DyadicTerminalFieldAction,
    width_blank: BlankLedger,
    clock: SkewQuadraticClock | None,
    odd_symbols: int,
    factors: FactorSpecs,
    segment_identities: tuple[CollatzSegmentIdentity, ...],
    first_boundary: tuple[int, BoundaryWitness] | None,
    seams: tuple[CollatzRadialBoundarySeam, ...],
    repeat_cylinder: RepeatedWordMooreCylinder | None = None,
) -> UnifiedSkewChain:
    factory = cast(
        _UnifiedChainFactory,
        type.__getattribute__(UnifiedSkewChain, "_issue"),
    )
    return factory(
        source,
        endpoint,
        fields,
        width_blank,
        clock,
        odd_symbols,
        factors,
        segment_identities,
        first_boundary,
        seams,
        repeat_cylinder,
    )


def required_quadratic_clock(chain: UnifiedSkewChain) -> SkewQuadraticClock:
    if chain.clock is None:
        raise AssertionError("requested innovation did not publish its clock")
    return chain.clock


@contextmanager
def source_assertions(source: int) -> Generator[None, None, None]:
    try:
        yield
    except AssertionError as error:
        raise AssertionError(f"source={source}: {error}") from error


def assert_normalized_accumulator(
    case: unittest.TestCase,
    result: CollatzTemporalRunQuotient,
    source: int,
    normalized: tuple[int, ...],
    modulus: int,
) -> None:
    expected = source + sum(
        (3 * value + 1) // 2 if value & 1 else value // 2 for value in normalized
    )
    case.assertEqual(
        result.accumulator(modulus).normalized_accumulator_residue,
        expected % modulus,
    )


class UnifiedSkewTerminalRegression(unittest.TestCase):
    def test_composer_charges_nested_border_discovery(self) -> None:
        ledger = ResourceLedger()
        with BoundaryActionTemplateMemo(ledger) as memo:
            chain = select_unified_skew_chain(
                23,
                15,
                templates=memo,
                ledger=ledger,
                include_quadratic_clock=False,
            )
        if chain is None:
            raise AssertionError("expected a source-certified border chain")
        self.assertGreater(
            ledger.counters.get("collatz_physical_border_return_candidate_checks", 0),
            0,
        )
        self.assertGreater(
            ledger.counters.get("collatz_physical_border_return_valuation_checks", 0),
            0,
        )

    def test_exact_skew_power_and_cross_family_moments(self) -> None:
        for length in range(1, 9):
            for code in range(1 << length):
                bits = tuple((code >> j) & 1 for j in range(length))
                direct = SkewQuadraticClock.factors(((bits, 1),), 24)
                powers = SkewQuadraticClock.identity(24)
                action = DyadicTerminalFieldAction.identity()
                for bit in bits:
                    powers = powers.then(SkewQuadraticClock.atom(bit, 24))
                    action = action.then(
                        DyadicTerminalFieldAction.one_run(1)
                        if bit
                        else DyadicTerminalFieldAction.zero_run(1)
                    )
                self.assertEqual(direct, powers)
                self.assertEqual(direct.value, action.offset % (1 << 24))
                for reps in (2, 3, 5):
                    clock = direct.power(reps)
                    field = action.power(reps)
                    self.assertEqual(clock.value, field.offset % (1 << 24))
                    self.assertEqual(clock.steps, field.steps)

    def test_unified_skew_chain_is_one_guarded_action_with_both_clocks(self) -> None:
        expectations = {
            13: (
                9,
                (
                    GuardedBorderPath(BoundaryPathKind.THREE_BORDER_RETURN, 3, 4),
                    NonBorderSegment.ZERO_RUN,
                ),
            ),
            23: (
                15,
                (
                    GuardedBorderPath(BoundaryPathKind.THREE_BORDER_RETURN, 3, 4),
                    NonBorderSegment.ZERO_RUN,
                ),
            ),
            26: (
                10,
                (
                    GuardedBorderPath(BoundaryPathKind.THREE_BORDER_RETURN, 6, 4),
                    NonBorderSegment.ZERO_RUN,
                ),
            ),
            30: (
                18,
                (
                    ENTRY_0563,
                    NonBorderSegment.ZERO_RUN,
                    NonBorderSegment.TERMINAL_POWER_OF_TWO,
                ),
            ),
        }
        for source, (ticks, segments) in expectations.items():
            with source_assertions(source):
                ledger = ResourceLedger()
                result = compile_collatz_temporal_run_quotient(
                    source,
                    ticks,
                    ledger=ledger,
                    include_joint_cocycle=True,
                    include_width_spine=True,
                    include_f5=True,
                    include_innovation_tape=True,
                    innovation_modulus=49,
                )
                values = physical_values(source, ticks)
                target = values[-1]
                self.assertEqual(target, 1)
                self.assertEqual(result.endpoint, 1)
                self.assertEqual(result.run_actions, 1)
                chain = result.unified_skew_chain
                if chain is None:
                    raise AssertionError("expected a producer-issued joined prefix")
                self.assertEqual(chain.segment_identities, segments)
                self.assertEqual(chain.physical_ticks, ticks)
                self.assertEqual(chain.normalized_symbols + chain.odd_symbols, ticks)
                clock = required_quadratic_clock(chain)
                self.assertEqual(clock.physical_ticks, ticks)
                clock.verify(chain.fields, source, 1)
                self.assertEqual(chain.fields.endpoint(source), 1)
                self.assertEqual(
                    ledger.counters["collatz_physical_unified_skew_terminal_actions"], 1
                )
                self.assertEqual(
                    ledger.counters.get("collatz_physical_temporal_dyadic_d8_pumps", 0),
                    0,
                )
                self.assertIsNotNone(result.joint_action)
                if result.tape_width_summary is None:
                    raise AssertionError("width observer was not published")
                if result.innovation_observation is None:
                    raise AssertionError("innovation observer was not published")
                width = result.tape_width_summary.blank
                self.assertEqual(
                    source.bit_length() + width.minimum,
                    min(map(int.bit_length, values)),
                )
                self.assertEqual(
                    source.bit_length() + width.maximum,
                    max(map(int.bit_length, values)),
                )
                if result.physical_f5 is None:
                    raise AssertionError("physical F5 action was not published")
                self.assertEqual(result.physical_f5.apply(source), 1)
                normalized, current = normalized_trace(
                    source, result.normalized_symbols
                )
                self.assertEqual(current, 1)
                tape = result.innovation_observation
                expected = tuple(exact_source_symbol(v, 49) for v in normalized)
                self.assertEqual(
                    tuple(tape.symbol_counts),
                    tuple(expected.count(s) for s in SIGNED_SYMBOLS),
                )
                self.assertEqual(tuple(tape.sample), expected[: len(tape.sample)])
                assert_normalized_accumulator(
                    self, result, source, normalized, modulus=49
                )

    def test_longer_horizon_still_powers_terminal_cycle(self) -> None:
        for source, terminal_ticks in ((13, 9), (23, 15), (30, 18)):
            with source_assertions(source):
                ticks = terminal_ticks + 12
                result = compile_collatz_temporal_run_quotient(
                    source,
                    ticks,
                    ledger=ResourceLedger(),
                    include_joint_cocycle=True,
                    include_innovation_tape=True,
                    innovation_modulus=5,
                )
                self.assertEqual(result.endpoint, physical_values(source, ticks)[-1])
                self.assertIsNotNone(result.unified_skew_chain)
                self.assertEqual(result.run_actions, 2)
                self.assertEqual(result.cycle_repetitions, 4)

    def test_missing_terminal_certificate_never_invents_future(self) -> None:
        high_source = (1 << 1100) + 30
        with BoundaryActionTemplateMemo(ResourceLedger()) as memo:
            self.assertIsNone(select_unified_skew_chain(30, 17, templates=memo))
            self.assertIsNone(select_unified_skew_chain(190, 18, templates=memo))
            high_chain = select_unified_skew_chain(high_source, 18, templates=memo)
        if high_chain is None:
            raise AssertionError(
                "expected an exact source-bound live prefix for the high fiber"
            )
        self.assertFalse(high_chain.reaches_terminal)
        self.assertLessEqual(high_chain.physical_ticks, 18)
        self.assertEqual(
            high_chain.endpoint,
            physical_values(high_source, high_chain.physical_ticks)[-1],
        )
        high_chain.verify()
        for source, ticks in ((30, 17), (190, 18), (43, 7)):
            result = compile_collatz_temporal_run_quotient(
                source,
                ticks,
                ledger=ResourceLedger(),
            )
            self.assertIsNone(result.unified_skew_chain)
            self.assertEqual(result.endpoint, physical_values(source, ticks)[-1])

    def test_shared_cache_miss_joins_high_fiber_without_eager_quadratic_clock(
        self,
    ) -> None:
        from number_compiler.sequences.collatz.temporal_dyadic import D8TemporalTable

        source, ticks = (1 << 1100) + 30, 18
        ledger = ResourceLedger()
        with patch.object(
            D8TemporalTable,
            "transition",
            side_effect=AssertionError("a certified high-fiber join entered D8"),
        ):
            result = compile_collatz_temporal_run_quotient(
                source,
                ticks,
                ledger=ledger,
                shared_cache=True,
            )
        chain = result.unified_skew_chain
        if chain is None:
            raise AssertionError("shared-cache miss skipped the source-bound join")
        if chain.clock is not None:
            raise AssertionError("an undemanded quadratic observer was constructed")
        self.assertFalse(chain.reaches_terminal)
        self.assertEqual(
            chain.endpoint,
            physical_values(source, chain.physical_ticks)[-1],
        )
        self.assertGreaterEqual(
            ledger.counters.get("collatz_physical_unified_skew_applied_actions", 0),
            1,
        )
        self.assertEqual(
            ledger.counters.get(
                "collatz_physical_temporal_d8_frame_materializations", 0
            ),
            0,
        )
        self.assertEqual(result.endpoint, physical_values(source, ticks)[-1])

    def test_live_cross_family_handoff_keeps_the_quadratic_seam(self) -> None:
        source, ticks = 2174, 120
        ledger = ResourceLedger()
        result = compile_collatz_temporal_run_quotient(
            source,
            ticks,
            ledger=ledger,
            include_f5=True,
            include_width_spine=True,
            include_joint_cocycle=True,
            include_innovation_tape=True,
            innovation_modulus=49,
        )
        chain = result.unified_skew_chain
        if chain is None:
            raise AssertionError("expected a joined live prefix")
        self.assertFalse(chain.reaches_terminal)
        self.assertGreater(len(chain.segment_identities), 2)
        self.assertLessEqual(chain.physical_ticks, ticks)
        # The exact parity word may repeat without preserving its absolute
        # bit-width envelope, so the complete width observer keeps the
        # scheduler's ordinary source-relative path.
        self.assertEqual(
            ledger.counters.get(
                "collatz_physical_unified_skew_additional_repetitions", 0
            ),
            0,
        )
        width = result.tape_width_summary
        if width is None:
            raise AssertionError("complete width observer was not published")
        values = physical_values(source, ticks)
        self.assertEqual(
            width.blank.minimum,
            min(v.bit_length() for v in values) - source.bit_length(),
        )
        self.assertEqual(
            width.blank.maximum,
            max(v.bit_length() for v in values) - source.bit_length(),
        )
        clock = required_quadratic_clock(chain)
        self.assertEqual(clock.physical_ticks, chain.physical_ticks)
        self.assertEqual(
            chain.endpoint,
            physical_values(source, chain.physical_ticks)[-1],
        )
        chain.verify()
        self.assertEqual(result.endpoint, physical_values(source, ticks)[-1])
        normalized, current = normalized_trace(source, result.normalized_symbols)
        self.assertEqual(
            result.endpoint,
            current if result.phase == 0 else 3 * current + 1,
        )
        expected = tuple(exact_source_symbol(v, 49) for v in normalized)
        tape = result.innovation_observation
        if tape is None:
            raise AssertionError("innovation observer was not published")
        self.assertEqual(
            tuple(tape.symbol_counts), tuple(expected.count(s) for s in SIGNED_SYMBOLS)
        )
        assert_normalized_accumulator(self, result, source, normalized, modulus=49)

    def test_composed_action_retains_independent_border_return_clocks(self) -> None:
        result = compile_collatz_temporal_run_quotient(
            23,
            15,
            ledger=ResourceLedger(),
            include_innovation_tape=True,
            innovation_modulus=49,
        )
        macro = result.first_boundary_macro
        if macro is None:
            raise AssertionError("expected the first producer-issued boundary")
        packet = macro.observation()
        self.assertEqual(packet["return_physical_ticks"], (4, 8))
        self.assertEqual(packet["return_normalized_steps"], (2, 6))
        chain = result.unified_skew_chain
        if chain is None:
            raise AssertionError("expected the composed skew prefix")
        self.assertEqual(chain.physical_ticks, 15)
        self.assertEqual(chain.normalized_symbols, 11)

    def test_unified_skew_chain_is_sealed_and_not_a_cross_fiber_terminal_oracle(
        self,
    ) -> None:
        with self.assertRaises(TypeError):
            UnifiedSkewChain()
        with BoundaryActionTemplateMemo(ResourceLedger()) as memo:
            chain = select_unified_skew_chain(30, 18, templates=memo)
        if chain is None:
            raise AssertionError("expected a composed terminal chain")
        # Keep the issued clock/seam shape intact and change only the source
        # residue, so this exercises source admission rather than shape rejection.
        with self.assertRaisesRegex(ValueError, "certify their source"):
            _issue_unified_chain(
                chain.source ^ 1,
                chain.endpoint,
                chain.fields,
                chain.width_blank,
                chain.clock,
                chain.odd_symbols,
                chain.factors,
                chain.segment_identities,
                chain.first_boundary,
                chain.seams,
            )
        lift = chain.source + (1 << chain.normalized_symbols)
        self.assertTrue(chain.fields.certifies(lift))
        self.assertNotEqual(chain.fields.endpoint(lift), 1)
        # Even a field-algebra-valid forged occurrence cannot become a
        # producer-issued terminal certificate.
        fake = object.__new__(UnifiedSkewChain)
        for name in (
            "source",
            "endpoint",
            "fields",
            "width_blank",
            "clock",
            "odd_symbols",
            "factors",
            "segment_identities",
            "first_boundary",
            "seams",
            "repeat_cylinder",
            "_issuer",
            "_binding",
        ):
            object.__setattr__(fake, name, getattr(chain, name))
        object.__setattr__(fake, "source", lift)
        with self.assertRaises(ValueError):
            fake.verify()

    def test_cli_publishes_one_fused_action_with_signed_tape(self) -> None:
        import json
        import subprocess
        import sys

        argv = [
            sys.executable,
            "-m",
            "number_compiler",
            "collatz",
            "--seed",
            "30",
            "--nth",
            "18",
            "--no-value",
            "--info",
            "temporal.macro",
            "--info",
            "temporal.innovation-borrow",
            "--temporal-innovation-borrow-modulus",
            "49",
            "--format",
            "json",
        ]
        proc = subprocess.run(
            argv,
            capture_output=True,
            text=True,
            check=True,
            timeout=15,
        )
        packet = json.loads(proc.stdout)
        border = packet["info"]["temporal.macro"]
        self.assertEqual(border["unified_skew_composed_actions"], 1)
        self.assertEqual(border["unified_skew_terminal_actions"], 1)
        self.assertEqual(border["unified_skew_joined_segments"], 3)
        self.assertEqual(border["normalized_signed_tape"]["normalized_steps"], 13)
        self.assertEqual(border["normalized_signed_tape"]["normalized_endpoint"], 1)
        innovation = packet["info"]["temporal.innovation-borrow"]
        position = innovation["position_cycle_harmonics"]
        self.assertEqual(position["status"], "complete")
        self.assertEqual(
            tuple(
                (
                    item["radix"],
                    item["position_lsd_zero_indexed"],
                )
                for item in position["spectra"]
            ),
            ((6, 0), (10, 0)),
        )

    def test_full_chain_does_not_enter_d8_selector(self) -> None:
        from number_compiler.sequences.collatz.temporal_dyadic import D8TemporalTable

        with patch.object(
            D8TemporalTable,
            "transition",
            side_effect=AssertionError("D8 replay"),
        ):
            result = compile_collatz_temporal_run_quotient(
                30,
                18,
                ledger=ResourceLedger(),
                include_joint_cocycle=True,
            )
            self.assertEqual(result.endpoint, 1)
            self.assertEqual(result.run_actions, 1)
            self.assertEqual(
                result.unified_skew_chain.physical_ticks
                if result.unified_skew_chain
                else 0,
                18,
            )


if __name__ == "__main__":
    unittest.main()
