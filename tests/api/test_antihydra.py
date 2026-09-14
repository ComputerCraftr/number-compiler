"""Independent literal, algebra, source-authority and CLI Antihydra controls."""

from __future__ import annotations

import json
from fractions import Fraction
from random import Random

import pytest

from number_compiler.api.cli import main
from number_compiler.sequences.antihydra.blocks import kernel, terminal_effect
from number_compiler.sequences.antihydra.certificate import check_implication, verify
from number_compiler.sequences.antihydra.machine import LiteralMachine, MACHINE_SHA256
from number_compiler.sequences.antihydra.mahler import tangent
from number_compiler.sequences.antihydra.observers import SpaceTimeProjection, tape_projection
from number_compiler.sequences.antihydra.runtime import CylinderEngine, Run, run
from number_compiler.sequences.antihydra.support import (
    directional_hasse, integer_binomial, move, section_suffix, sweep, tape_hasse, tape_intervals,
)


@pytest.mark.parametrize("a", range(4))
@pytest.mark.parametrize("b", range(3, 21))
def test_section_grammar_every_transition(a: int, b: int) -> None:
    machine = LiteralMachine.section(a, b)
    h = b+4
    effects = terminal_effect(h) if a == 0 and b & 1 else kernel(h & 1, 1).apply(h, a)[2:]
    words = [sweep(j) for j in range(b//2-1)] + [section_suffix(a, b)]
    for word in words:
        for port, count in word:
            for _ in range(count):
                assert port == 2*machine.state + int(machine.head in machine.ones)
                before = machine.time, machine.head, set(machine.ones)
                event = machine.step()
                if port == 10:
                    assert event is None and machine.halted
                    assert (machine.time, machine.head, machine.ones) == before
                else:
                    assert event is not None
    assert (machine.left, machine.right) == effects
    if not machine.halted:
        successor_a = a-1 if b & 1 else a+2
        successor_b = 3*(b//2)+3 if b & 1 else 3*(b//2)+2
        separator = -1
        assert machine.state == 4
        assert machine.head == separator+successor_b+1
        assert machine.ones == (set(range(separator-successor_a, separator))
                                | set(range(separator+1, separator+successor_b+1)))


def test_cylinder_composition_and_roof_against_scalar() -> None:
    rng = Random(912)
    engine = CylinderEngine(max_cache_entries=128)
    for _ in range(100):
        width = rng.randrange(1, 65)
        h = rng.getrandbits(width+5)+8
        a = 3*width
        block = engine.cylinder(h % (1 << width), width)
        x, balance, left, right = h, a, 0, 0
        for _ in range(width):
            k = (x-4)//2
            if x & 1:
                ticks, displacement = 3*k*k+12*k+5, k+1
                balance -= 1
            else:
                ticks, displacement = 2*balance+3*k*k+12*k+11, k+1
                balance += 2
            left += (ticks-displacement)//2
            right += (ticks+displacement)//2
            x = x+x//2
        assert block.apply(h, a) == (x, balance, left, right)
    assert engine.ledger.counters["cache_evictions"] > 0
    assert all(item.accounting_delta == 0 for item in engine.ledger.inventory())


def test_cylinder_association_and_safety() -> None:
    a, b, c = kernel(13, 4), kernel(3, 3), kernel(1, 2)
    assert a.then(b).then(c) == a.then(b.then(c))
    with pytest.raises(ValueError, match="safe admitted"):
        kernel(1, 1).apply(7, 0)
    assert sum(terminal_effect(7)) == 11


@pytest.mark.parametrize("returns", range(7))
@pytest.mark.parametrize("sign,time_sign", ((1, 1), (-1, 1), (-1, -1)))
def test_literal_spacetime_and_tape(returns: int, sign: int, time_sign: int) -> None:
    result = run(returns)
    machine = LiteralMachine()
    width, time_width, modulus = 3, 4, 7
    ports = [[0]*12 for _ in range(12)]
    moments = [[0]*3 for _ in range(2)]
    for _ in range(result.physical_ticks):
        event = machine.step()
        assert event is not None
        for order in range(3):
            moments[int(move(event.port) > 0)][order] += integer_binomial(event.head, order)
        zturn, zslot = divmod(event.head, width)
        uturn, uslot = divmod(event.time, time_width)
        factor = (-1 if sign == -1 and zturn & 1 else 1) * (
            -1 if time_sign == -1 and uturn & 1 else 1)
        ports[event.port][zslot*time_width+uslot] = (
            ports[event.port][zslot*time_width+uslot]+factor
        ) % modulus
    assert (machine.left, machine.right) == (result.left, result.right)
    assert ports == SpaceTimeProjection(result, width, time_width, sign, time_sign,
                                       modulus, 1000000).evaluate()["typed_ports"]
    actual_moments = directional_hasse(result, 2, modulus)
    assert actual_moments["left"] == [x % modulus for x in moments[0]]
    assert actual_moments["right"] == [x % modulus for x in moments[1]]
    tape = {x: 3 if x in machine.ones else 2
            for x in range(machine.visited_min, machine.visited_max+1)}
    assert tape == {x: p for lo, hi, p in tape_intervals(result) for x in range(lo, hi)}
    expected = [0]*width
    for x, p in tape.items():
        turns, slot = divmod(x, width)
        expected[slot] += p*(-1 if sign == -1 and turns & 1 else 1)
    assert tape_projection(result, width, sign, modulus).coefficients == tuple(
        x % modulus for x in expected)
    assert tape_hasse(result, 4, modulus) == tuple(
        sum(p*integer_binomial(x, k) for x, p in tape.items()) % modulus for k in range(5))


def test_sweep_period_compression_and_failure_cleanup() -> None:
    result = run(32)
    observation = SpaceTimeProjection(result, 2, 2, -1, 1, 3, 100000).evaluate()
    sampled = observation["sampled_sweep_classes"]
    assert isinstance(sampled, int) and sampled < 32*12
    assert result.physical_ticks > 10**10
    before = result.ledger.nodes
    with pytest.raises(ValueError, match="budget"):
        SpaceTimeProjection(result, 2, 2, -1, 1, 257, 1).evaluate()
    assert result.ledger.nodes == before


def test_tangent_is_bound_and_full_match_requires_refinement() -> None:
    result = run(0)
    first = tangent(result, 1)
    assert first["resolved"] is False and first["required_next_precision"] == 7
    second = tangent(result, 8)
    assert second["gap"] == 1
    with pytest.raises(ValueError, match="unbound"):
        tangent(object.__new__(Run), 8)
    assert tangent(run(1), 8)["consumed_centered_odd_events"] == 1


@pytest.mark.parametrize("kind", ("clock", "tape", "hasse", "tropical",
                                  "twisted", "modular", "spacetime", "mahler", "hensel"))
def test_cli_real_execution(kind: str, capsys: pytest.CaptureFixture[str]) -> None:
    assert main(["antihydra", "--nth", "4", "--no-value", "--info", kind, "--format", "json"]) == 0
    output = json.loads(capsys.readouterr().out)["info"][kind]
    assert output["completed_returns"] == 4
    assert output["nonhalting_certified"] is False
    assert output["work_counters"]["arithmetic_returns"] == 4


def test_cli_factor_and_source_rejection(capsys: pytest.CaptureFixture[str]) -> None:
    assert main(["antihydra", "--nth", "4", "--no-value", "--info", "factor", "--width", "3",
                 "--modulus", "9", "--format", "json"]) == 0
    data = json.loads(capsys.readouterr().out)["info"]["factor"]["value"]
    assert data["factor"] == 3 and data["factor_target"] == 9
    with pytest.raises(SystemExit) as rejected:
        main(["antihydra", "--nth", "1", "--seed", "7"])
    assert rejected.value.code == 2
    assert main(["antihydra", "--nth", "5000"]) == 2


def test_certificate_checks_arithmetic_and_source_coverage() -> None:
    one, zero = Fraction(1), Fraction(0)
    check_implication([(one, zero, zero)], (2*one, zero, zero), [2])
    with pytest.raises(ValueError, match="negative"):
        check_implication([(one, zero, zero)], (-one, zero, zero), [-1])
    with pytest.raises(ValueError, match="match"):
        check_implication([(one, zero, zero)], (zero, one, zero), [1])
    with pytest.raises(ValueError, match="schema"):
        verify({"nonhalting_certified": True, "safe_steps": 1000000})
    with pytest.raises(ValueError, match="both next"):
        verify({"schema": "antihydra-affine-charts-v1", "source": "blank",
                "machine_sha256": MACHINE_SHA256, "bits": 1, "initial": 0,
                "charts": [{"residue": 0, "inequalities": [], "branches": []}]})


def test_refinement_rejects_other_source_failures() -> None:
    from devtools.experiments.antihydra.barrier_search import candidate_failure

    for bits in (2, 4, 6):
        evidence = candidate_failure(bits, 32, 10000)
        assert evidence["status"] == "SPURIOUS_SOURCE_PATH"
        assert evidence["source_8_admitted"] is False
