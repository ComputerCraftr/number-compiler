"""Connected quotient control must keep exact values at downstream guards."""

import random
from itertools import product

import pytest

from devtools.verification.consumer_fixtures import free_collatz_variables
from number_compiler.arithmetic.carry.collatz_output_quotient import (
    CORRECTIONS,
    radix64_domain,
    radix64_free_directional_row,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.functions.finite_function_types import (
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.output_morphism import (
    CARRY,
    DIGIT,
    DOMAIN,
    FREE_CARRY_ACTION,
    RESIDUAL_SHIFT,
    CollatzOutputMorphism,
)
from number_compiler.sequences.collatz.radix64_transducer import (
    Radix64CollatzStage,
    compose_radix64_events,
)
from tests.support.assertions import assert_clean_payloads
from tests.support.reference_arithmetic import literal_events as _oracle


def _digits(n: int) -> tuple[int, ...]:
    result = []
    while n:
        n, d = divmod(n, 64)
        result.append(d)
    return tuple(result)


def test_symbolic_raw_output_and_correction_all_primitive_ports() -> None:
    ledger = ResourceLedger()
    bits = BitFunctionArena(ledger)
    morphism, ports, d, c = _raw_variables(bits)
    outgoing, raw = morphism.raw(d, c)
    correction = morphism.correction(c, outgoing)
    domain = morphism.domain(raw)
    for shift in range(6):
        edge = morphism.growth(c, shift)
        for carry in range(3):
            assert (
                bits.evaluate(edge, {ports[0].variable: 0, ports[1].variable: carry})
                == carry >> shift
            )
    assert morphism.growth(c, 2) == morphism.growth(c, 5)
    for digit, carry in product(range(64), range(3)):
        binding = {ports[0].variable: digit, ports[1].variable: carry}
        out, value = _assert_raw_pair(bits, outgoing, raw, binding, digit, carry)
        assert bits.evaluate(domain, binding) == radix64_domain(value)
        assert bits.evaluate(correction, binding) == CORRECTIONS.index(carry - 64 * out)
    assert_clean_payloads(ledger)


def test_raw_value_path_does_not_decode_the_seventeen_way_joint_observer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from devtools.verification import collatz_harmonic_ports

    bits = BitFunctionArena(ResourceLedger())
    morphism, ports, digit, carry = _raw_variables(bits)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("geometry-first value path decoded a redundant joint observer")

    monkeypatch.setattr(CollatzOutputMorphism, "classify", forbidden)
    monkeypatch.setattr(collatz_harmonic_ports, "radix64_phi5", forbidden)
    outgoing, raw = morphism.raw(digit, carry)
    for d, c in product(range(64), range(3)):
        binding = {ports[0].variable: d, ports[1].variable: c}
        _assert_raw_pair(bits, outgoing, raw, binding, d, c)


def test_different_domain_geometries_share_complete_carry_correction_morphisms() -> (
    None
):
    bits = BitFunctionArena(ResourceLedger())
    morphism = CollatzOutputMorphism(bits)
    port = FinitePort(PortVariable(0, 0, "incoming", 0), 3)
    incoming = bits.variable((port,), port, CARRY)
    actions = tuple(
        bits.constant(FunctionSignature((port,), DOMAIN), d) for d in range(5)
    )
    outputs = []
    for geometry in ((0, 2, 1), (0, 3, 1), (0, 2, 3), (0, 3, 3)):
        carry = incoming
        corrections = []
        for domain in geometry:
            next_carry = morphism.carry_apply(actions[domain], carry)
            corrections.append(morphism.correction(carry, next_carry))
            carry = next_carry
        outputs.append((carry, tuple(corrections)))
    assert all(output == outputs[0] for output in outputs)
    for c in range(3):
        binding = {port.variable: c}
        assert bits.evaluate(outputs[0][0], binding) == 1
        assert tuple(bits.evaluate(f, binding) for f in outputs[0][1]) == (
            CORRECTIONS.index(c),
            CORRECTIONS.index(-64),
            CORRECTIONS.index(-63),
        )


def test_symbolic_temporal_composition_keeps_value_register_in_guards() -> None:
    bits = BitFunctionArena(ResourceLedger(max_nodes=200000))
    morphism = CollatzOutputMorphism(bits)
    ports = tuple(FinitePort(PortVariable(0, i, "source", 0), 64) for i in range(3))
    source = tuple(bits.variable(ports, p, DIGIT) for p in ports)
    one = bits.constant(FunctionSignature(ports, CARRY), 1)
    c1, r0 = morphism.raw(source[0], one)
    c2, r1 = morphism.raw(source[1], c1)
    _, r2 = morphism.raw(source[2], c2)
    y0, y1 = morphism.shift(r0, r1, 3), morphism.shift(r1, r2, 3)
    next_c, s0 = morphism.raw(y0, one)
    _, s1 = morphism.raw(y1, next_c)
    result = morphism.shift(s0, s1, 1)
    domain = morphism.domain(result)
    # Rebuilding the same extensional output uses canonical finite-function IDs.
    assert morphism.shift(s0, s1, 1) == result
    rng = random.Random(64917)
    for _ in range(128):
        ds = tuple(rng.randrange(64) for _ in ports)
        n = sum(d * 64**i for i, d in enumerate(ds))
        expected = (3 * ((3 * n + 1) // 8) + 1) // 2 % 64
        binding = {p.variable: d for p, d in zip(ports, ds, strict=True)}
        assert bits.evaluate(result, binding) == expected
        assert bits.evaluate(domain, binding) == radix64_domain(expected)
    # This checks declared local phases, not their whole-event admissibility.


def test_directional_domain_consumer_avoids_exact_joint_leaf(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from devtools.verification import collatz_harmonic_ports

    bits = BitFunctionArena(ResourceLedger(max_nodes=200000))
    morphism, ports, raw, adjacent = _adjacent_raw_variables(bits)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("directional consumer reconstructed the old joint leaf")

    # These are assertion-side observers, not dependencies of the directional
    # compiler.  Poisoning them prevents an exact digit or harmonic decode from
    # being hidden behind a later domain projection.
    monkeypatch.setattr(CollatzOutputMorphism, "shift", forbidden)
    monkeypatch.setattr(CollatzOutputMorphism, "domain", forbidden)
    monkeypatch.setattr(collatz_harmonic_ports, "radix64_phi5", forbidden)
    outputs = tuple(
        morphism.pair_domain_views(
            morphism.left_domain_view(raw, shift),
            morphism.right_domain_view(adjacent, shift),
            shift,
        )
        for shift in range(6)
    )
    for a, b, shift in product(range(64), range(64), range(6)):
        binding = {ports[0].variable: a, ports[1].variable: b}
        assert bits.evaluate(outputs[shift], binding) == radix64_domain(
            (a + 64 * b) >> shift & 63
        )
    assert bits.ledger.counters["collatz_directional_domain_compositions"] == 6


def test_free_future_consumer_defers_carry_and_root_shift_without_raw_midpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger(max_nodes=200000)
    bits = BitFunctionArena(ledger)
    morphism = CollatzOutputMorphism(bits)
    ports, digit, carry, shift = free_collatz_variables(bits)
    growth_ports = ports[1:]
    growth_carry = bits.variable(growth_ports, growth_ports[0], CARRY)
    growth_shift = bits.variable(growth_ports, growth_ports[1], RESIDUAL_SHIFT)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("free consumer materialized a selected raw/value fiber")

    monkeypatch.setattr(CollatzOutputMorphism, "raw", forbidden)
    monkeypatch.setattr(CollatzOutputMorphism, "directional", forbidden)
    monkeypatch.setattr(CollatzOutputMorphism, "left_domain_view", forbidden)
    monkeypatch.setattr(CollatzOutputMorphism, "right_domain_view", forbidden)
    monkeypatch.setattr(CollatzOutputMorphism, "growth", forbidden)
    left, right = morphism.free_directional_actions(digit, carry, shift)
    growth = morphism.free_growth(growth_carry, growth_shift)
    assert bits.resolve(left).signature.output == FREE_CARRY_ACTION
    assert bits.resolve(right).signature.output == FREE_CARRY_ACTION
    assert bits.resolve(left).signature.inputs == ports
    assert bits.resolve(right).signature.inputs == ports
    assert bits.resolve(growth).signature.inputs == growth_ports
    assert not ledger.counters.get("collatz_output_morphism_raw_compositions", 0)
    expected_rows = tuple(
        tuple(radix64_free_directional_row(phase, incoming) for incoming in range(3))
        for phase in range(6)
    )
    fixed_counts = []
    free_rows = []
    for value in range(64):
        row = []
        for phase, incoming in product(range(6), range(3)):
            binding = {
                ports[0].variable: value,
                ports[1].variable: incoming,
                ports[2].variable: phase,
            }
            expected = expected_rows[phase][incoming][value]
            observed = bits.evaluate(left, binding), bits.evaluate(right, binding)
            assert observed == expected
            assert (
                bits.evaluate(
                    growth,
                    {
                        growth_ports[0].variable: incoming,
                        growth_ports[1].variable: phase,
                    },
                )
                == incoming >> phase
            )
            row.append(observed)
        free_rows.append(tuple(row))
    for phase, incoming in product(range(6), range(3)):
        fixed_counts.append(
            len({expected_rows[phase][incoming][value] for value in range(64)})
        )
    assert fixed_counts[::3] == [5, 10, 20, 25, 20, 10]
    assert all(
        len(set(fixed_counts[offset : offset + 3])) == 1 for offset in range(0, 18, 3)
    )
    # Simultaneously exposing every hypothetical (carry, shift) context is an
    # exact leaf observer, so these rows are forbidden as semantic ActionIDs.
    assert len(set(free_rows)) == 64


def test_exact_shift_uses_adjacent_directional_value_views() -> None:
    bits = BitFunctionArena(ResourceLedger(max_nodes=200000))
    morphism, ports, raw, adjacent = _adjacent_raw_variables(bits)
    for shift in range(6):
        left, _ = morphism.directional(raw, shift)
        _, right = morphism.directional(adjacent, shift)
        target = morphism.shift(raw, adjacent, shift)
        target_domain = morphism.shift_domain(raw, adjacent, shift)
        assert morphism.join_directional(left, right, shift) == target
        for a, b in product(range(64), repeat=2):
            binding = {ports[0].variable: a, ports[1].variable: b}
            assert bits.evaluate(left, binding) == a >> shift
            assert bits.evaluate(right, binding) == b % (1 << shift)
            assert bits.evaluate(target, binding) == (a + 64 * b) >> shift & 63
            assert bits.evaluate(target_domain, binding) == radix64_domain(
                (a + 64 * b) >> shift & 63
            )


def test_live_radix64_path_avoids_redundant_field_construction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz import raw_field

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("radix-64 event used the old redundant field")

    monkeypatch.setattr(raw_field, "_raw_divided_coefficients", forbidden)
    for n in (1, 21, 27, 85, 1836429, 1856909, 64**12 * 2 + (64**12 - 1) // 3):
        target, k = _oracle(n, 1)
        step = raw_field.accelerated_collatz_sentinel_step(n, base=64)
        assert step.target_digits == _digits(target)
        assert step.valuation == k


def test_streaming_stage_retains_only_left_directional_value_view() -> None:
    stage = Radix64CollatzStage()
    assert stage.feed(43) is None
    # 3*43+1 = 2 (mod 64), e=1: retain q=1 rather than exact raw digit 2.
    assert stage.shift == 1
    assert stage.pending == 1
    assert stage.feed(42) == 1
    # 3*42+2 = 0 (mod 64): its left view is zero; its right view was consumed.
    assert stage.pending == 0
    assert stage.finish() == (0, 1)


def test_streaming_temporal_composition_matches_exact_targets_weights_and_frames() -> (
    None
):
    rng = random.Random(641152)
    sources = [1, 21, 27, 85, 1836429, 1856909]
    sources += [
        rng.getrandbits(width) | 1 for width in (64, 256, 2048) for _ in range(8)
    ]
    for n, events in product(sources, (1, 2, 4)):
        expected, k = _oracle(n, events)
        # A single-pass input cannot be revisited or converted into a midpoint.
        result = compose_radix64_events(iter(_digits(n)), events)
        assert result.target_digits == _digits(expected)
        assert result.valuation == k
        ds = _digits(expected)
        frame = next((i for i, d in enumerate(ds) if d != 21), len(ds))
        assert result.exit_frame == frame
        assert result.carry_peak <= 2


def test_1152_frame_translation_preserves_target_and_exact_weight_difference() -> None:
    # n_q = 64**q*m + (64**q-1)/3; strip q before the raw controller.
    m = 450
    results = [compose_radix64_events((21,) * q + _digits(m), 2) for q in (1, 193)]
    a, b = results
    assert a.target_digits == b.target_digits
    assert a.exit_frame == b.exit_frame
    assert b.valuation - a.valuation == 1152
    assert b.source_frame - a.source_frame == 192


def test_two_event_stream_exhausts_small_sources_and_boundary_phases() -> None:
    phases = set()
    for n in range(1, 4096, 2):
        result = compose_radix64_events(iter(_digits(n)), 2)
        expected, k = _oracle(n, 2)
        assert result.target_digits == _digits(expected)
        assert result.valuation == k
        phases.add(result.source_shift)
    assert phases == set(range(6))


def test_symbolic_sort_and_publication_budget_and_stream_boundaries_fail_closed() -> (
    None
):
    ledger = ResourceLedger()
    bits = BitFunctionArena(ledger)
    morphism = CollatzOutputMorphism(bits)
    d = bits.constant(FunctionSignature((), DIGIT), 5)
    c = bits.constant(FunctionSignature((), CARRY), 1)
    before = ledger.snapshot()
    with pytest.raises(ValueError):
        morphism.shift(d, d, 6)
    assert ledger.entries == before.entries
    _, remainder = morphism.directional(d, 1)
    with pytest.raises(ValueError):
        morphism.join_directional(d, remainder, 1)
    with pytest.raises(ValueError):
        morphism.raw(c, d)
    ledger.max_nodes = ledger.nodes
    with pytest.raises(BlockContextBudgetExceeded):
        morphism.raw(d, c)
    with pytest.raises(BlockContextBudgetExceeded):
        compose_radix64_events(iter(()), 65)
    for source in ((), (2,), (1, 0)):
        with pytest.raises(ValueError):
            compose_radix64_events(source)
    stage = Radix64CollatzStage()
    stage.feed(1)
    assert stage.finish() == (1,)
    with pytest.raises(ValueError):
        stage.feed(1)
    with pytest.raises(ValueError):
        stage.finish()


def _raw_variables(
    bits: BitFunctionArena,
) -> tuple[
    CollatzOutputMorphism,
    tuple[FinitePort, FinitePort],
    FactoredFunctionID,
    FactoredFunctionID,
]:
    morphism = CollatzOutputMorphism(bits)
    ports = (
        FinitePort(PortVariable(0, 0, "digit", 0), 64),
        FinitePort(PortVariable(0, 1, "carry", 0), 3),
    )
    return (
        morphism,
        ports,
        bits.variable(ports, ports[0], DIGIT),
        bits.variable(ports, ports[1], CARRY),
    )


def _adjacent_raw_variables(
    bits: BitFunctionArena,
) -> tuple[
    CollatzOutputMorphism,
    tuple[FinitePort, ...],
    FactoredFunctionID,
    FactoredFunctionID,
]:
    morphism = CollatzOutputMorphism(bits)
    ports = tuple(FinitePort(PortVariable(0, i, "raw", 0), 64) for i in range(2))
    raw, adjacent = tuple(bits.variable(ports, port, DIGIT) for port in ports)
    return morphism, ports, raw, adjacent


def _assert_raw_pair(
    bits: BitFunctionArena,
    outgoing: FactoredFunctionID,
    raw: FactoredFunctionID,
    binding: dict[PortVariable, int],
    digit: int,
    carry: int,
) -> tuple[int, int]:
    out, value = divmod(3 * digit + carry, 64)
    assert bits.evaluate(outgoing, binding) == out
    assert bits.evaluate(raw, binding) == value
    return out, value
