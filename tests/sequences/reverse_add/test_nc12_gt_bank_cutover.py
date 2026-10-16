"""NC12 source-owned GT/LT/F5 bank resurrection and finite border certificate."""

from __future__ import annotations

from dataclasses import fields, replace
from typing import TypeVar

import pytest

from number_compiler.api.number_api import NumberCompiler, PoweredReverseAddTermPayload
from number_compiler.api.query_types import ReverseAddTermQuery
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.bank_width_clock import WidthMacro
from number_compiler.sequences.reverse_add.mixed_periodic_bank import (
    ControlledMixedBank,
    IncompleteMixedBorder,
    MixedFrame,
    MixedPeriodicCore,
    _controlled_bank_workspace,
)
from number_compiler.sequences.reverse_add.q19_border_control import (
    BoundaryControlNotAuthorized,
    CertifiedBorderGrowth,
)
from number_compiler.sequences.reverse_add.q19_controlled_gt_bank import (
    SourceGuardedGTBankAction,
    _finite_proved_action,
    conditional_alternating_first_growth,
)
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from number_compiler.sequences.reverse_add.q19_uniform_cone import (
    UniformConeNotAuthorized,
)
from number_compiler.sequences.reverse_add.source_workspace import (
    ReverseSourceImageWorkspace,
)
from number_compiler.sequences.reverse_add.temporal_bank_actions import (
    ConditionalEQGrowthExit,
    power_alternating_outputs,
    power_uniform_outputs,
)
from number_compiler.sequences.reverse_add.temporal_bulk_moore import (
    AlternatingCore,
    UniformCarryCell,
    alternating_moore_certificate,
    uniform_bulk_moore_certificate,
)
from tests.support.reverse_add_sources import periodic_reverse_add_source


def _rev(x: int) -> int:
    return int(str(x)[::-1])


def _pair(x: int, coordinate: int) -> int:
    word = str(x)
    return int(word[coordinate]) + int(word[-coordinate - 1])


def _trace(
    x: int,
    coordinate: int,
    depth: int,
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    growth: list[int] = []
    coeff = [_pair(x, coordinate)]
    for _ in range(depth):
        next_x = x + _rev(x)
        growth.append(int(len(str(next_x)) > len(str(x))))
        x = next_x
        coeff.append(_pair(x, coordinate))
    return tuple(growth), tuple(coeff)


_RecordT = TypeVar("_RecordT", CertifiedBorderGrowth, SourceGuardedGTBankAction)


def _resealed_copy(record: _RecordT, **changes: object) -> _RecordT:
    forged = object.__new__(type(record))
    for descriptor in fields(record):
        object.__setattr__(forged, descriptor.name, getattr(record, descriptor.name))
    for name, value in changes.items():
        object.__setattr__(forged, name, value)
    object.__setattr__(forged, "_binding", forged._snapshot())
    return forged


def test_nc10_temporal_banks_are_reusable_in_nc12() -> None:
    assert alternating_moore_certificate().quiet_future_states == 100
    assert alternating_moore_certificate().cycle_lengths == (1, 2, 6, 10, 30)
    assert len(uniform_bulk_moore_certificate().future_states) == 12
    q = power_uniform_outputs(UniformCarryCell(8, 0, 0), 10**18)
    assert q.steps == 10**18 and q.compiled_nodes < 15000
    assert q.at(10**18 - 1).f5[0] == q.at(10**18 - 1).coefficients[0] % 5
    a = power_alternating_outputs(AlternatingCore(0, 11), 10**18, quiet_guarded=True)
    assert a.steps == 10**18 and a.compiled_nodes < 15000
    # Even though it is algebraically powerable, 10^18 quiet *whole-source*
    # steps are universally impossible. The bank makes no such claim.
    assert not WidthMacro.from_bits((0,)).repeat(10**18).admitted()


def test_controlled_bank_reserves_before_allocating_and_releases_on_rejection() -> None:
    # The initial arena and first orbit row fit; a later orbit or Moore
    # reservation does not. This exercises cleanup after work already exists.
    ledger = ResourceLedger(max_cache_entries=30)
    workspace = ledger.register("controlled-bank-test-workspace", "bank_workspace")

    with (
        _controlled_bank_workspace(ledger, workspace) as reserve,
        pytest.raises(BlockContextBudgetExceeded),
    ):
        ControlledMixedBank(
            MixedPeriodicCore((5, 16)),
            (0, 0, 0, 0, 1),
            max_states=8,
            workspace_reserve=reserve,
        )

    assert ledger.entries == 0
    assert ledger.nodes == 0
    assert ledger.peak_entries == 26
    assert ledger.peak_nodes == 12
    ledger.mark_disposed(workspace)


def test_controlled_bank_reuses_each_orbit_transition_for_linking(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = 0
    advance = MixedPeriodicCore.advance

    def counted(
        self: MixedPeriodicCore, growth: int
    ) -> tuple[MixedPeriodicCore, MixedFrame]:
        nonlocal calls
        calls += 1
        return advance(self, growth)

    monkeypatch.setattr(MixedPeriodicCore, "advance", counted)
    bank = ControlledMixedBank(MixedPeriodicCore((5, 16)), (0, 1), max_states=8)
    assert calls == len(bank.states) * len(bank.pattern)


def test_finite_control_fallback_reserves_before_allocating_its_output_arena() -> None:
    ledger = ResourceLedger(max_nodes=0)
    workspace = ledger.register("finite-bank-test-workspace", "bank_workspace")

    with (
        _controlled_bank_workspace(ledger, workspace) as reserve,
        pytest.raises(BlockContextBudgetExceeded),
    ):
        _finite_proved_action((5, 16), (0, 0, 0, 0, 1), workspace_reserve=reserve)

    assert ledger.entries == 0
    assert ledger.nodes == 0
    assert ledger.peak_nodes == 0
    ledger.mark_disposed(workspace)


def test_width_control_dfa_all_entry_phases() -> None:
    assert WidthMacro.from_bits((0, 0, 0, 0, 1)).repeat(1000).admitted()
    assert not WidthMacro.from_bits((0, 0, 0, 0, 0)).admitted()
    assert not WidthMacro.from_bits((1, 1, 1, 1)).admitted()
    assert (
        not WidthMacro.from_bits((0, 0, 0, 0, 1))
        .repeat(2)
        .then(WidthMacro.from_bits((0, 0, 0, 0, 0)))
        .admitted()
    )
    a = WidthMacro.from_bits((0, 1, 1))
    b = WidthMacro.from_bits((0, 0, 1))
    assert a.then(b).transfer == WidthMacro.from_bits((0, 1, 1, 0, 0, 1)).transfer
    with pytest.raises(ValueError):
        WidthMacro.event(True)


@pytest.mark.parametrize(
    "pattern", ((5, 16), (7, 14), (0, 11), (2, 14), (8, 17), (5, 16, 2))
)
def test_source_certified_bank_predicts_actual_two_field_trajectory(
    pattern: tuple[int, ...],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    start = periodic_reverse_add_source(pattern, seed=9302 + sum(pattern))
    k = len(pattern)
    coord = 200 - 200 % k
    depth = 16
    bits, coeff = _trace(start, coord, depth)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(start, 10), base=10)
    try:
        cert = owner.certify_border_growth(owner.initial, steps=depth, window_digits=6)
        assert cert.growth_word == bits
        assert cert.physical_growth_certified is True

        def poison(*args: object, **kwargs: object) -> None:
            raise AssertionError("physical Q19 work is forbidden in this GT bank")

        monkeypatch.setattr(owner, "apply_pair_step", poison)
        monkeypatch.setattr(owner, "apply_punctured_pair_block", poison)
        action = owner.authorize_controlled_gt_bank(
            owner.initial,
            steps=depth,
            coordinate=coord,
            period_size=k,
            growth_control=cert,
        )
        assert action.control_certified and not action.full_integer_certified
        assert action.growth_count == sum(bits)
        assert tuple(action.at(t) for t in range(depth + 1)) == coeff
        for t in range(depth):
            frame = action.frame(t)
            assert frame.target[coord % k] == coeff[t + 1]
            assert frame.masks()["gt_high"][coord % k] == (15 <= coeff[t + 1] <= 18)
            assert frame.masks()["f5"][coord % k] == coeff[t + 1] % 5
            assert len(frame.incoming) == k
            assert len(action.conditional_next_quiet_borrow(t)) == 2
        assert ledger.counters.get("reverse_q19_primitive_pair_applications", 0) == 0
        assert ledger.counters.get("reverse_q19_punctured_t4_applications", 0) == 0
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_public_digit_demand_consumes_certified_bank_without_q19_discovery(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = periodic_reverse_add_source((5, 16), seed=9323)
    coordinate = 200
    steps = 16
    value = source
    for _ in range(steps):
        value += _rev(value)
    expected = digits_lsd(value, 10)[coordinate]

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("certified pointed demand reopened Q19 discovery")

    monkeypatch.setattr(ReversePairQ19OutputOwner, "apply_pair_step", forbidden)
    monkeypatch.setattr(
        ReversePairQ19OutputOwner, "apply_punctured_pair_block", forbidden
    )
    compiler = NumberCompiler()
    query = ReverseAddTermQuery(steps, seed=source, base=10)
    term = None
    try:
        assert compiler.project_digit(query, coordinate) == expected
        projected = compiler.project(query)
        assert isinstance(projected.payload, PoweredReverseAddTermPayload)
        term = projected.payload.term
        workspace = term._workspace
        assert workspace is not None
        assert workspace._image is None
        counters = term._ledger.counters
        assert counters["reverse_q19_pointed_gt_bank_applied_actions"] == 1
        assert counters["reverse_q19_border_control_state_visits"] > 0
        assert counters["reverse_q19_border_control_edge_transitions"] > 0
        assert counters["reverse_q19_border_control_source_pair_inspections"] > 0
        assert counters.get("reverse_q19_primitive_pair_applications", 0) == 0
        assert counters.get("reverse_q19_punctured_t4_applications", 0) == 0
        workspace.dispose()
    finally:
        if term is not None and term._workspace is not None:
            term._workspace.dispose()


def test_same_pointed_request_reuses_ledger_owned_gt_bank(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = periodic_reverse_add_source((5, 16), seed=9323)
    coordinate = 200
    steps = 16
    endpoint = source
    for _ in range(steps):
        endpoint += _rev(endpoint)
    expected = digits_lsd(endpoint, 10)[coordinate]
    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, source, steps, base=10)
    try:
        assert workspace.digit(coordinate) == expected
        before = dict(ledger.counters)
        owner = workspace.adapter._q19_owner
        assert owner is not None

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("warm pointed hit rebuilt its source proof or action")

        monkeypatch.setattr(owner, "certify_border_growth", forbidden)
        monkeypatch.setattr(owner, "authorize_controlled_gt_bank", forbidden)
        assert workspace.digit(coordinate) == expected
        assert ledger.counters["reverse_q19_pointed_gt_bank_cache_hits"] == 1
        assert (
            ledger.counters["reverse_q19_border_control_attempts"]
            == before["reverse_q19_border_control_attempts"]
        )
        assert (
            ledger.counters["reverse_q19_border_control_state_visits"]
            == before["reverse_q19_border_control_state_visits"]
        )
        assert (
            ledger.counters["reverse_q19_pointed_gt_bank_applied_actions"]
            == before["reverse_q19_pointed_gt_bank_applied_actions"]
        )
        assert workspace._image is None
    finally:
        workspace.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_border_79_to_103_and_119_to_138_exact_mixed_return() -> None:
    for source, k, n, expected in (
        (16474800379447118011108106559729985745, 4, 24, "010010101010010101010010"),
        (
            178208907106857199148923887279922093100275751161090187,
            4,
            19,
            "0101010100101010010",
        ),
    ):
        ledger = ResourceLedger()
        owner = ReversePairQ19OutputOwner(ledger, digits_lsd(source, 10), base=10)
        try:
            result = owner.certify_border_growth(
                owner.initial, steps=n, window_digits=k
            )
            assert (
                owner.certify_border_growth(owner.initial, steps=n, window_digits=k)
                is result
            )
            assert "".join(map(str, result.growth_word)) == expected
            x = source
            for bit in result.growth_word:
                y = x + _rev(x)
                assert bit == int(len(str(y)) > len(str(x)))
                x = y
            with pytest.raises(BoundaryControlNotAuthorized):
                owner.certify_border_growth(owner.initial, steps=n + 1, window_digits=k)
        finally:
            owner.dispose()
            assert ledger.entries == ledger.nodes == 0


def test_owner_registry_rejects_resealed_certificates_and_actions() -> None:
    source = periodic_reverse_add_source((5, 16), seed=9323)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(source, 10), base=10)
    try:
        certificate = owner.certify_border_growth(
            owner.initial, steps=16, window_digits=6
        )
        changed_word = (1 - certificate.growth_word[0],) + certificate.growth_word[1:]
        forged_certificate = _resealed_copy(certificate, growth_word=changed_word)
        with pytest.raises(ValueError, match="retained by this Q19 owner"):
            forged_certificate.validate(owner, owner.initial)
        with pytest.raises(ValueError, match="retained by this Q19 owner"):
            owner.authorize_controlled_gt_bank(
                owner.initial,
                steps=16,
                coordinate=200,
                period_size=2,
                growth_control=forged_certificate,
            )
        original_word = certificate.growth_word
        object.__setattr__(certificate, "growth_word", changed_word)
        object.__setattr__(certificate, "_binding", certificate._snapshot())
        with pytest.raises(ValueError, match="retained by this Q19 owner"):
            certificate.validate(owner, owner.initial)
        object.__setattr__(certificate, "growth_word", original_word)
        object.__setattr__(certificate, "_binding", certificate._snapshot())
        certificate.validate(owner, owner.initial)

        action = owner.authorize_controlled_gt_bank(
            owner.initial,
            steps=16,
            coordinate=200,
            period_size=2,
            growth_control=certificate,
        )
        forged_action = _resealed_copy(action, coordinate=action.coordinate + 1)
        with pytest.raises(ValueError, match="retained by this Q19 owner"):
            forged_action._validate()
        original_coordinate = action.coordinate
        object.__setattr__(action, "coordinate", original_coordinate + 1)
        object.__setattr__(action, "_binding", action._snapshot())
        with pytest.raises(ValueError, match="retained by this Q19 owner"):
            action._validate()
        object.__setattr__(action, "coordinate", original_coordinate)
        object.__setattr__(action, "_binding", action._snapshot())
        action._validate()
        original_target = action.action.target
        object.__setattr__(action.action, "target", replace(original_target))
        object.__setattr__(action, "_binding", action._snapshot())
        with pytest.raises(ValueError, match="not retained by this Q19 owner"):
            action._validate()
        object.__setattr__(action.action, "target", original_target)
        object.__setattr__(action, "_binding", action._snapshot())
        action._validate()
        frame = action.frame(0)
        with pytest.raises((AttributeError, TypeError)):
            object.__setattr__(frame, "growth", 1 - frame.growth)
        emit = next(node for node in action.action.arena.nodes if node.tag == "emit")
        with pytest.raises((AttributeError, TypeError)):
            object.__setattr__(emit, "steps", emit.steps + 1)

        target = action.action.target
        target_coefficients = target.coefficients
        changed_coefficients = (target_coefficients[0] + 1,) + target_coefficients[1:]
        object.__setattr__(target, "coefficients", changed_coefficients)
        with pytest.raises(ValueError, match="altered"):
            action.frame(0)
        object.__setattr__(target, "coefficients", target_coefficients)
        assert action.frame(0).target
        audit = ledger.audit_payload_contracts()
        assert audit.invalid == frozenset()
        assert audit.owns_root("reverse_add", owner, ledger=ledger)
        owner.dispose()
        with pytest.raises(ValueError, match="disposed Q19 pair output owner"):
            action._validate()
        assert ledger.entries == ledger.nodes == 0
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_conditional_input_never_authenticates_actual_border() -> None:
    source = periodic_reverse_add_source((5, 16), seed=8320)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(source, 10), base=10)
    try:
        conditioned = owner.authorize_controlled_gt_bank(
            owner.initial,
            steps=18,
            coordinate=200,
            period_size=2,
            growth_control=(0, 1),
        )
        assert conditioned.control_certified is False
        assert conditioned.full_integer_certified is False
        assert conditioned.output_nodes > 0
        with pytest.raises(ValueError):
            replace(conditioned, control_certified=True)
        with pytest.raises(TypeError):
            conditioned.action.arena.ids[("forged",)] = 0
        root = conditioned.action.output_root
        object.__setattr__(conditioned.action, "output_root", 0)
        with pytest.raises(ValueError):
            conditioned.at(12)
        object.__setattr__(conditioned.action, "output_root", root)
        assert conditioned.at(12) in range(19)
        with pytest.raises(ValueError):
            SourceGuardedGTBankAction(
                conditioned.owner,
                conditioned.source,
                conditioned.coordinate,
                conditioned.steps,
                conditioned.period,
                conditioned.growth_control,
                conditioned.halo,
                conditioned.action,
            )
        foreign_ledger = ResourceLedger()
        foreign = ReversePairQ19OutputOwner(
            foreign_ledger, digits_lsd(196, 10), base=10
        )
        try:
            with pytest.raises(ValueError):
                conditioned.square(foreign)
        finally:
            foreign.dispose()
            assert foreign_ledger.entries == foreign_ledger.nodes == 0
        with pytest.raises(IncompleteMixedBorder):
            owner.authorize_controlled_gt_bank(
                owner.initial,
                steps=20,
                coordinate=200,
                period_size=2,
                growth_control=(0, 0, 0, 0, 0),
            )
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_all_eq_fourway_exit_stays_punctured() -> None:
    for source in ((0, 18), (2, 16), (4, 14)):
        result = conditional_alternating_first_growth(
            AlternatingCore(*source), quiet_steps=0
        )
        assert isinstance(result, ConditionalEQGrowthExit)
        assert result.coefficient == 9
        assert dict(result.alternatives) == {
            (0, 0): 18,
            (0, 1): 9,
            (1, 0): 9,
            (1, 1): 0,
        }
    nongrowth = conditional_alternating_first_growth(
        AlternatingCore(0, 11), quiet_steps=0
    )
    assert isinstance(nongrowth, UniformCarryCell)
    assert nongrowth.coefficient == 2
    with pytest.raises(IncompleteMixedBorder):
        conditional_alternating_first_growth(AlternatingCore(0, 18), quiet_steps=5)


def test_border_control_refuses_ambiguity_forgery_and_future_upsquare() -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    try:
        cert = owner.certify_border_growth(owner.initial, steps=5, window_digits=1)
        assert cert.growth_word == (0, 1, 0, 1, 0)
        with pytest.raises(BoundaryControlNotAuthorized):
            owner.certify_border_growth(owner.initial, steps=6, window_digits=1)
        with pytest.raises(ValueError):
            replace(cert, growth_word=(1, 1, 1, 1, 1))
        with pytest.raises(ValueError):
            CertifiedBorderGrowth(owner, owner.initial, (0,), 1, 1)
        with pytest.raises(UniformConeNotAuthorized):
            owner.authorize_controlled_gt_bank(
                owner.initial,
                steps=5,
                coordinate=1,
                period_size=1,
                growth_control=cert,
            )
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0
    with pytest.raises(ValueError):
        cert.validate(owner, owner.initial)
