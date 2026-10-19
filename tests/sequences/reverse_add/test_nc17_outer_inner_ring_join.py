"""NC17 reverse/add source-bound cyclotomic/exterior/carry/center integration."""

from __future__ import annotations

from unittest.mock import patch

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from number_compiler.sequences.reverse_add.temporal_depth_transfer_matrix import (
    conditional_depth_window,
    pair_index,
)
from number_compiler.sequences.reverse_add.temporal_inward_constraints import (
    InconsistentReverseConstraints,
    ReverseInwardConstraints,
)


def _successor(x: int) -> int:
    return x + int(str(x)[::-1])


def _source196(n: int) -> int:
    x = 196
    for _ in range(n):
        x = _successor(x)
    return x


def _center(value: int) -> int:
    s = str(value)
    return int(s[(len(s) - 1) // 2 : (len(s) + 2) // 2])


@pytest.mark.parametrize("value", [12345, 1382, 1001, 1991])
def test_exterior_center_fiber_matches_literal_source(value: int) -> None:
    s = str(value)
    width = len(s)
    system = ReverseInwardConstraints((width,))
    system.constrain_digit(0, 0, int(s[0]))
    system.constrain_digit(0, width - 1, int(s[-1]))
    k = 1 if width & 1 else 2
    start = (width - k) // 2
    outside = int(s[:start] + "0" * k + s[start + k :])
    system.constrain_exterior_residue99(0, outside % 99)
    system.constrain_residue(0, 99, value % 99)
    system.propagate()
    assert _center(value) in system.center_domain(0)


def test_middle_00_99_remain_distinct_until_f5_pair_constraint() -> None:
    system = ReverseInwardConstraints((4,))
    system.constrain_prefix(0, "1")
    system.constrain_suffix(0, "1")
    system.constrain_exterior_residue99(0, 1001 % 99)
    system.constrain_residue(0, 99, 1001 % 99)
    system.propagate()
    assert system.center_domain(0) == (0, 99)
    system.constrain_pair(0, 1, 0)
    system.propagate()
    assert system.center_domain(0) == (0,)


def test_incorrect_exact_exterior_or_global_residue_refused() -> None:
    system = ReverseInwardConstraints((4,))
    system.constrain_prefix(0, "1")
    system.constrain_suffix(0, "2")
    system.constrain_exterior_residue99(0, 1002 % 99)
    system.constrain_residue(0, 99, 1382 % 99)
    system.constrain_pair(0, 1, 3 + 8)
    system.propagate()
    # The ordered global minus exterior residue rejects the reflected 83,
    # even though both 38 and 83 have Q19 center pair sum 11.
    assert system.center_domain(0) == (38,)
    with pytest.raises(InconsistentReverseConstraints):
        system.constrain_exterior_residue99(0, (1002 + 1) % 99)


def test_source_issued_ring_joins_cyclotomic_and_middle_carry() -> None:
    x = _source196(79)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(x, 10), base=10)
    try:
        ring = owner.authorize_temporal_ring_bank(
            owner.initial,
            steps=9,
            window_digits=3,
            positions=(0, 1, 2),
            source_pair_prefix=3,
        )
        values = [x]
        for _ in range(9):
            values.append(_successor(values[-1]))
        assert len(ring.carry_wire_phases) == 9
        assert ring.global_residues99 == tuple(v % 99 for v in values)
        assert ring.global_residues198 == tuple(v % 198 for v in values)
        assert all(
            _center(v) in d for v, d in zip(values, ring.center_domains, strict=True)
        )
        assert any(len(phases) > 1 for phases in ring.carry_wire_phases)
        word = ring.conditional_carry_word()
        assert not word.conditional_power(10**14).physical_repeat_certified
        # The finite 100-state consumer selects a positive border width. Its
        # domains are projections, so it must label endpoints as an
        # overapproximation while retaining the literal source path.
        matrix_word = ring.conditional_carry_word(border_digits=1)
        matrix = conditional_depth_window(matrix_word, position=1, steps=4)
        packet = matrix.to_packet()
        assert packet["relation_semantics"] == "projected_bank_domain_overapproximation"
        assert packet["source_root_assignment_joined"] is False
        assert matrix.affine_action.boolean == matrix.action
        assert not hasattr(matrix.affine_action, "power")
        affine_rows = packet["affine_transition_rows"]
        assert isinstance(affine_rows, list)
        assert len(affine_rows) == 100
        affine_semantics = packet["affine_relation_semantics"]
        assert isinstance(affine_semantics, str)
        assert "offsets correlated by pair state" in affine_semantics
        first_pair = (
            digits_lsd(values[0], 10)[1],
            digits_lsd(values[0], 10)[-2],
        )
        path_offsets: dict[tuple[int, int], set[int]] = {first_pair: {0}}
        for phase_matrix in matrix.phase_matrices:
            next_offsets: dict[tuple[int, int], set[int]] = {}
            for source_pair, offsets in path_offsets.items():
                row = phase_matrix.rows[pair_index(source_pair)]
                for target_index in range(100):
                    if not row & (1 << target_index):
                        continue
                    target_pair = divmod(target_index, 10)
                    edge_offset = (sum(target_pair) - 2 * sum(source_pair)) % 5
                    target_offsets = next_offsets.setdefault(target_pair, set())
                    target_offsets.update(
                        (2 * offset + edge_offset) % 5 for offset in offsets
                    )
            path_offsets = next_offsets
        expected_affine_endpoints = tuple(
            (pair, tuple(sorted(offsets)))
            for pair, offsets in sorted(path_offsets.items())
        )
        assert matrix.affine_action.endpoints(first_pair) == expected_affine_endpoints
        original_action_rows = matrix.action._relation.rows
        object.__setattr__(
            matrix.action._relation,
            "rows",
            (True, *original_action_rows[1:]),
        )
        try:
            with pytest.raises(ValueError, match="contents changed"):
                matrix.to_packet()
        finally:
            object.__setattr__(matrix.action._relation, "rows", original_action_rows)
        for tick in range(4):
            source_digits = digits_lsd(values[tick], 10)
            target_digits = digits_lsd(values[tick + 1], 10)
            source_pair = (source_digits[1], source_digits[-2])
            target_pair = (target_digits[1], target_digits[-2])
            target_bit = 1 << pair_index(target_pair)
            assert (
                matrix.phase_matrices[tick].rows[pair_index(source_pair)] & target_bit
            )
        correlated_phases = ring.diagnostic()["correlated_carry_phases"]
        assert isinstance(correlated_phases, int)
        assert correlated_phases >= 9
        assert not ring.temporal_repeat_certified
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_mod99_mod198_alias_does_not_force_center_period() -> None:
    x = _source196(79)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(x, 10), base=10)
    try:
        ring = owner.authorize_temporal_ring_bank(
            owner.initial,
            steps=9,
            window_digits=3,
            positions=(0,),
            include_source_digits=True,
        )
        # At physical times 80 and 86 the global residues agree, even
        # modulo 198, while the actual centers are 22 and 7.
        assert ring.global_residues99[1] == ring.global_residues99[7]
        assert ring.global_residues198[1] == ring.global_residues198[7]
        assert not set(ring.center_domains[1]).intersection(ring.center_domains[7])
        assert ring.conditional_joint_center_period(6) == "contradicted"
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


@pytest.mark.parametrize("width", [129, 130])
def test_large_root_mod99_slp_join_without_reading_all_source_digits(
    width: int,
) -> None:
    x = 10 ** (width - 1) + 7
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(x, 10), base=10)
    try:
        with patch.object(
            ReversePairQ19OutputOwner,
            "apply_pair_step",
            side_effect=AssertionError("unexpected physical Q19 step"),
        ):
            cert = owner.certify_border_growth(owner.initial, steps=2, window_digits=1)
            system = cert.inward_temporal_constraints(max_modular_digits=128)
            system.propagate()
        actual = (x, _successor(x), _successor(_successor(x)))
        if width & 1:
            assert system.global_residue99(0) == actual[0] % 99
        else:
            assert system.global_residue99(0) is None
        assert tuple(system.global_residue99(i) for i in (1, 2)) == (
            actual[1] % 99,
            actual[2] % 99,
        )
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_later_q19_root_residue_is_the_actual_later_integer() -> None:
    for seed in (196, 1000, 10089):
        ledger = ResourceLedger()
        owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
        try:
            source = owner.apply_pair_step(owner.initial)
            # The initial Q19 root already issues seed+reverse(seed). One
            # apply_pair_step advances the issued output to generation two.
            actual = _successor(_successor(seed))
            cert = owner.certify_border_growth(source, steps=2, window_digits=1)
            system = cert.inward_temporal_constraints()
            system.propagate()
            assert system.global_residue99(0) == actual % 99
            assert system.global_residue198(0) == actual % 198
        finally:
            owner.dispose()
            assert ledger.entries == ledger.nodes == 0


def test_public_cli_exposes_joint_source_bound_ports_without_value_render() -> None:
    import json
    import os
    import subprocess
    import sys

    proc = subprocess.run(
        [
            sys.executable,
            "-m",
            "number_compiler",
            "reverse-add",
            "--seed",
            "196",
            "--nth",
            "2",
            "--no-value",
            "--info",
            "temporal.open-ring",
            "--spatial-pair-bank-position",
            "0",
            "--spatial-bank-morphism-count",
            "1",
            "--format",
            "json",
        ],
        check=True,
        capture_output=True,
        text=True,
        env={**os.environ, "PYTHONPATH": "src"},
    )
    packet = json.loads(proc.stdout)["info"]["temporal.open-ring"]
    joint = packet["joint_cyclotomic_center"]
    assert joint["mod99"] == [97, 95, 91]
    assert joint["mod198"] == [196, 95, 91]
    assert joint["center_domains"] == [[9], [8], [67]]
    assert len(joint["correlated_carry_phases"]) == 2
    assert not joint["physical_repeat_certified"]
    assert not packet["temporal_repeat_certified"]
