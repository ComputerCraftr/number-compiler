from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from devtools.proofs.special_source_program import (
    FoldedSupportInstruction,
    FoldedSupportProgram,
    SpecialSourceCertificateCandidate,
)
from number_compiler.sequences.power_numbers.frobenius_chunk import (
    SpecialFrobeniusChunkSpec,
)

if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.frobenius_chunk import (
        SpecialFrobeniusChunkSpec,
    )


def _f5_spec() -> SpecialFrobeniusChunkSpec:
    return SpecialFrobeniusChunkSpec("fermat", 5, 2, 9, 6, 33)


def test_folded_support_program_is_explicit_dag_without_deferred_power() -> None:
    program = FoldedSupportProgram(
        (
            FoldedSupportInstruction("atom", "baseline_v2"),
            FoldedSupportInstruction("atom", "trace_seed"),
            FoldedSupportInstruction("sub", 0, 1),
        )
    )
    assert program.node_count == 3
    assert "pow" not in {ins.op for ins in program.instructions}
    evaluation = program.evaluate(_f5_spec())
    assert evaluation.value == 1
    assert evaluation.support_gcd == 1
    assert evaluation.ring_additions == 1
    assert evaluation.ring_multiplications == 0
    assert evaluation.gcd_operations == 0


def test_folded_support_program_rejects_forward_reference_and_unknown_atom() -> None:
    with pytest.raises(ValueError):
        FoldedSupportProgram((FoldedSupportInstruction("add", 0, 0),))
    with pytest.raises(ValueError):
        FoldedSupportInstruction("atom", "hidden_factor")
    with pytest.raises(ValueError):
        FoldedSupportInstruction("pow", 0)


def test_candidate_certificate_never_claims_its_empirical_program_is_proved() -> None:
    zero = FoldedSupportProgram.atom("zero")
    candidate = SpecialSourceCertificateCandidate.evaluate(_f5_spec(), zero)
    assert candidate.support_gcd == (1 << 32) + 1
    assert candidate.semantic_source_code == (1 << 5) - 1
    assert not candidate.theorem_proved
