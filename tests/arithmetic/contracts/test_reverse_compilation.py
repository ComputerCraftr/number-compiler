from __future__ import annotations

from array import array
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
    _load_base10_t2_kernel,
)
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.contracts.temporal_family import _issue_certificate
from number_compiler.hashlife.actions.lazy_compiler import (
    LazyCompiler,
    ProgramComposition,
)
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.compilation import (
    compile_reverse_pair_power,
    is_verified_decimal_pair_kernel,
)
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.reverse_pair_oracle import reference_successor


@pytest.mark.parametrize("exponent", [0, 1, 2, 3, 4, 17, 10**18])
def test_decimal_compilation_preserves_physical_exponent_and_verified_primitive(
    exponent: int,
) -> None:
    compiler = LazyCompiler(ResourceLedger())
    power = compile_reverse_pair_power(compiler, 10, exponent)
    assert power.exponent == exponent
    if not exponent:
        assert power.root is None and not compiler.nodes
        return
    assert power.root is not None and power.root.exponent == exponent
    assert power.operator_nodes == power.root.operator_nodes()
    assert power.syntax_depth == getattr(power.root, "depth", 1)
    assert power.compose_operations <= 2 * exponent.bit_length()
    assert power.operator_nodes <= 2 * exponent.bit_length()
    atoms = [node for node in compiler.nodes if type(node) is not ProgramComposition]
    # The verified T² table is a proof certificate, not a production temporal
    # leaf.  Binary powering retains one exact algebraic T primitive for every
    # positive exponent, including even powers.
    assert not any(is_verified_decimal_pair_kernel(atom) for atom in atoms)
    assert sum(type(atom) is BaseBlockEffect for atom in atoms) == 1


@pytest.mark.parametrize("base", [2, 3, 5, 11])
def test_other_radices_keep_the_exact_one_step_primitive(base: int) -> None:
    compiler = LazyCompiler(ResourceLedger())
    power = compile_reverse_pair_power(compiler, base, 9)
    assert power.exponent == 9
    atoms = [node for node in compiler.nodes if type(node) is not ProgramComposition]
    assert len(atoms) == 1 and type(atoms[0]) is BaseBlockEffect


@pytest.mark.parametrize("exponent", [1, 2, 3, 4, 5])
def test_compiled_pair_digits_match_scalar_reference(exponent: int) -> None:
    source = (7, 18, 7)
    expected: tuple[int, ...] = source
    for _ in range(exponent):
        expected = reference_successor(expected, 10)
    compiler = LazyCompiler(ResourceLedger())
    power = compile_reverse_pair_power(compiler, 10, exponent)
    assert power.root is not None
    app = HashLifeBlockIndex(power.root, source, logical_length=len(source) + exponent)
    output = tuple(
        app.direct_powered_point(position) for position in range(len(source) + exponent)
    )
    assert tuple(value for value in output if value != power.root.blank) == expected


def test_public_reverse_descriptor_excludes_t2_and_certifies_physical_steps() -> None:
    term = ReverseAddPoweredTerm(196, 18)
    assert term.pair_power is not None and term.pair_power.exponent == 17
    assert not any(
        is_verified_decimal_pair_kernel(node) for node in term._compiler.nodes
    )
    assert term.effect is not None
    certificate = _issue_certificate(term.effect, "reverse-add", 17)
    certificate.validate(term.effect)
    assert certificate.steps == term.effect.exponent == 17


def fake_kernel() -> FiniteBlockEffect:
    return FiniteBlockEffect(
        base=10,
        exponent=2,
        left_count=1,
        right_count=1,
        alphabet_size=20,
        initial_left=0,
        initial_right=0,
        left_transitions=array("H", [0] * 20),
        right_transitions=array("H", [0] * 20),
        outputs=bytes(range(20)),
        kernel_name="base10_t2_minimized_757x179",
        storage_bytes=451918,
        uncompressed_bytes=0,
        blank_left_tail=2,
        blank_right_tail=1,
        stable_blank_output=True,
    )


def test_same_name_and_forged_matching_digest_cannot_grant_arithmetic_certificate() -> (
    None
):
    compiler = LazyCompiler(ResourceLedger())
    fake = fake_kernel()
    assert not is_verified_decimal_pair_kernel(fake)
    # A matching hash is only an index hint: the exact definition must match.
    verified = _load_base10_t2_kernel()
    object.__setattr__(
        fake,
        "_semantic_identity",
        SemanticIdentity(verified.semantic_digest, ("different table",)),
    )
    assert not is_verified_decimal_pair_kernel(fake)
    effect = compiler.compose(fake, DigitNormalizeBlockEffect(10))
    with pytest.raises(ValueError, match="certified arithmetic"):
        _issue_certificate(effect, "reverse-add", 2)


def test_production_compilation_does_not_load_the_proof_artifact(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.contracts.block_kernel as module

    def refused() -> Never:
        raise RuntimeError("kernel digest mismatch")

    monkeypatch.setattr(module, "_load_base10_t2_kernel", refused)
    compiler = LazyCompiler(ResourceLedger())
    power = compile_reverse_pair_power(compiler, 10, 2)
    assert power.root is not None
    assert all(type(node) is not FiniteBlockEffect for node in compiler.nodes)
