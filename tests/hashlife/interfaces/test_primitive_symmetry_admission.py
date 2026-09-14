"""Immutable symmetry certificates are bound at primitive admission."""

from __future__ import annotations

from array import array

import pytest

from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.hashlife.interfaces.primitive_behavior import LocalSymmetryWitness
from number_compiler.hashlife.tiles.tiles import TileArena
from number_compiler.resources.ledger import ResourceLedger


def _symmetric_effect() -> FiniteBlockEffect:
    return FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=1,
        right_count=1,
        alphabet_size=2,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", (0, 0)),
        right_transitions=array("I", (0, 0)),
        outputs=bytes((0, 1)),
        kernel_name="symmetric-admission",
        storage_bytes=10,
        uncompressed_bytes=10,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
        blank=1,
    )


def _witnesses() -> tuple[LocalSymmetryWitness, LocalSymmetryWitness]:
    identity = LocalSymmetryWitness(
        ActionTransform.IDENTITY,
        (0, 1),
        (0,),
        (0,),
        (0, 1),
    )
    mirror = LocalSymmetryWitness(
        ActionTransform.MIRROR,
        (0, 1),
        (0,),
        (0,),
        (0, 1),
    )
    return identity, mirror


def test_first_admission_freezes_complete_mirror_certificate() -> None:
    arena = DiamondKernelArena(ResourceLedger())
    handle = arena.intern(_symmetric_effect(), symmetry_witnesses=_witnesses())
    certificate = arena.local_symmetry(handle)
    assert certificate.transforms == (
        ActionTransform.IDENTITY,
        ActionTransform.MIRROR,
    )
    assert arena.intern(_symmetric_effect()) == handle
    assert (
        arena.intern(
            _symmetric_effect(),
            symmetry_witnesses=_witnesses(),
        )
        == handle
    )


def test_tile_adapter_exposes_only_the_admitted_complete_subgroup() -> None:
    ledger = ResourceLedger()
    kernels = DiamondKernelArena(ledger)
    adapter = PrimitiveTileKernelAdapter(
        TileArena(ledger),
        kernels,
        DiamondQuotientArena(SemanticFunctionArena(ledger)),
    )
    action = adapter.admit(
        _symmetric_effect(),
        symmetry_witnesses=_witnesses(),
    )
    certificate = adapter.local_symmetry(action)
    assert certificate.transforms == (
        ActionTransform.IDENTITY,
        ActionTransform.MIRROR,
    )
    with pytest.raises(ValueError, match="unsupported D4"):
        certificate.require(ActionTransform(4))


def test_late_symmetry_upgrade_cannot_change_published_kernel_semantics() -> None:
    arena = DiamondKernelArena(ResourceLedger())
    handle = arena.intern(_symmetric_effect())
    assert arena.local_symmetry(handle).transforms == (ActionTransform.IDENTITY,)
    before = arena.ledger.entries, arena.ledger.nodes
    with pytest.raises(ValueError, match="another symmetry certificate"):
        arena.intern(_symmetric_effect(), symmetry_witnesses=_witnesses())
    assert (arena.ledger.entries, arena.ledger.nodes) == before


def test_invalid_symmetry_rejects_before_primitive_publication() -> None:
    arena = DiamondKernelArena(ResourceLedger())
    before = arena.ledger.entries, arena.ledger.nodes
    identity, mirror = _witnesses()
    forged = LocalSymmetryWitness(
        mirror.transform,
        mirror.symbol_map,
        mirror.left_map,
        mirror.right_map,
        (1, 0),
    )
    with pytest.raises(ValueError, match="blank/activity"):
        arena.intern(
            _symmetric_effect(),
            symmetry_witnesses=(identity, forged),
        )
    assert (arena.ledger.entries, arena.ledger.nodes) == before
