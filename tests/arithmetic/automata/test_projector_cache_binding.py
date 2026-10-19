from __future__ import annotations

import pytest

from number_compiler.arithmetic.automata.slp import BimachineSLPProjector, SLPArena
from number_compiler.arithmetic.automata.transducer import (
    build_pair_step_bimachine,
    encode_pair_half,
)
from number_compiler.arithmetic.functions.residual import minimize_bimachine


def test_projector_cache_binding_rejects_a_populated_public_cache() -> None:
    machine = minimize_bimachine(
        build_pair_step_bimachine(10), cache_outputs=False
    ).machine
    arena = SLPArena()
    root = arena.word(encode_pair_half(0, (1, 2, 3), 10))
    projector = BimachineSLPProjector(machine, arena)

    projector.forward(root, machine.left.start)

    with pytest.raises(ValueError, match="already in use"):
        projector.bind_cache_stores(
            forward={},
            reverse={},
            block={},
            forward_power={},
            reverse_power={},
        )
