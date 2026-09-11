"""Original fixed2/3-state kernel for independent codec tests."""

from __future__ import annotations

from array import array
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


def tiny() -> tuple[DiamondRuntime, ActionProgramID]:
    effect = FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=2,
        right_count=3,
        alphabet_size=4,
        initial_left=0,
        initial_right=0,
        left_transitions=array("H", (q for q in range(2) for _ in range(4))),
        right_transitions=array("H", (q for q in range(3) for _ in range(4))),
        outputs=bytes(s for _ in range(2) for s in range(4) for _ in range(3)),
        kernel_name="codec-test",
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
    )
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    atom = compiler.atom(effect)
    geometry = SourceGeometry(ledger, ExactSource((1,), 2, "reverse", 3, 1))
    geometry.span((1,), 3, 1)
    runtime = DiamondRuntime(compiler, geometry)
    action = runtime.actions.intern(atom)
    runtime.kernel(action)
    return runtime, action
