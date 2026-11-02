"""Source-bound Collatz temporal quotient by maximal parity runs.

The normalized map uses ``H0(x)=x/2`` and ``H1(x)=(3*x+1)/2``. Exact
2-adic valuations select maximal zero and one runs, which are applied with
closed affine powers. Mixed wide sources use an accounted finite D8
source-section transducer; they do not construct a global parity itinerary or
physical branch tree. The pinned ``1 -> 4 -> 2 -> 1`` cycle is source-bound
and powered. Optional F5 views remain observations, never branch authority;
their root-fiber algebra does not replace exact source authentication.
"""

from __future__ import annotations

from contextlib import ExitStack

from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.boundary_templates import (
    BoundaryActionTemplateMemo,
)
from number_compiler.sequences.collatz.joint_temporal_action import (
    CollatzJointTemporalBuilder,
)
from number_compiler.sequences.collatz.temporal_f5_observer import (
    F5_AFFINE_ALPHABET,
    HENSEL_ONE_F5,
    HENSEL_ZERO_F5,
    ODD_HALF_F5,
    CollatzAnonymousF5Fiber,
    CollatzF5AffineAction,
    CollatzPoweredRootVietaProgram,
    CollatzRootFiberCertificate,
    root_fiber_certificate,
)
from number_compiler.sequences.collatz.temporal_run_executor import (
    execute_collatz_temporal_run,
)
from number_compiler.sequences.collatz.temporal_run_result import (
    CollatzTemporalRunQuotient,
)


def compile_collatz_temporal_run_quotient(
    seed: int,
    physical_ticks: int,
    *,
    ledger: ResourceLedger,
    include_f5: bool = False,
    shared_cache: bool = False,
    include_width_spine: bool = False,
    include_joint_cocycle: bool = False,
    include_innovation_tape: bool = False,
    require_mixed_prefix: bool = False,
    innovation_modulus: int | None = None,
    prefer_source_closed_d8: bool = False,
) -> CollatzTemporalRunQuotient:
    """Compile the exact source-bound action without a parity itinerary.

    Work uses maximal runs, finite D8 sections and the powered known cycle.
    It retains no physical successor leaf or global parity word. Run count can
    grow with requested ticks; arithmetic cost depends on operand widths.
    """
    if type(seed) is not int or seed <= 0:
        raise ValueError("Collatz temporal quotient requires a positive seed")
    if type(physical_ticks) is not int or physical_ticks < 0:
        raise ValueError("Collatz temporal quotient requires nonnegative ticks")
    if type(ledger) is not ResourceLedger:
        raise TypeError("Collatz temporal quotient requires its resource ledger")

    if type(include_f5) is not bool:
        raise TypeError("F5 projection selection must be Boolean")
    if type(shared_cache) is not bool:
        raise TypeError("shared cache flag must be Boolean")
    if type(include_width_spine) is not bool:
        raise TypeError("width-spine demand must be Boolean")
    if type(include_joint_cocycle) is not bool:
        raise TypeError("joint-cocycle demand must be Boolean")
    if type(include_innovation_tape) is not bool:
        raise TypeError("innovation-tape demand must be Boolean")
    if type(require_mixed_prefix) is not bool:
        raise TypeError("mixed-prefix routing mode must be Boolean")
    if type(prefer_source_closed_d8) is not bool:
        raise TypeError("D8 successor admission mode must be Boolean")
    if innovation_modulus is not None and (
        type(innovation_modulus) is not int
        or innovation_modulus < 3
        or innovation_modulus > 4096
        or innovation_modulus % 2 == 0
        or not include_innovation_tape
    ):
        raise ValueError("complete innovation tape needs a demanded odd modulus")
    from number_compiler.sequences.collatz.innovation_input_tape import (
        ParityProgramBuilder,
    )
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
    )

    with ExitStack() as stack:
        scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
        stack.enter_context(scratch.scope())
        macros = (
            CollatzDyadicMacros(ledger, shared_cache=True)
            if shared_cache and seed.bit_length() >= 64
            else None
        )
        if macros is not None:
            stack.enter_context(macros)
        joint_builder = CollatzJointTemporalBuilder(
            ledger,
            scratch,
            seed,
            requested=include_joint_cocycle,
            shared_cache=shared_cache,
        )
        stack.enter_context(joint_builder)
        parity_builder = (
            ParityProgramBuilder(seed, ledger)
            if innovation_modulus is not None
            else None
        )
        if parity_builder is not None:
            stack.enter_context(parity_builder)
        boundary_templates = stack.enter_context(BoundaryActionTemplateMemo(ledger))
        return execute_collatz_temporal_run(
            seed,
            physical_ticks,
            ledger=ledger,
            include_f5=include_f5,
            include_width_spine=include_width_spine,
            include_joint_cocycle=include_joint_cocycle,
            include_innovation_tape=include_innovation_tape,
            require_mixed_prefix=require_mixed_prefix,
            innovation_modulus=innovation_modulus,
            prefer_source_closed_d8=prefer_source_closed_d8,
            macros=macros,
            scratch=scratch,
            joint_builder=joint_builder,
            parity_builder=parity_builder,
            boundary_templates=boundary_templates,
        )


__all__ = [
    "F5_AFFINE_ALPHABET",
    "HENSEL_ONE_F5",
    "HENSEL_ZERO_F5",
    "ODD_HALF_F5",
    "CollatzAnonymousF5Fiber",
    "CollatzF5AffineAction",
    "CollatzPoweredRootVietaProgram",
    "CollatzRootFiberCertificate",
    "CollatzTemporalRunQuotient",
    "compile_collatz_temporal_run_quotient",
    "root_fiber_certificate",
]
