"""Production construction of the symbolic physical-Collatz action ``C**n``."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.adic_morphism import PadicAffineMorphism
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.field_action import (
    CollatzActionGeometry,
    CollatzCharacterAction,
    CollatzCocyclePrograms,
    CollatzDefectArena,
    CollatzFieldAction,
    CollatzFieldActionArena,
    CollatzFieldActionID,
)
from number_compiler.sequences.collatz.runtime_programs import (
    CollatzRuntimeProgramArena,
)


@dataclass(frozen=True, slots=True)
class CollatzRuntimeActionBundle:
    """All index-owned algebra required by a source-bound Collatz provider."""

    programs: CollatzRuntimeProgramArena
    defects: CollatzDefectArena
    actions: CollatzFieldActionArena
    primitive: CollatzFieldActionID
    powered: CollatzFieldActionID


def build_collatz_runtime_action(
    steps: int,
    ledger: ResourceLedger,
    *,
    geometry: CollatzActionGeometry = CollatzActionGeometry(),
) -> CollatzRuntimeActionBundle:
    """Build ``C**steps`` with logarithmic binary component composition.

    This compiler does not import the verified C4 proof table.  The one-class
    residual is the neutral local defect after the executable carry/root/output
    components have been kept separately; it makes no global trajectory-state
    quotient claim.
    """
    if type(steps) is not int:
        raise TypeError("physical Collatz steps must be an exact integer")
    if steps < 0:
        raise ValueError("physical Collatz steps must be nonnegative")
    if type(ledger) is not ResourceLedger:
        raise TypeError("Collatz runtime action requires an index ledger")
    if type(geometry) is not CollatzActionGeometry:
        raise TypeError("Collatz runtime action requires normalized geometry")
    programs = CollatzRuntimeProgramArena(ledger)
    defects = CollatzDefectArena(((0,),), identity=0, ledger=ledger)
    actions = CollatzFieldActionArena(
        programs,
        defects,
        padic_precision=32,
        ledger=ledger,
    )
    primitive = actions.intern(
        CollatzFieldAction(
            # Branch-dependent character/innovation data remains in the executable
            # root/affine programs.  Publishing the odd branch's ``3*x+1`` affine
            # record here would incorrectly specialize the source-independent
            # physical action before its parity port is bound.
            CollatzCharacterAction(0, ()),
            programs.primitive("root"),
            programs.primitive("affine"),
            PadicAffineMorphism(3, 32, 1, 0, 0).radial_quotient,
            defects.identity,
            CollatzCocyclePrograms(
                programs.primitive("physical-tick"),
                programs.primitive("valuation"),
                programs.primitive("frame"),
            ),
            programs.primitive("output"),
            geometry,
        )
    )
    powered = actions.power(primitive, steps)
    output = programs.resolve(actions.resolve(powered).output_morphism)
    if output.exponent != steps:
        raise AssertionError("Collatz action construction lost its output exponent")
    ledger.bump("collatz_runtime_action_builds")
    return CollatzRuntimeActionBundle(programs, defects, actions, primitive, powered)


__all__ = ["CollatzRuntimeActionBundle", "build_collatz_runtime_action"]
