"""Exact Collatz orbit formulas synthesized from finite radix monoids.

The canonical Collatz representation here is binary.  The two arithmetic
branches are not handwritten bit loops:

* even: exact division by 2, synthesized as the finite remainder monoid;
* odd: exact ``3*n+1``, synthesized as the finite multiplication-carry monoid.

Both are compiled through :mod:`number_compiler.arithmetic.fields.digit_formula`, the same generic
parallel-prefix formula machinery used to express reverse-and-add carry scans.
This computes exact orbits for concrete seeds; it does **not** prove the Collatz
conjecture for all positive integers.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import NoReturn

from number_compiler.arithmetic.fields.binary_piecewise import (
    BinaryBranchDecision,
    BinaryPiecewiseHandler,
)
from number_compiler.arithmetic.fields.digit_formula import (
    CompiledDigitTransduction,
    DigitSpec,
    closed_digit_at,
    divide_formula,
    multiply_add_formula,
    synthesize_divide,
    synthesize_function_monoid,
    synthesize_multiply_add,
)
from number_compiler.arithmetic.formula.formula import FormulaArena, FormulaRoot
from number_compiler.arithmetic.polynomials.cyclotomic_affine import (
    CyclotomicAffineMorphism,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock

BINARY = DigitSpec(2)
COLLATZ_BINARY_HANDLER = BinaryPiecewiseHandler("collatz")


@dataclass(frozen=True, slots=True)
class CollatzStep:
    index: int
    branch: str
    root: FormulaRoot
    value: int | None
    width: int
    formula_nodes: int
    transducer_states: int
    transition_monoid_size: int
    residues: tuple[tuple[int, int, int], ...] = ()


def parity_bit(arena: FormulaArena, root: FormulaRoot) -> int:
    """Exact n mod 2 from the binary least-significant digit formula."""
    return closed_digit_at(arena, root, 0)


@dataclass(frozen=True, slots=True)
class CollatzPiecewiseMorphism:
    """Canonical self-branching binary Collatz successor.

    The branch is emitted from the current least-significant digit; it is never
    supplied as an itinerary symbol.  ``raw_cyclotomic_morphism`` exposes the
    same branch in the shared affine cyclotomic IR: even is the exact ``z^-1``
    shift, odd is the raw ``(1+z)x+1`` map before canonical radix normalization.
    """

    base: int = 2

    def __post_init__(self) -> None:
        if int(self.base) != 2:
            raise ValueError("canonical piecewise Collatz morphism is binary")

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz-piecewise-morphism", 2)

    def branch_decision(
        self, arena: FormulaArena, root: FormulaRoot
    ) -> BinaryBranchDecision:
        if root.plane_count != 1:
            raise ValueError("Collatz formula must use canonical binary digit planes")
        if parity_bit(arena, root) == 0:
            return BinaryBranchDecision.zero("collatz-lsb-parity")
        return BinaryBranchDecision.one("collatz-lsb-parity")

    def select_branch(self, arena: FormulaArena, root: FormulaRoot) -> str:
        decision = self.branch_decision(arena, root)
        return "divide_2" if decision.kind == "ZERO" else "multiply_3_add_1"

    def apply_formula(
        self,
        arena: FormulaArena,
        root: FormulaRoot,
    ) -> tuple[FormulaRoot, str, CompiledDigitTransduction]:
        decision = self.branch_decision(arena, root)

        def even(
            _decision: BinaryBranchDecision,
        ) -> tuple[FormulaRoot, str, CompiledDigitTransduction]:
            out, compiled = divide_formula(arena, root, BINARY, 2, require_exact=True)
            return out, "divide_2", compiled

        def odd(
            _decision: BinaryBranchDecision,
        ) -> tuple[FormulaRoot, str, CompiledDigitTransduction]:
            out, compiled = multiply_add_formula(arena, root, BINARY, 3, 1)
            return out, "multiply_3_add_1", compiled

        def impossible(branch: BinaryBranchDecision) -> NoReturn:
            raise AssertionError(("Collatz parity must be total", branch))

        return COLLATZ_BINARY_HANDLER.dispatch(
            decision,
            zero_branch=even,
            one_branch=odd,
            split_branch=impossible,
            unknown_branch=impossible,
        )

    def raw_cyclotomic_morphism(
        self, template: CyclotomicDigitBlock, branch: str
    ) -> CyclotomicAffineMorphism:
        """Return the branch's exact affine map before any required normalization."""
        from number_compiler.arithmetic.polynomials.cyclotomic_affine import (
            CyclotomicAffineMorphism,
        )

        branch = str(branch)
        if branch == "divide_2":
            return CyclotomicAffineMorphism.from_residues(
                template,
                template.z_power_residue(-1),
                (0,) * template.degree,
            )
        if branch == "multiply_3_add_1":
            return CyclotomicAffineMorphism.from_polynomials(template, (1, 1), (1,))
        raise ValueError(branch)


COLLATZ_PIECEWISE_MORPHISM = CollatzPiecewiseMorphism()


def collatz_successor_formula(
    arena: FormulaArena,
    root: FormulaRoot,
) -> tuple[FormulaRoot, str, CompiledDigitTransduction]:
    return COLLATZ_PIECEWISE_MORPHISM.apply_formula(arena, root)


def collatz_monoid_metrics() -> dict[str, dict[str, object]]:
    mul = synthesize_multiply_add(2, 3, 1)
    div = synthesize_divide(2, 2)
    mm = synthesize_function_monoid(mul)
    dm = synthesize_function_monoid(div)
    return {
        "multiply_3_add_1": {
            "states": len(mul.states),
            "state_values": mul.states,
            "transition_monoid": mm.size,
            "digit_generators": mm.digit_function,
        },
        "divide_2": {
            "states": len(div.states),
            "state_values": div.states,
            "transition_monoid": dm.size,
            "digit_generators": dm.digit_function,
        },
    }


__all__ = [
    "BINARY",
    "COLLATZ_BINARY_HANDLER",
    "COLLATZ_PIECEWISE_MORPHISM",
    "CollatzPiecewiseMorphism",
    "CollatzStep",
    "collatz_monoid_metrics",
    "collatz_successor_formula",
    "parity_bit",
]
