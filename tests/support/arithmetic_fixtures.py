"""Fresh arithmetic interface fixtures shared by contract and payload audits."""

from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.arithmetic.fields.symbolic_innovation import (
    RadialMultiplier,
    SymbolicInnovationArena,
    SymbolicRadialInnovation,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.execution.diamond_primitive_demand import (
    PrimitiveDemandOracle,
)
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.observation.diamond_observers import NonblankBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.cylinder_innovation import (
    PrimitiveSuccessorClause,
)


def wide_innovation_operators() -> tuple[ResourceLedger, SymbolicInnovationArena]:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    one = arena.interval(1)
    arena.linear_combination((((1 << 130) + 1, one),))
    arena.radial(one, RadialMultiplier(1 << 130, 1 << 129))
    arena.chart(one, CylinderChart(-1, -(1 << 130)))
    return ledger, arena


def ternary_xy_ports() -> tuple[FinitePort, FinitePort, AtomSort]:
    x = FinitePort(PortVariable(0, 0, "x", 0), 3)
    y = FinitePort(PortVariable(0, 0, "y", 0), 3)
    return x, y, AtomSort("three", 3)


def nonblank_demand() -> tuple[
    ResourceLedger, DiamondKernelArena, ActionProgramID, PrimitiveDemandOracle
]:
    ledger = ResourceLedger()
    kernels = DiamondKernelArena(ledger)
    handle = kernels.intern(NonblankBlockEffect(2, 2))
    return ledger, kernels, handle, PrimitiveDemandOracle(kernels)


def forge_growth(clause: PrimitiveSuccessorClause, growth: int) -> None:
    """Forge only public growth fields, leaving retained authority untouched."""
    object.__setattr__(clause, "growth", growth)
    object.__setattr__(clause, "output_extent", clause.extent + growth)
    object.__setattr__(
        clause,
        "action",
        SymbolicRadialInnovation(RadialMultiplier(1 - growth, growth), clause._beta),
    )
