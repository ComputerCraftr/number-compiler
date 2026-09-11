"""Independent semantic identity, scope, and transaction-boundary regressions."""

from __future__ import annotations

from dataclasses import replace
from itertools import product
from typing import TYPE_CHECKING

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
    FunctionSort,
    ProductSort,
    SemanticFunctionID,
    SemanticSort,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.actions.diamond_actions import (
    ImageCellArena,
    TemporalActionArena,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.interfaces.diamond_quotient import (
    COMPONENT_ROLES,
    DiamondKey,
    DiamondQuotientArena,
    MacroComponents,
    MacroInterface,
)
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.arithmetic.functions.finite_function_types import (
        SemanticFunctionID,
        SemanticNode,
        SemanticRequest,
    )
    from number_compiler.arithmetic.functions.semantic_functions import (
        SemanticFunctionArena,
    )
    from number_compiler.hashlife.actions.diamond_actions import (
        ImageCellArena,
        PortSignatureID,
    )
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondKey,
        DiamondQuotientArena,
        LocalInterfaceID,
        MacroComponents,
        MacroInterface,
        QuotientRecord,
    )
    from number_compiler.resources.ledger import ResourceInventory, ResourceLedger


def _fixture() -> tuple[
    ResourceLedger,
    SemanticFunctionArena,
    DiamondQuotientArena,
    ImageCellArena,
    PortSignatureID,
    MacroComponents,
    SemanticFunctionID,
]:
    ledger = ResourceLedger()
    functions = SemanticFunctionArena(ledger)
    port = FinitePort(PortVariable(0, 0, "admissible", 0), 2)
    inputs = (port,)
    zero = functions.atom(FunctionSignature(inputs, BOOL), 0)
    one = functions.atom(FunctionSignature(inputs, BOOL), 1)
    admissible = functions.variable(inputs, port, BOOL)
    source = SourceGeometry(ledger, ExactSource((1, 0), 2, blank=2, extent=2))
    source.span((1, 0), 2, 2)
    cells = ImageCellArena(TemporalActionArena(LazyCompiler(ledger)), source)
    quotient = DiamondQuotientArena(functions, cells)
    interface = MacroInterface(
        SemanticIdentity("audit-kernel", ("fixed",)),
        inputs,
        (BOOL,) * len(COMPONENT_ROLES),
        admissible,
    )
    signature = quotient.intern_interface(interface)
    components = MacroComponents(*(zero for _ in COMPONENT_ROLES))
    return ledger, functions, quotient, cells, signature, components, one


def _retention(
    ledger: ResourceLedger,
    functions: SemanticFunctionArena,
    quotient: DiamondQuotientArena,
) -> tuple[
    int,
    int,
    int,
    int,
    tuple[ResourceInventory, ...],
    tuple[SemanticNode, ...],
    tuple[tuple[SemanticNode, int], ...],
    tuple[tuple[SemanticRequest, SemanticFunctionID], ...],
    tuple[MacroInterface, ...],
    tuple[tuple[MacroInterface, PortSignatureID], ...],
    tuple[QuotientRecord, ...],
    tuple[tuple[QuotientRecord, LocalInterfaceID], ...],
    tuple[tuple[DiamondKey, LocalInterfaceID], ...],
]:
    snapshot = ledger.snapshot()
    return (
        snapshot.entries,
        snapshot.nodes,
        snapshot.peak_entries,
        snapshot.peak_nodes,
        snapshot.inventory,
        tuple(functions.nodes),
        tuple(functions.keys.items()),
        tuple(functions.memo.items()),
        tuple(quotient._signatures),
        tuple(quotient._signature_keys.items()),
        tuple(quotient._nodes.values()),
        tuple(quotient._keys.items()),
        tuple(quotient.parents.items()),
    )


@pytest.mark.parametrize("extra_entries", (2, 3))
def test_failed_complete_normalization_cannot_publish_partial_function_state(
    extra_entries: int,
) -> None:
    ledger, functions, quotient, _, signature, components, _ = _fixture()
    ledger.tighten_limits(None, ledger.entries + extra_entries)
    before = _retention(ledger, functions, quotient)
    with pytest.raises(BlockContextBudgetExceeded):
        quotient.intern(signature, components)
    after = _retention(ledger, functions, quotient)
    assert after[:2] == before[:2]
    assert after[4:] == before[4:]
    # Rejected publication rolls back retention, not the real scratch peak.
    assert after[2] >= before[2]
    assert after[3] >= before[3]


def test_failed_complete_normalization_is_atomic_for_node_budget_too() -> None:
    ledger, functions, quotient, _, signature, components, _ = _fixture()
    ledger.tighten_limits(ledger.nodes + 1, None)
    before = _retention(ledger, functions, quotient)
    with pytest.raises(BlockContextBudgetExceeded):
        quotient.intern(signature, components)
    after = _retention(ledger, functions, quotient)
    assert after[:2] == before[:2]
    assert after[4:] == before[4:]
    assert after[2] >= before[2]
    assert after[3] >= before[3]


def test_parent_normalization_failure_does_not_leave_a_successful_child_memo() -> None:
    ledger, functions, quotient, cells, signature, components, one = _fixture()
    child = quotient.intern(signature, components)
    cell = cells.source_span(0, 2)[0][1]
    key = DiamondKey(child, child, cell, 1, 0, 0, signature)
    ledger.tighten_limits(None, ledger.entries + 1)
    before = _retention(ledger, functions, quotient)
    with pytest.raises(BlockContextBudgetExceeded):
        quotient.normalize_and_publish(key, replace(components, output=one))
    assert _retention(ledger, functions, quotient) == before


@pytest.mark.parametrize("kind", ("product", "function"))
def test_cyclic_semantic_sort_rejects_without_recursive_hashing_or_retention(
    kind: str,
) -> None:
    functions = SemanticFunctionArena(ResourceLedger())
    cyclic: ProductSort | FunctionSort
    if kind == "product":
        cyclic = object.__new__(ProductSort)
        object.__setattr__(cyclic, "items", (cyclic,))
    else:
        cyclic = object.__new__(FunctionSort)
        object.__setattr__(cyclic, "inputs", ())
        object.__setattr__(cyclic, "output", cyclic)
    before = functions.ledger.snapshot()
    with pytest.raises((TypeError, ValueError)):
        functions.invalid(FunctionSignature((), cyclic))
    assert functions.ledger.snapshot() == before


def test_macro_admissibility_rejects_non_boolean_named_sort_before_retention() -> None:
    ledger, functions, quotient, _, signature, _, _ = _fixture()
    impostor = functions.atom(
        FunctionSignature(
            quotient.interface(signature).inputs, AtomSort("unrelated-two-state", 2)
        ),
        1,
    )
    malformed = replace(quotient.interface(signature), admissible=impostor)
    before = _retention(ledger, functions, quotient)
    with pytest.raises((TypeError, ValueError)):
        quotient.intern_interface(malformed)
    assert _retention(ledger, functions, quotient) == before


def test_nested_kernel_identity_cannot_hide_mutable_payload() -> None:
    ledger, functions, quotient, _, signature, _, _ = _fixture()
    nested = SemanticIdentity("nested", ("valid",))
    kernel = SemanticIdentity("outer", (nested,))
    object.__setattr__(nested, "behavior", ([0, 1, 0, 1],))
    malformed = replace(quotient.interface(signature), kernel=kernel)
    before = _retention(ledger, functions, quotient)
    with pytest.raises((TypeError, ValueError)):
        quotient.intern_interface(malformed)
    assert _retention(ledger, functions, quotient) == before


def test_three_port_currying_and_capture_avoiding_application_share_canonical_truth_table() -> (
    None
):
    functions = SemanticFunctionArena(ResourceLedger())
    ports = tuple(
        FinitePort(PortVariable(0, 0, name, 0), 2) for name in ("a", "b", "c")
    )
    a, b, c = (functions.variable(ports, port, BOOL) for port in ports)
    zero = functions.atom(FunctionSignature(ports, BOOL), 0)
    one = functions.atom(FunctionSignature(ports, BOOL), 1)
    xor_ab = functions.ite(a, functions.ite(b, zero, one), b)
    parity = functions.ite(c, functions.ite(xor_ab, zero, one), xor_ab)
    for bound in ((ports[0], ports[2]), (ports[1],), ports):
        curried = functions.curry(parity, bound)
        arguments = {
            port.variable: functions.variable(ports, port, BOOL) for port in bound
        }
        assert functions.apply(curried, arguments) == parity
    for values in product(range(2), repeat=3):
        supplied = dict(zip((port.variable for port in ports), values, strict=True))
        assert (
            functions.evaluate(parity, supplied).value
            == values[0] ^ values[1] ^ values[2]
        )


@pytest.mark.parametrize("warm", (False, True))
def test_function_application_checks_foreign_unused_arguments_before_lookup(
    warm: bool,
) -> None:
    functions = SemanticFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "x", 0), 2)
    constant = functions.atom(FunctionSignature((port,), BOOL), 0)
    curried = functions.curry(constant, (port,))
    local = functions.atom(FunctionSignature((), BOOL), 0)
    if warm:
        functions.apply(curried, {port.variable: local})
    foreign = SemanticFunctionArena(ResourceLedger()).atom(
        FunctionSignature((), BOOL), 0
    )
    before = functions.ledger.snapshot()
    with pytest.raises((TypeError, ValueError)):
        functions.apply(curried, {port.variable: foreign})
    assert functions.ledger.snapshot() == before


def test_deep_acyclic_finite_sort_uses_iterative_identity_not_recursive_hashing() -> (
    None
):
    functions = SemanticFunctionArena(ResourceLedger())
    sort: SemanticSort = BOOL
    for _ in range(1500):
        sort = ProductSort((sort,))
    function = functions.invalid(FunctionSignature((), sort))
    assert functions.resolve(function).signature.output == sort
    assert functions.evaluate(function, {}).kind == "invalid"


@pytest.mark.parametrize("role", COMPONENT_ROLES)
def test_complete_quotient_rejects_undefined_channel_on_admissible_ports(
    role: str,
) -> None:
    ledger, functions, quotient, _, signature, components, _ = _fixture()
    assert isinstance(components.output, SemanticFunctionID)
    invalid = functions.invalid(functions.signature(components.output))
    before = _retention(ledger, functions, quotient)
    with pytest.raises(ValueError):
        quotient.intern(
            signature,
            MacroComponents(
                *(
                    invalid if name == role else value
                    for name, value in zip(
                        COMPONENT_ROLES, components.functions(), strict=True
                    )
                )
            ),
        )
    assert _retention(ledger, functions, quotient) == before


def test_complete_function_channel_requires_total_body_not_only_a_function_terminal() -> (
    None
):
    ledger, functions, quotient, _, signature, components, _ = _fixture()
    interface = quotient.interface(signature)
    bound = FinitePort(PortVariable(0, 0, "inner", 0), 2)
    undefined = functions.invalid(FunctionSignature(interface.inputs + (bound,), BOOL))
    function_value = functions.curry(undefined, (bound,))
    outputs = list(interface.outputs)
    outputs[COMPONENT_ROLES.index("output")] = functions.signature(
        function_value
    ).output
    nested_signature = quotient.intern_interface(
        replace(interface, outputs=tuple(outputs))
    )
    before = _retention(ledger, functions, quotient)
    with pytest.raises(ValueError):
        quotient.intern(nested_signature, replace(components, output=function_value))
    assert _retention(ledger, functions, quotient) == before
