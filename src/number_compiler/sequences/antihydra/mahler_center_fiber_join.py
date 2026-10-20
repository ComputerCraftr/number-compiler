"""Source-fiber joins for already-issued Mahler center summaries."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.sequences.antihydra.mahler_joint_future import (
    MahlerJointFutureAction,
)

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.mahler_center_depth_matrix import (
        MahlerCenterBooleanMatrix,
        MahlerCertifiedCenterDepthTransfer,
    )
    from number_compiler.sequences.antihydra.mahler_low_border_carry import (
        MahlerLowBorderCarryCertificate,
    )
    from number_compiler.sequences.antihydra.mahler_port_puncture import (
        MahlerCenterPortPuncture,
    )

MAX_CENTER_TICKS = 32


@dataclass(frozen=True, slots=True)
class MahlerComposedCenterTransferFields:
    """Validated field values for a joined source-certified transfer."""

    matrix: MahlerCenterBooleanMatrix
    safety_matrix: MahlerCenterBooleanMatrix
    steps: int
    pointed_sources: tuple[int, ...]
    pointed_centers: tuple[int, ...]
    center_positions: tuple[int, ...]
    radix99: tuple[int, ...]
    radix198: tuple[int, ...]
    rejected_source_paths: int
    width_births: tuple[int, ...]
    conditional_composition: MahlerCenterBooleanMatrix
    initial_ledger: int | None
    low_border_carries: tuple[MahlerLowBorderCarryCertificate | None, ...]
    source_port_punctures: tuple[tuple[MahlerCenterPortPuncture, ...], ...]
    source_fiber_edges: tuple[MahlerCenterFiberEdge, ...]
    composition_joins: int
    equal_span_joins: int


def allocate_transfer_fields(
    transfer_type: type[MahlerCertifiedCenterDepthTransfer],
    fields: dict[str, object],
) -> MahlerCertifiedCenterDepthTransfer:
    """Allocate a transfer from an exact builder field mapping.

    The trusted caller validates the derived values and attaches the issuer
    seal after this helper returns.
    """
    names = (
        "matrix",
        "safety_matrix",
        "steps",
        "pointed_sources",
        "pointed_centers",
        "center_positions",
        "radix99",
        "radix198",
        "rejected_source_paths",
        "width_births",
        "conditional_composition",
        "initial_ledger",
        "low_border_carries",
        "source_port_punctures",
        "source_fiber_edges",
        "composition_joins",
        "equal_span_joins",
    )
    if type(fields) is not dict or tuple(fields) != names:
        raise ValueError("Mahler center issuer received an incomplete field set")
    result = object.__new__(transfer_type)
    for name in names:
        object.__setattr__(result, name, fields[name])
    return result


@dataclass(frozen=True, slots=True)
class MahlerCenterFiberEdge:
    """One checked temporal edge keyed by its complete integer source."""

    source: int
    endpoint: int
    future: MahlerJointFutureAction
    ledger_delta: int
    ledger_minimum: int

    def __post_init__(self) -> None:
        if (
            type(self.source) is not int
            or self.source < 1
            or type(self.endpoint) is not int
            or self.endpoint < 1
            or type(self.future) is not MahlerJointFutureAction
            or type(self.ledger_delta) is not int
            or type(self.ledger_minimum) is not int
            or self.ledger_minimum > min(0, self.ledger_delta)
            or not self.future.integer_admits(self.source)
            or self.future.endpoint(self.source) != self.endpoint
        ):
            raise ValueError("invalid source-issued Mahler fiber edge")

    def then(self, after: MahlerCenterFiberEdge) -> MahlerCenterFiberEdge:
        """Compose only adjacent full roots and pull back the second guard."""
        if type(after) is not MahlerCenterFiberEdge or self.endpoint != after.source:
            raise ValueError("full-source Mahler fiber seams do not coincide")
        future = self.future.then(after.future)
        if (
            not future.integer_admits(self.source)
            or future.endpoint(self.source) != after.endpoint
        ):
            raise ArithmeticError("powered Mahler source guard lost its exact endpoint")
        delta = self.ledger_delta + after.ledger_delta
        minimum = min(self.ledger_minimum, self.ledger_delta + after.ledger_minimum)
        return MahlerCenterFiberEdge(
            self.source, after.endpoint, future, delta, minimum
        )

    def ledger_safe(self, initial: int | None) -> bool:
        return initial is None or initial + self.ledger_minimum >= 0


def compose_transfers(
    first: MahlerCertifiedCenterDepthTransfer,
    second: MahlerCertifiedCenterDepthTransfer,
) -> MahlerComposedCenterTransferFields:
    """Compose cached full-source actions; never reissue spatial cones."""
    from number_compiler.sequences.antihydra.mahler_center_depth_matrix import (
        MahlerCenterBooleanMatrix,
        MahlerCertifiedCenterDepthTransfer,
    )

    if (
        type(first) is not MahlerCertifiedCenterDepthTransfer
        or type(second) is not MahlerCertifiedCenterDepthTransfer
    ):
        raise TypeError("center trace needs another source-certified relation")
    first.require_issued()
    second.require_issued()
    if first.pointed_sources[-1] != second.pointed_sources[0]:
        raise ValueError("Mahler center traces have nonadjacent full source roots")
    if first.center_positions[-1] != second.center_positions[0]:
        raise ValueError("Mahler center traces disagree on their seam coordinate")
    if first.steps + second.steps > MAX_CENTER_TICKS:
        raise BlockContextBudgetExceeded(
            "joined center transfer exceeds source horizon"
        )

    if first.initial_ledger is not None:
        pointed = next(
            (
                edge
                for edge in first.source_fiber_edges
                if edge.source == first.pointed_sources[0]
            ),
            None,
        )
        if pointed is None or pointed.endpoint != first.pointed_sources[-1]:
            raise ArithmeticError("first half lost its authenticated pointed edge")
        balance = first.initial_ledger + pointed.ledger_delta
        if second.initial_ledger is not None and second.initial_ledger != balance:
            raise ValueError("Mahler matrix second-half ledger is detached")
    elif second.initial_ledger is not None:
        raise ValueError("cannot introduce a known ledger after an unknown prefix")

    right_edges = {edge.source: edge for edge in second.source_fiber_edges}
    if len(right_edges) != len(second.source_fiber_edges):
        raise ArithmeticError("second-half source fiber has duplicate source roots")
    joined_edges = tuple(
        edge.then(right_edges[edge.endpoint])
        for edge in first.source_fiber_edges
        if edge.endpoint in right_edges
    )
    arithmetic = [0] * 100
    safety = [0] * 100
    for edge in joined_edges:
        src_center = (edge.source // 10 ** first.center_positions[0]) % 100
        dst_center = (edge.endpoint // 10 ** second.center_positions[-1]) % 100
        arithmetic[src_center] |= 1 << dst_center
        if not edge.future.guard.empty and edge.ledger_safe(first.initial_ledger):
            safety[src_center] |= 1 << dst_center

    conditional = first.conditional_composition.then(second.conditional_composition)
    if any(row & ~conditional.rows[i] for i, row in enumerate(arithmetic)):
        raise ArithmeticError("source-fiber join violates conditional center matrix")
    first_center = first.pointed_centers[0]
    last_center = second.pointed_centers[-1]
    if not ((arithmetic[first_center] >> last_center) & 1):
        raise ArithmeticError("power lost actual pointed integer-source trajectory")

    return MahlerComposedCenterTransferFields(
        matrix=MahlerCenterBooleanMatrix(tuple(arithmetic)),
        safety_matrix=MahlerCenterBooleanMatrix(tuple(safety)),
        steps=first.steps + second.steps,
        pointed_sources=first.pointed_sources + second.pointed_sources[1:],
        pointed_centers=first.pointed_centers + second.pointed_centers[1:],
        center_positions=first.center_positions + second.center_positions[1:],
        radix99=first.radix99 + second.radix99[1:],
        radix198=first.radix198 + second.radix198[1:],
        rejected_source_paths=(
            first.rejected_source_paths
            + len(first.source_fiber_edges)
            - len(joined_edges)
        ),
        width_births=first.width_births
        + tuple(first.steps + tick for tick in second.width_births),
        conditional_composition=conditional,
        initial_ledger=first.initial_ledger,
        low_border_carries=first.low_border_carries + second.low_border_carries,
        source_port_punctures=first.source_port_punctures
        + second.source_port_punctures,
        source_fiber_edges=joined_edges,
        composition_joins=first.composition_joins + second.composition_joins + 1,
        equal_span_joins=(
            first.equal_span_joins
            + second.equal_span_joins
            + int(first.steps == second.steps)
        ),
    )


def powered_from_source(
    transfer_type: type[MahlerCertifiedCenterDepthTransfer],
    source: int,
    physical_steps: int,
    *,
    initial_ledger: int | None = None,
    leaf_steps: int = 4,
) -> MahlerCertifiedCenterDepthTransfer:
    """Join bounded source fibers as admitted one-step actions emit endpoints.

    This builds a finite diagnostic transfer; it does not claim that a
    production term query has become sublinear. The selected path is advanced
    by the existing source-admitted successor actions, and each leaf consumes
    those same actions instead of rediscovering its pointed word afterward.
    """
    if type(source) is not int or source <= 0:
        raise ValueError("positive pointed Mahler center source required")
    if source >= 10**256:
        raise BlockContextBudgetExceeded(
            "pointed source exceeds the 256-digit center matrix budget"
        )
    if (
        type(physical_steps) is not int
        or not 1 <= physical_steps <= MAX_CENTER_TICKS
        or type(leaf_steps) is not int
        or not 1 <= leaf_steps <= 16
    ):
        raise ValueError("powered center certificate exceeds finite horizon")
    if initial_ledger is not None and type(initial_ledger) is not int:
        raise TypeError("initial ledger must be an exact integer")

    branches = MahlerJointFutureAction().successor_branches()
    admitted_actions = {branch.epsilon: branch.action for branch in branches}
    if set(admitted_actions) != {0, 1}:
        raise ArithmeticError("Mahler source owner did not issue both one-bit branches")

    layers: list[MahlerCertifiedCenterDepthTransfer] = []
    leaf_sources = [source]
    leaf_futures: list[MahlerJointFutureAction] = []
    leaf_balance = initial_ledger
    current_balance = initial_ledger
    current = source
    for tick in range(physical_steps):
        epsilon = current & 1
        edge_future = admitted_actions[epsilon]
        if not edge_future.integer_admits(current):
            raise ArithmeticError("selected Mahler branch rejected its current source")
        endpoint = edge_future.endpoint(current)
        if endpoint <= 0 or endpoint >= 10**256:
            raise BlockContextBudgetExceeded(
                "pointed source exceeds the 256-digit center matrix budget"
            )
        leaf_sources.append(endpoint)
        leaf_futures.append(edge_future)
        current_balance = (
            None if current_balance is None else current_balance + 3 * epsilon - 1
        )
        current = endpoint

        leaf_finished = len(leaf_futures) == leaf_steps
        final_tick = tick + 1 == physical_steps
        if leaf_finished or final_tick:
            layers.append(
                transfer_type.from_sources(
                    tuple(leaf_sources),
                    initial_ledger=leaf_balance,
                    pointed_futures=tuple(leaf_futures),
                )
            )
            leaf_sources = [current]
            leaf_futures = []
            leaf_balance = current_balance
    while len(layers) > 1:
        next_layer: list[MahlerCertifiedCenterDepthTransfer] = []
        for index in range(0, len(layers), 2):
            if index + 1 == len(layers):
                next_layer.append(layers[index])
            else:
                left, right = layers[index : index + 2]
                next_layer.append(
                    left.square_with(right)
                    if left.steps == right.steps
                    else left.then(right)
                )
        layers = next_layer
    return layers[0]


__all__ = [
    "MahlerCenterFiberEdge",
    "MahlerComposedCenterTransferFields",
    "allocate_transfer_fields",
    "compose_transfers",
    "powered_from_source",
]
