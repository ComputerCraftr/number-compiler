"""Reusable proofs for complete functions on one admitted primitive interface.

Keys contain only primitive sorts and canonical finite-function IDs. They have
no source, expression, occurrence, coordinate, or observed-argument component.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    LEFT_A,
    RIGHT_A,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    BoundaryExpressionArena,
    StateSort,
    SymbolSort,
)
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import (
    evaluate_primitive_bits,
)
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)


@dataclass(frozen=True, slots=True)
class FiniteInterfaceKey:
    source: StateSort
    target: StateSort | SymbolSort
    function: TransferSummaryID


@dataclass(frozen=True, slots=True)
class FiniteInterfaceCertificate:
    input_size: int
    output_size: int


class FiniteFunctionAdmission:
    def __init__(self, arena: BoundaryExpressionArena) -> None:
        self.arena = arena
        self.kernels = arena.boundaries.kernels
        self.ledger = arena.ledger
        self.ledger.register_execution_root(self)
        prefix = f"finite-interface-admission-{len(self.ledger.inventory())}"
        self.owner = self.ledger.register(prefix, "query_memo")
        self.memo: OwnedMemo[FiniteInterfaceKey, FiniteInterfaceCertificate] = (
            OwnedMemo(self.ledger, self.owner, evictable=True)
        )

    def interface(self, key: FiniteInterfaceKey) -> FiniteInterfaceCertificate:
        """Check current scope and immutable primitive metadata without telemetry."""
        if type(key) is not FiniteInterfaceKey or type(key.source) is not StateSort:
            raise ValueError(
                "finite admission requires a declared primitive input sort"
            )
        self.arena._validate_sort(key.source)
        before = self.arena.primitive(key.source.action)
        if before is None:
            raise ValueError(
                "finite admission cannot enumerate a composed input domain"
            )
        domain = len(before.domain(BoundarySide(key.source.side)))
        if type(key.target) is StateSort:
            self.arena._validate_sort(key.target)
            after = self.arena.primitive(key.target.action)
            if after is None or (before.base, before.blank) != (
                after.base,
                after.blank,
            ):
                raise ValueError(
                    "finite admission requires compatible primitive output metadata"
                )
            codomain = len(after.domain(BoundarySide(key.target.side)))
        elif type(key.target) is SymbolSort:
            self.arena._validate_sort(key.target)
            if (key.target.base, key.target.blank) != (before.base, before.blank):
                raise ValueError(
                    "finite admission symbol alphabet differs from the input primitive"
                )
            codomain = key.target.blank + 1
        else:
            raise ValueError("finite admission requires a finite output sort")
        expression = self.kernels.expression(key.function)
        if expression.domain != codomain:
            raise ValueError("finite function has another output domain")
        return FiniteInterfaceCertificate(domain, codomain)

    def validate(
        self,
        source: StateSort,
        target: StateSort | SymbolSort,
        function: TransferSummaryID,
    ) -> int:
        """Validate all inputs before a warm lookup; return actual proof visits."""
        key = FiniteInterfaceKey(source, target, function)
        certificate = self.interface(key)
        found = self.memo.get(key)
        if found is not None:
            if found != certificate:
                raise ValueError(
                    "finite admission certificate disagrees with its primitive interfaces"
                )
            self.ledger.bump(_interfaces_keys.FINITE_INTERFACE_ADMISSION_REQUESTS)
            self.ledger.bump(_interfaces_keys.FINITE_INTERFACE_ADMISSION_CACHE_HITS)
            return 0
        expression = self.kernels.expression(function)
        port = LEFT_A if source.side == 0 else RIGHT_A
        width = (certificate.input_size - 1).bit_length()
        allowed = {
            PortVariable(port.time, port.side, port.role, port.bit + bit)
            for bit in range(width)
        }
        pending, seen = list(expression.bits), set()
        visits, peak = 0, len(pending)
        functions = self.kernels.functions
        while pending:
            handle = pending.pop()
            visits += 1
            index = functions._resolve(handle)
            if index in seen:
                continue
            seen.add(index)
            node = functions._nodes[index]
            if node.variable is not None:
                if node.variable not in allowed:
                    raise ValueError("finite function contains another input interface")
                pending.extend(
                    (functions._handle(node.low), functions._handle(node.high))
                )
            peak = max(peak, len(pending) + len(seen))
        for value in range(certificate.input_size):
            output, decision_reads = evaluate_primitive_bits(
                self.kernels, expression, value, width, port
            )
            visits += decision_reads
            if output >= certificate.output_size:
                raise ValueError(
                    "finite function emits outside its declared primitive domain"
                )
        # All rejection paths above leave both telemetry and retained stores alone.
        self.ledger.bump(_interfaces_keys.FINITE_INTERFACE_ADMISSION_REQUESTS)
        self.ledger.bump(_interfaces_keys.FINITE_INTERFACE_ADMISSION_EVALUATIONS)
        self.ledger.bump(
            _interfaces_keys.FINITE_INTERFACE_ADMISSION_PROOF_VISITS, visits
        )
        self.ledger.bump(
            _interfaces_keys.FINITE_INTERFACE_ADMISSION_WORKSPACE_PEAK,
            max(
                0,
                peak
                - self.ledger.counters.get(
                    _interfaces_keys.FINITE_INTERFACE_ADMISSION_WORKSPACE_PEAK,
                    0,
                ),
            ),
        )
        limit = self.ledger.max_cache_entries
        node_limit = self.ledger.max_nodes
        if (limit is None or self.ledger.entries < limit) and (
            node_limit is None or self.ledger.nodes <= node_limit
        ):
            self.memo[key] = certificate
        else:
            self.ledger.bump(
                _interfaces_keys.FINITE_INTERFACE_ADMISSION_UNCACHED_EVALUATIONS
            )
        return visits
