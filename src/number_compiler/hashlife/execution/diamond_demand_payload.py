"""Independent scope and finite-domain checks for primitive demand memos."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.execution.diamond_primitive_demand import (
    PrimitiveDemandCertificate,
    PrimitiveDemandKey,
    PrimitiveDemandOracle,
)
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.resources.ledger import ResourceLedger


class DemandPayloadRegistry:
    record_types = (PrimitiveDemandKey, PrimitiveDemandCertificate)

    def __init__(
        self, ledger: ResourceLedger, kernels: tuple[DiamondKernelArena, ...]
    ) -> None:
        actual = dict(ledger.iter_containers())
        self.oracles = tuple(
            root
            for root in ledger.iter_execution_roots()
            if type(root) is PrimitiveDemandOracle
            and root.ledger is ledger
            and root.kernels in kernels
            and actual.get(root.owner) is root.memo._data
        )
        self.accepted: set[int] = set()
        self.rejected: set[int] = set()
        for oracle in self.oracles:
            for key, certificate in oracle.memo.items():
                target = (
                    self.accepted
                    if self._entry(oracle, key, certificate)
                    else self.rejected
                )
                target.update((id(key), id(certificate)))

    @staticmethod
    def _entry(oracle: PrimitiveDemandOracle, key: object, certificate: object) -> bool:
        if (
            type(key) is not PrimitiveDemandKey
            or type(certificate) is not PrimitiveDemandCertificate
        ):
            return False
        if (
            type(key.kernel) is not ActionProgramID
            or key.kernel.kind != "diamond-kernel"
            or key.kernel.owner is not oracle.kernels.owner
            or type(key.kernel.local_id) is not int
            or not 0 <= key.kernel.local_id < len(oracle.kernels._kernels)
            or type(key.operation) is not str
            or key.operation not in ("advance", "emit")
            or type(key.side) is not int
            or key.side not in (0, 1)
            or key.operation == "emit"
            and key.side != 0
            or type(key.values) is not tuple
        ):
            return False
        primitive = oracle.kernels._kernels[key.kernel.local_id]
        count = primitive.left_count if key.side == 0 else primitive.right_count
        sizes = (
            (count, primitive.blank + 1)
            if key.operation == "advance"
            else (primitive.left_count, primitive.blank + 1, primitive.right_count)
        )
        output_size = count if key.operation == "advance" else primitive.blank + 1
        return (
            len(key.values) == len(sizes)
            and any(value is None for value in key.values)
            and all(
                value is None or type(value) is int and 0 <= value < size
                for value, size in zip(key.values, sizes, strict=True)
            )
            and (
                certificate.value is None
                or type(certificate.value) is int
                and 0 <= certificate.value < output_size
            )
        )

    def valid(self, value: object) -> bool:
        # A familiar bounded record is not an authority: it must be the actual
        # key/value of an owned memo, with its paired primitive domain checked.
        return (
            type(value) in self.record_types
            and id(value) in self.accepted
            and id(value) not in self.rejected
        )
