"""Audit-scoped validation for retained future-behavior records."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.semantic_identity import (
    SemanticIdentity,
    SemanticIdentityValidator,
)
from number_compiler.hashlife.behavior.future_behavior import (
    FutureBehaviorClass,
    FutureBehaviorProfile,
    QuiescentBlankCertificate,
)
from number_compiler.hashlife.interfaces import primitive_behavior
from number_compiler.hashlife.interfaces.primitive_behavior import (
    CertifiedLocalSymmetry,
    PrimitiveBehaviorQuotient,
)
from number_compiler.resources.ledger import ResourceLedger


class BehaviorPayloadValidator:
    """Validate one audit's shared behavior DAG without retaining authority."""

    record_types = (
        CertifiedLocalSymmetry,
        FutureBehaviorClass,
        FutureBehaviorProfile,
        PrimitiveBehaviorQuotient,
        QuiescentBlankCertificate,
    )

    def __init__(self, ledger: ResourceLedger) -> None:
        from number_compiler.hashlife.interfaces.diamond_kernel import (
            DiamondKernelArena,
        )

        self._identities = SemanticIdentityValidator()
        self._checked: dict[int, tuple[object, bool]] = {}
        self._quotients = {
            quotient.semantic_identity: quotient
            for root in ledger.iter_execution_roots()
            if type(root) is DiamondKernelArena and root.ledger is ledger
            for quotient in root._behavioral_quotients.values()
        }

    def recognizes(self, value: object) -> bool:
        return type(value) in self.record_types

    def validate_identity(self, value: SemanticIdentity) -> None:
        """Validate an identity in this audit's shared union DAG."""
        self._identities.validate(value)

    def valid(self, value: object) -> bool:
        checked = self._checked.get(id(value))
        if checked is not None and checked[0] is value:
            return checked[1]
        try:
            if type(value) is PrimitiveBehaviorQuotient:
                primitive_behavior.validate_primitive_behavior_quotient(
                    value,
                    validate_identity=self.validate_identity,
                )
            elif type(value) is CertifiedLocalSymmetry:
                quotient = self._quotients.get(value.behavior)
                if quotient is None:
                    raise ValueError("local symmetry omitted its quotient")
                primitive_behavior.validate_certified_local_symmetry(quotient, value)
            elif type(value) is FutureBehaviorClass:
                value.__post_init__()
            elif (
                type(value) is FutureBehaviorProfile
                or type(value) is QuiescentBlankCertificate
            ):
                value.validate_with(self.validate_identity)
            else:
                return False
            valid = True
        except (TypeError, ValueError, AttributeError):
            valid = False
        self._checked[id(value)] = value, valid
        return valid

    def finish(self) -> None:
        self._identities.finish()


__all__ = ["BehaviorPayloadValidator"]
