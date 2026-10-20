"""Read-only resource-audit contract for reverse/add field-action owners."""

from __future__ import annotations

from collections.abc import Mapping, MutableMapping, MutableSequence
from dataclasses import dataclass
from types import MappingProxyType
from typing import TYPE_CHECKING, Protocol

from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.arithmetic.carry.carry_monoid import CarryFn, compose_carry_fn
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.reverse_add.field_action_types import (
    BinarySemanticOp,
    ReverseActionAutomorphisms,
    ReverseDefectClassID,
    ReverseFieldAction,
    ReverseGeometry,
    SemanticKey,
)
from number_compiler.sequences.reverse_add.semantic_identity_cache import (
    SemanticIdentityMemoRecord,
    build_radial_identity,
    valid_radial_memo,
)

if TYPE_CHECKING:
    from number_compiler.resources.payload_contracts import PayloadAuditStoreBinding
    from number_compiler.sequences.reverse_add.coordinate_program import (
        ReverseCoordinateProgramArena,
    )


@dataclass(frozen=True, slots=True)
class ReverseFieldActionAuditSnapshot:
    """Fresh immutable view of this arena's exact registered stores."""

    ledger: ResourceLedger
    owner: ArenaToken
    base: int
    order: int
    max_residual_classes: int
    coordinate_programs: ReverseCoordinateProgramArena | None
    action_kind: str
    residual_kind: str
    output_kind: str
    stores: tuple[tuple[int, str, str, object], ...]
    residual_owner: int
    residual_key_owner: int
    output_owner: int
    output_key_owner: int
    action_owner: int
    action_key_owner: int
    compose_owner: int
    transform_owner: int
    witness_owner: int
    semantic_identity_owner: int
    semantic_identity_issued_owner: int
    residual_backing: object
    residual_key_backing: object
    output_backing: object
    output_key_backing: object
    action_backing: object
    action_key_backing: object
    compose_backing: object
    transform_backing: object
    witness_backing: object
    semantic_identity_backing: object
    semantic_identity_issued_backing: object
    residuals: tuple[SemanticKey, ...]
    residual_keys: Mapping[SemanticKey, ReverseDefectClassID]
    outputs: tuple[SemanticKey, ...]
    output_keys: Mapping[SemanticKey, CoordinateOutputMorphismID]
    actions: tuple[ReverseFieldAction, ...]
    action_keys: Mapping[tuple[object, ...], FieldCellActionID]
    compositions: Mapping[
        tuple[FieldCellActionID, FieldCellActionID], FieldCellActionID
    ]
    transforms: Mapping[tuple[FieldCellActionID, ActionTransform], FieldCellActionID]
    witnesses: Mapping[FieldCellActionID, tuple[FieldCellActionID, FieldCellActionID]]
    semantic_identities: Mapping[FieldCellActionID, SemanticIdentityMemoRecord]
    semantic_identity_issued: Mapping[FieldCellActionID, SemanticIdentityMemoRecord]


class ReverseFieldActionAudit(Protocol):
    """Audit operations implemented on the same owner, never a certificate issuer."""

    ledger: ResourceLedger
    owner: ArenaToken
    _base: int
    _order: int
    _max_residual_classes: int
    _coordinate_programs: ReverseCoordinateProgramArena | None
    _ACTION_KIND: str
    _RESIDUAL_KIND: str
    _OUTPUT_KIND: str
    _residual_owner: int
    _residual_key_owner: int
    _output_owner: int
    _output_key_owner: int
    _action_owner: int
    _action_key_owner: int
    _compose_owner: int
    _transform_owner: int
    _witness_owner: int
    _semantic_identity_owner: int
    _semantic_identity_issued_owner: int
    _residuals: MutableSequence[SemanticKey]
    _residual_keys: MutableMapping[SemanticKey, ReverseDefectClassID]
    _outputs: MutableSequence[SemanticKey]
    _output_keys: MutableMapping[SemanticKey, CoordinateOutputMorphismID]
    _actions: MutableSequence[ReverseFieldAction]
    _action_keys: MutableMapping[tuple[object, ...], FieldCellActionID]
    _compose: MutableMapping[
        tuple[FieldCellActionID, FieldCellActionID], FieldCellActionID
    ]
    _transforms: MutableMapping[
        tuple[FieldCellActionID, ActionTransform], FieldCellActionID
    ]
    _witnesses: MutableMapping[
        FieldCellActionID, tuple[FieldCellActionID, FieldCellActionID]
    ]
    _semantic_identities: LedgerDict[FieldCellActionID, SemanticIdentityMemoRecord]
    _semantic_identity_issued: LedgerDict[FieldCellActionID, SemanticIdentityMemoRecord]
    _residual_compose: BinarySemanticOp
    _output_compose: BinarySemanticOp
    _automorphisms: ReverseActionAutomorphisms

    def resolve(self, reference: FieldCellActionID) -> ReverseFieldAction: ...
    def _canonical_block(
        self, block: ReverseAddCyclotomicInnovationBlock
    ) -> ReverseAddCyclotomicInnovationBlock: ...
    @staticmethod
    def innovation_block(
        action: ReverseFieldAction,
    ) -> ReverseAddCyclotomicInnovationBlock: ...
    def _action_key(
        self,
        base: int,
        block: ReverseAddCyclotomicInnovationBlock,
        carry_forward: CarryFn,
        carry_backward: CarryFn,
        residual: ReverseDefectClassID,
        output: CoordinateOutputMorphismID,
        geometry: ReverseGeometry,
    ) -> tuple[object, ...]: ...
    @staticmethod
    def _validate_semantic_key(key: SemanticKey) -> None: ...
    def _residual_key(self, reference: ReverseDefectClassID) -> SemanticKey: ...
    def _output_key(self, reference: CoordinateOutputMorphismID) -> SemanticKey: ...
    def _transformed_components(
        self, action: ReverseFieldAction, transform: ActionTransform
    ) -> tuple[
        ReverseAddCyclotomicInnovationBlock,
        SemanticKey,
        SemanticKey,
        CarryFn,
        CarryFn,
        ReverseGeometry,
    ]: ...

    def payload_audit_store_bindings(
        self,
    ) -> tuple[PayloadAuditStoreBinding, ...]:
        """Return exact owned-store bindings for the explicit resource audit."""
        from number_compiler.resources.payload_contracts import (
            PayloadAuditStoreBinding,
        )

        return (
            PayloadAuditStoreBinding(
                self._residual_owner, "_residuals", "reverse_residual_node"
            ),
            PayloadAuditStoreBinding(
                self._residual_key_owner,
                "_residual_keys",
                "reverse_residual_interner",
            ),
            PayloadAuditStoreBinding(
                self._output_owner, "_outputs", "reverse_output_morphism"
            ),
            PayloadAuditStoreBinding(
                self._output_key_owner, "_output_keys", "reverse_output_interner"
            ),
            PayloadAuditStoreBinding(
                self._action_owner, "_actions", "reverse_field_action"
            ),
            PayloadAuditStoreBinding(
                self._action_key_owner, "_action_keys", "reverse_action_interner"
            ),
            PayloadAuditStoreBinding(
                self._compose_owner, "_compose", "reverse_action_composition"
            ),
            PayloadAuditStoreBinding(
                self._transform_owner, "_transforms", "reverse_action_transform"
            ),
            PayloadAuditStoreBinding(
                self._witness_owner,
                "_witnesses",
                "reverse_action_construction_witness",
            ),
            PayloadAuditStoreBinding(
                self._semantic_identity_owner,
                "_semantic_identities",
                "reverse_action_semantic_identity",
            ),
            PayloadAuditStoreBinding(
                self._semantic_identity_issued_owner,
                "_semantic_identity_issued",
                "reverse_action_semantic_identity_authority",
            ),
        )

    def payload_audit_snapshot(self) -> ReverseFieldActionAuditSnapshot:
        """Copy the current direct-store rows while preserving object identity."""
        stores = (
            (
                self._residual_owner,
                "_residuals",
                "reverse_residual_node",
                self._residuals,
            ),
            (
                self._residual_key_owner,
                "_residual_keys",
                "reverse_residual_interner",
                self._residual_keys,
            ),
            (self._output_owner, "_outputs", "reverse_output_morphism", self._outputs),
            (
                self._output_key_owner,
                "_output_keys",
                "reverse_output_interner",
                self._output_keys,
            ),
            (self._action_owner, "_actions", "reverse_field_action", self._actions),
            (
                self._action_key_owner,
                "_action_keys",
                "reverse_action_interner",
                self._action_keys,
            ),
            (
                self._compose_owner,
                "_compose",
                "reverse_action_composition",
                self._compose,
            ),
            (
                self._transform_owner,
                "_transforms",
                "reverse_action_transform",
                self._transforms,
            ),
            (
                self._witness_owner,
                "_witnesses",
                "reverse_action_construction_witness",
                self._witnesses,
            ),
            (
                self._semantic_identity_owner,
                "_semantic_identities",
                "reverse_action_semantic_identity",
                self._semantic_identities,
            ),
            (
                self._semantic_identity_issued_owner,
                "_semantic_identity_issued",
                "reverse_action_semantic_identity_authority",
                self._semantic_identity_issued,
            ),
        )
        return ReverseFieldActionAuditSnapshot(
            ledger=self.ledger,
            owner=self.owner,
            base=self._base,
            order=self._order,
            max_residual_classes=self._max_residual_classes,
            coordinate_programs=self._coordinate_programs,
            action_kind=self._ACTION_KIND,
            residual_kind=self._RESIDUAL_KIND,
            output_kind=self._OUTPUT_KIND,
            stores=stores,
            residual_owner=self._residual_owner,
            residual_key_owner=self._residual_key_owner,
            output_owner=self._output_owner,
            output_key_owner=self._output_key_owner,
            action_owner=self._action_owner,
            action_key_owner=self._action_key_owner,
            compose_owner=self._compose_owner,
            transform_owner=self._transform_owner,
            witness_owner=self._witness_owner,
            semantic_identity_owner=self._semantic_identity_owner,
            semantic_identity_issued_owner=self._semantic_identity_issued_owner,
            residual_backing=self._residuals,
            residual_key_backing=self._residual_keys,
            output_backing=self._outputs,
            output_key_backing=self._output_keys,
            action_backing=self._actions,
            action_key_backing=self._action_keys,
            compose_backing=self._compose,
            transform_backing=self._transforms,
            witness_backing=self._witnesses,
            semantic_identity_backing=self._semantic_identities,
            semantic_identity_issued_backing=self._semantic_identity_issued,
            residuals=tuple(self._residuals),
            residual_keys=MappingProxyType(dict(self._residual_keys.items())),
            outputs=tuple(self._outputs),
            output_keys=MappingProxyType(dict(self._output_keys.items())),
            actions=tuple(self._actions),
            action_keys=MappingProxyType(dict(self._action_keys.items())),
            compositions=MappingProxyType(dict(self._compose.items())),
            transforms=MappingProxyType(dict(self._transforms.items())),
            witnesses=MappingProxyType(dict(self._witnesses.items())),
            semantic_identities=MappingProxyType(
                dict(self._semantic_identities.items())
            ),
            semantic_identity_issued=MappingProxyType(
                dict(self._semantic_identity_issued.items())
            ),
        )

    def audit_action_record_is_exact(self, index: int, action: object) -> bool:
        """Recompute an indexed action row against its canonical interners."""
        if type(index) is not int or not 0 <= index < len(self._actions):
            return False
        if type(action) is not ReverseFieldAction:
            return False
        try:
            action.geometry.__post_init__()
            block = self.innovation_block(action)
            expected_id = FieldCellActionID(self.owner, self._ACTION_KIND, index)
            valid = (
                action.base == self._base
                and type(action.carry_forward) is CarryFn
                and type(action.carry_backward) is CarryFn
                and type(action.geometry) is ReverseGeometry
                and self._canonical_block(block) == block
                and self.resolve(expected_id) is action
                and self._action_keys.get(
                    self._action_key(
                        action.base,
                        block,
                        action.carry_forward,
                        action.carry_backward,
                        action.residual,
                        action.output,
                        action.geometry,
                    )
                )
                == expected_id
                and type(action.residual) is ReverseDefectClassID
            )
            self._residual_key(action.residual)
            self._output_key(action.output)
            return valid
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            return False

    def audit_composition_is_exact(
        self,
        before: FieldCellActionID,
        after: FieldCellActionID,
        result: FieldCellActionID,
    ) -> bool:
        """Recompute a cached parent action without publishing new records."""
        try:
            first, second, actual = (
                self.resolve(before),
                self.resolve(after),
                self.resolve(result),
            )
            block = self._canonical_block(
                self.innovation_block(first).then(self.innovation_block(second))
            )
            valid = (
                actual.base == first.base == second.base
                and actual.radial == block.radial
                and actual.innovation == block.innovation
                and actual.carry_forward
                is compose_carry_fn(second.carry_forward, first.carry_forward)
                and actual.carry_backward
                is compose_carry_fn(second.carry_backward, first.carry_backward)
                and actual.geometry == first.geometry.then(second.geometry)
                and self._compose.get((before, after)) == result
            )
            residual_key = self._residual_compose(
                self._residual_key(first.residual),
                self._residual_key(second.residual),
            )
            self._validate_semantic_key(residual_key)
            valid &= self._residual_keys.get(residual_key) == actual.residual
            if self._coordinate_programs is None:
                output_key = self._output_compose(
                    self._output_key(first.output), self._output_key(second.output)
                )
                self._validate_semantic_key(output_key)
                valid &= self._output_keys.get(output_key) == actual.output
            else:
                from number_compiler.sequences.reverse_add.coordinate_program import (
                    ReverseCoordinateProgram,
                )

                before_program = self._coordinate_programs.resolve(first.output)
                after_program = self._coordinate_programs.resolve(second.output)
                actual_program = self._coordinate_programs.resolve(actual.output)
                expected_program = ReverseCoordinateProgram(
                    self._base,
                    before_program.pair_steps + after_program.pair_steps,
                    before_program.normalized or after_program.normalized,
                )
                valid &= (
                    actual_program == expected_program
                    and self._coordinate_programs.audit_program_is_interned(
                        actual_program, actual.output.local_id
                    )
                )
            return bool(valid)
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            return False

    def audit_semantic_identity_is_exact(
        self, source: object, record: SemanticIdentityMemoRecord, issued: object
    ) -> bool:
        """Check one identity cache row against the issued action object."""
        if (
            type(source) is not FieldCellActionID
            or type(record) is not tuple
            or len(record) != 6
            or record is not issued
        ):
            return False
        try:
            action = self.resolve(source)
            if not valid_radial_memo(
                source,
                id(action),
                action.radial,
                record,
                issued,
                self.owner,
                self._ACTION_KIND,
                len(self._actions),
            ):
                return False
            recorded_source, action_seal, radial_seal, identity, digest, behavior = (
                record
            )
            expected_identity = build_radial_identity(action.radial)
            return (
                recorded_source == source
                and action_seal == id(action)
                and radial_seal == (action.radial.no_growth, action.radial.growth)
                and type(identity) is SemanticIdentity
                and identity.digest == digest
                and identity.behavior is behavior
                and identity == expected_identity
                and type(digest) is str
                and type(behavior) is tuple
            )
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            return False

    def audit_transform_is_exact(
        self,
        source: FieldCellActionID,
        transform: ActionTransform,
        result: FieldCellActionID,
    ) -> bool:
        """Recompute a cached transform without interning its components."""
        if (
            self._coordinate_programs is not None
            or type(transform) is not ActionTransform
            or int(transform) & ~3
        ):
            return False
        try:
            source_action = self.resolve(source)
            self.resolve(result)
            if type(self._automorphisms) is not ReverseActionAutomorphisms:
                return False
            (
                block,
                residual_key,
                output_key,
                carry_forward,
                carry_backward,
                geometry,
            ) = self._transformed_components(source_action, transform)
            self._validate_semantic_key(residual_key)
            self._validate_semantic_key(output_key)
            residual = self._residual_keys.get(residual_key)
            output = self._output_keys.get(output_key)
            if residual is None or output is None:
                return False
            action_key = self._action_key(
                source_action.base,
                block,
                carry_forward,
                carry_backward,
                residual,
                output,
                geometry,
            )
            return (
                self._action_keys.get(action_key) == result
                and self._transforms.get((source, transform)) == result
            )
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            return False
