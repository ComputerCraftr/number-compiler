"""Complete primitive interfaces and reduced parametric finite functions.

Only primitive boundary domains are enumerated. Composed interfaces stay in
factored decision diagrams; no spatial word or temporal trajectory is stored.
"""

from __future__ import annotations

from collections.abc import Mapping, MutableMapping, Sequence
from dataclasses import dataclass, field
from types import MappingProxyType
from typing import Literal, Protocol, cast

from number_compiler.arithmetic.contracts.block_effect import (
    BlockEffect,
    BoundarySide,
    BoundaryState,
    _effect_key,
)
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
    TransferSummaryID,
)
from number_compiler.arithmetic.contracts.semantic_identity import (
    SemanticIdentity,
    SemanticIdentityDomain,
    SemanticIdentityValidator,
)
from number_compiler.arithmetic.functions.finite_port_action import (
    FinitePortActionArena,
    PortVariable,
)
from number_compiler.arithmetic.radix_division import SymbolicBinaryDivisionEffect
from number_compiler.hashlife.actions.diamond_storage_snapshot import (
    DiamondKernelStorageSnapshot,
)
from number_compiler.hashlife.execution.tile_execution_adapter import FamilyTileHooks
from number_compiler.hashlife.interfaces.primitive_behavior import (
    MAX_PRIMITIVE_BEHAVIOR_TABLE_ENTRIES,
    CertifiedLocalSymmetry,
    LocalSymmetryWitness,
    PrimitiveBehaviorQuotient,
    PrimitiveBehaviorWork,
    capture_primitive_behavior_with_validator,
    certify_local_symmetry,
    identity_symmetry,
    minimize_primitive_behavior_with_validator,
    primitive_behavior_table_slots,
)
from number_compiler.hashlife.observation.diamond_observers import NonblankBlockEffect
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.owned_memo import OwnedMemoAuditSnapshot
from number_compiler.resources.stores import LedgerList


class _BoundedBoundaryUniverse(Protocol):
    def boundary_universe(
        self,
        side: BoundarySide,
        *,
        max_states: int | None = None,
    ) -> tuple[BoundaryState, ...] | None: ...


@dataclass(frozen=True, slots=True)
class PrimitiveKernel:
    """Immutable original operator and its complete primitive port domains."""

    effect: BlockEffect
    left: Sequence[BoundaryState]
    right: Sequence[BoundaryState]
    ledger: ResourceLedger
    behavior: PrimitiveBehaviorQuotient | None = None
    family_hooks: FamilyTileHooks | None = field(
        default=None, repr=False, compare=False
    )

    @property
    def base(self) -> int:
        return self.effect.base

    @property
    def blank(self) -> int:
        return self.effect.blank

    @property
    def left_count(self) -> int:
        if type(self.effect) is SymbolicBinaryDivisionEffect:
            return 1
        return len(self.left)

    @property
    def right_count(self) -> int:
        if type(self.effect) is SymbolicBinaryDivisionEffect:
            return 2 * self.effect.radix
        return len(self.right)

    def _domain_count(self, side: BoundarySide) -> int:
        if type(side) is not BoundarySide:
            raise ValueError("invalid primitive boundary side")
        return self.left_count if side is BoundarySide.LEFT else self.right_count

    def domain(self, side: BoundarySide) -> Sequence[BoundaryState]:
        if type(side) is not BoundarySide:
            raise ValueError("invalid primitive boundary side")
        return self.left if side is BoundarySide.LEFT else self.right

    def encode(self, side: BoundarySide, state: BoundaryState) -> int:
        """Map an original primitive state into its canonical integer domain."""
        domain = self.domain(side)
        count = self._domain_count(side)
        if type(state) is int and 0 <= state < count:
            if type(self.effect) is SymbolicBinaryDivisionEffect:
                return state
            if domain[state] == state:
                return state
        if type(self.effect) is SymbolicBinaryDivisionEffect:
            raise ValueError("symbolic division state lies outside its port")
        return domain.index(state)

    def decode(self, side: BoundarySide, state: int) -> BoundaryState:
        domain = self.domain(side)
        self.validate_atom_index(state, self._domain_count(side))
        if type(self.effect) is SymbolicBinaryDivisionEffect:
            return state
        return domain[state]

    def initial(self, side: BoundarySide) -> int:
        return self.encode(side, self.effect.initial(side))

    def advance(self, side: BoundarySide, state: int, symbol: int) -> int:
        domain = self.domain(side)
        self.validate_atom_index(state, self._domain_count(side))
        self.validate_atom_index(symbol, self.blank + 1)
        self.ledger.bump(_interfaces_keys.DIAMOND_KERNEL_TRANSITION_EVALUATIONS)
        self.ledger.bump(_shared_keys.PRIMITIVE_TRANSITION_EVALUATIONS)
        behavior = self.behavior
        if behavior is not None:
            classes = (
                behavior.left_classes
                if side is BoundarySide.LEFT
                else behavior.right_classes
            )
            transitions = (
                behavior.left_transitions
                if side is BoundarySide.LEFT
                else behavior.right_transitions
            )
            representatives = (
                behavior.left_representatives
                if side is BoundarySide.LEFT
                else behavior.right_representatives
            )
            if len(representatives) == len(domain):
                return representatives[transitions[classes[state]][symbol]]
        if type(self.effect) is SymbolicBinaryDivisionEffect:
            return self.effect.advance(side, state, symbol)
        return self.encode(side, self.effect.advance(side, domain[state], symbol))

    def emit(self, left: int, symbol: int, right: int) -> int:
        self.validate_atom_index(left, self.left_count)
        self.validate_atom_index(right, self.right_count)
        self.validate_atom_index(symbol, self.blank + 1)
        self.ledger.bump(_interfaces_keys.DIAMOND_KERNEL_OUTPUT_EVALUATIONS)
        self.ledger.bump(_shared_keys.PRIMITIVE_OUTPUT_EVALUATIONS)
        if type(self.effect) is SymbolicBinaryDivisionEffect:
            result = self.effect.emit(left, symbol, right)
        elif self.behavior is None:
            result = self.effect.emit(self.left[left], symbol, self.right[right])
        else:
            result = self.behavior.output(
                self.behavior.left_classes[left],
                symbol,
                self.behavior.right_classes[right],
            )
        self.validate_atom_index(result, self.blank + 1)
        return self.ledger.observe_arithmetic(result)

    def observe(self, left: int, symbol: int, right: int) -> tuple[int, ...]:
        """Return occurrence metadata which is not implied by output digits.

        A family may attach a source-owned occurrence observer. Generic
        kernels default to the identity occurrence cocycle.
        """
        self.validate_atom_index(left, self.left_count)
        self.validate_atom_index(right, self.right_count)
        self.validate_atom_index(symbol, self.blank + 1)
        self.ledger.bump(_interfaces_keys.PRIMITIVE_OCCURRENCE_OBSERVATION_EVALUATIONS)
        if self.behavior is not None:
            return self.behavior.observation(
                self.behavior.left_classes[left],
                symbol,
                self.behavior.right_classes[right],
            )
        hooks = self.family_hooks
        if hooks is not None and hooks.owns_effect(self.effect):
            return hooks.observe_primitive(self, left, symbol, right)
        return 0, 0, 0

    def is_absorbing(self, side: BoundarySide, state: int) -> bool:
        """Check the complete primitive alphabet, never a sampled input word."""
        self.validate_atom_index(state, self._domain_count(side))
        self.ledger.bump(_interfaces_keys.DIAMOND_KERNEL_ABSORBER_CHECKS)
        if type(self.effect) is NonblankBlockEffect:
            return state == 1
        return all(
            self.advance(side, state, symbol) == state
            for symbol in range(self.blank + 1)
        )

    @staticmethod
    def validate_atom_index(value: int, size: int) -> None:
        if type(value) is not int or not 0 <= value < size:
            raise ValueError("value outside primitive interface")


@dataclass(frozen=True, slots=True)
class FiniteExpression:
    """Factored Boolean functions encoding one finite interface value."""

    domain: int
    bits: tuple[TransferSummaryID, ...]

    def __post_init__(self) -> None:
        if type(self.domain) is not int or not 1 <= self.domain <= 1 << 64:
            raise ValueError("finite values require a positive at-most-64-bit domain")
        if (
            type(self.bits) is not tuple
            or len(self.bits) != (self.domain - 1).bit_length()
        ):
            raise ValueError("finite value has the wrong component count")
        for bit in self.bits:
            if (
                type(bit) is not TransferSummaryID
                or bit.kind != "finite-port-function"
                or bit.owner is not self.bits[0].owner
            ):
                raise ValueError("finite components require one scoped decision arena")


@dataclass(frozen=True, slots=True)
class KernelApplication:
    kernel: ActionProgramID
    operation: Literal["advance", "emit"]
    side: int
    arguments: tuple[TransferSummaryID, ...]


@dataclass(frozen=True, slots=True)
class KernelTemplateKey:
    kernel: ActionProgramID
    operation: Literal["advance", "emit"]
    side: int
    constants: tuple[int | None, ...]


@dataclass(frozen=True, slots=True)
class KernelTemplate:
    parameters: tuple[TransferSummaryID, ...]
    function: TransferSummaryID


class DiamondKernelArena:
    """Canonical primitive IDs and extensional parametric finite action IDs."""

    def __init__(self, ledger: ResourceLedger | None = None) -> None:
        self.ledger = ResourceLedger() if ledger is None else ledger
        self.family_hooks: FamilyTileHooks | None = None
        self.owner = ArenaToken("diamond-kernels")
        self.ledger.register_execution_root(self)
        prefix = f"diamond-kernel-{len(self.ledger.inventory())}"
        self._kernel_owner = self.ledger.register(
            prefix + "-primitives", "finite_kernel"
        )
        self._key_owner = self.ledger.register(
            prefix + "-primitive-ids", "finite_kernel_interner"
        )
        self._expression_owner = self.ledger.register(
            prefix + "-expressions", "canonical_transfer"
        )
        self._expression_key_owner = self.ledger.register(
            prefix + "-expression-ids", "transfer_interner"
        )
        self._kernels: LedgerList[PrimitiveKernel] = self.ledger.make_list(
            self._kernel_owner
        )
        self._kernel_ids: MutableMapping[object, ActionProgramID] = (
            self.ledger.make_dict(self._key_owner)
        )
        self._expressions: LedgerList[FiniteExpression] = self.ledger.make_list(
            self._expression_owner
        )
        self._expression_ids: MutableMapping[FiniteExpression, TransferSummaryID] = (
            self.ledger.make_dict(self._expression_key_owner)
        )
        self._behavior_owner = self.ledger.register(
            prefix + "-behavioral-quotients",
            "primitive_behavioral_quotient",
        )
        self._behavioral_quotients: MutableMapping[int, PrimitiveBehaviorQuotient] = (
            self.ledger.make_dict(self._behavior_owner)
        )
        self._symmetry_owner = self.ledger.register(
            prefix + "-local-symmetries",
            "primitive_behavioral_symmetry",
        )
        self._local_symmetries: MutableMapping[int, CertifiedLocalSymmetry] = (
            self.ledger.make_dict(self._symmetry_owner)
        )
        self.ledger.register_container(
            self._behavior_owner,
            self._behavioral_quotients,
            node_count=lambda: len(self._behavioral_quotients),
            payloads=lambda: self._behavioral_quotients.items(),
        )
        self.ledger.register_container(
            self._symmetry_owner,
            self._local_symmetries,
            node_count=lambda: len(self._local_symmetries),
            payloads=lambda: self._local_symmetries.items(),
        )
        application_owner = self.ledger.register(prefix + "-applications", "query_memo")
        self._applications: OwnedMemo[KernelApplication, TransferSummaryID] = OwnedMemo(
            self.ledger,
            application_owner,
            evictable=True,
            composition_entries=True,
        )
        template_owner = self.ledger.register(
            prefix + "-templates", "finite_kernel_template"
        )
        self._templates: OwnedMemo[KernelTemplateKey, KernelTemplate] = OwnedMemo(
            self.ledger,
            template_owner,
            nodes_per_entry=1,
        )
        self.functions = FinitePortActionArena(self.ledger)

    def bind_family_hooks(self, hooks: FamilyTileHooks | None) -> None:
        if hooks is not None and type(hooks) is not FamilyTileHooks:
            raise TypeError("kernel arena requires canonical family hooks")
        if self.family_hooks is not None and self.family_hooks is not hooks:
            raise ValueError("kernel arena is already bound to another family adapter")
        self.family_hooks = hooks

    def intern(
        self,
        effect: BlockEffect,
        *,
        symmetry_witnesses: tuple[LocalSymmetryWitness, ...] | None = None,
    ) -> ActionProgramID:
        # Admission precedes all key lookups; a forged alias is not a kernel.
        common = (
            BaseBlockEffect,
            FiniteBlockEffect,
            DigitNormalizeBlockEffect,
            NonblankBlockEffect,
            SymbolicBinaryDivisionEffect,
        )
        if type(effect) not in common:
            if self.family_hooks is not None and self.family_hooks.owns_effect(effect):
                # The compiler already admitted this immutable occurrence.
                # Validate its family law without replacing the object bound
                # by the chronological composition certificate.
                self.family_hooks.clone(effect)
            elif self.family_hooks is not None and self.family_hooks.owns_compatibility(
                effect
            ):
                self.family_hooks.validate_compatibility(effect)
            else:
                raise TypeError(
                    "only complete immutable primitive kernels are admitted"
                )
        if type(effect) is SymbolicBinaryDivisionEffect:
            # Retain a canonical frozen definition instead of the caller's
            # instance.  Even deliberate ``object.__setattr__`` corruption of
            # that instance cannot alter an admitted kernel after interning.
            effect = SymbolicBinaryDivisionEffect(effect.radix)
        if (
            type(effect.base) is not int
            or not 2 <= effect.base <= 1 << 64
            or type(effect.blank) is not int
            or not 1 <= effect.blank < 1 << 64
        ):
            raise ValueError(
                "primitive alphabet exceeds the supported 64-bit interface"
            )
        if type(effect) is FiniteBlockEffect and not (
            1 <= effect.left_count <= 1 << 64 and 1 <= effect.right_count <= 1 << 64
        ):
            raise ValueError("primitive states exceed the supported 64-bit interface")
        key = _effect_key(effect)
        found = self._kernel_ids.get(key)
        if found is not None:
            if symmetry_witnesses is not None:
                expected = certify_local_symmetry(
                    self.behavioral_quotient(found),
                    symmetry_witnesses,
                )
                if self.local_symmetry(found) != expected:
                    raise ValueError(
                        "primitive kernel already has another symmetry certificate"
                    )
            return found
        compatibility_artifact = (
            self.family_hooks is not None
            and self.family_hooks.owns_compatibility(effect)
        )
        has_runtime_behavior = (
            not (type(effect) is FiniteBlockEffect and effect.exponent > 1)
            and not compatibility_artifact
            and type(effect) is not SymbolicBinaryDivisionEffect
        )
        if (
            has_runtime_behavior
            and primitive_behavior_table_slots(1, 1, effect.blank + 1)
            > MAX_PRIMITIVE_BEHAVIOR_TABLE_ENTRIES
        ):
            raise ValueError(
                "primitive behavioral table exceeds its fixed admission bound"
            )
        if type(effect) is FiniteBlockEffect and has_runtime_behavior:
            table_entries = primitive_behavior_table_slots(
                effect.left_count,
                effect.right_count,
                effect.blank + 1,
            )
            if table_entries > MAX_PRIMITIVE_BEHAVIOR_TABLE_ENTRIES:
                raise ValueError(
                    "primitive behavioral table exceeds its fixed admission bound"
                )
        left = self._domain(effect, BoundarySide.LEFT)
        right = self._domain(effect, BoundarySide.RIGHT)
        if left is None or right is None:
            raise ValueError(
                "primitive behavioral table exceeds its fixed admission bound"
            )
        if not left or not right:
            raise ValueError("primitive boundary interface is incomplete")
        left_count = 1 if type(effect) is SymbolicBinaryDivisionEffect else len(left)
        right_count = (
            2 * effect.radix
            if type(effect) is SymbolicBinaryDivisionEffect
            else len(right)
        )
        table_entries = primitive_behavior_table_slots(
            left_count,
            right_count,
            effect.blank + 1,
        )
        if (
            has_runtime_behavior
            and table_entries > MAX_PRIMITIVE_BEHAVIOR_TABLE_ENTRIES
        ):
            raise ValueError(
                "primitive behavioral table exceeds its fixed admission bound"
            )
        left_owner = self.ledger.register(
            f"diamond-primitive-{self._kernel_owner}-{len(self._kernels)}-left",
            "finite_port",
        )
        right_owner = self.ledger.register(
            f"diamond-primitive-{self._kernel_owner}-{len(self._kernels)}-right",
            "finite_port",
        )
        compact_domain = type(effect) is SymbolicBinaryDivisionEffect
        left_charge = 1 if compact_domain else len(left)
        right_charge = 1 if compact_domain else len(right)
        reservations = [
            (self._kernel_owner, 1, 1),
            (self._key_owner, 1, 0),
            (left_owner, left_charge, left_charge),
            (right_owner, right_charge, right_charge),
        ]
        if has_runtime_behavior:
            reservations.append((self._behavior_owner, 1, 1))
            reservations.append((self._symmetry_owner, 1, 1))
        self.ledger.reserve_many(tuple(reservations))
        identity_validator: SemanticIdentityValidator | None = None
        try:
            # Primitive domains are immutable values and may be shared by the
            # effect implementation or by CPython's tuple constants.  The
            # retained stores nevertheless belong to this kernel alone.  Give
            # each store a fresh bounded container identity after reserving it.
            # Symbolic division still materializes only its one representative,
            # never its conceptual ``2 * radix`` right domain.
            left = tuple(item for item in left)
            right = tuple(item for item in right)
            raw_kernel = PrimitiveKernel(
                effect, left, right, self.ledger, family_hooks=self.family_hooks
            )
            behavior: PrimitiveBehaviorQuotient | None = None
            symmetry: CertifiedLocalSymmetry | None = None
            if has_runtime_behavior:
                identity_validator = SemanticIdentityValidator()
                source = SemanticIdentity.from_validator(
                    SemanticIdentityDomain.PRIMITIVE_BEHAVIOR,
                    ("primitive-behavior", key),
                    identity_validator,
                )
                work = PrimitiveBehaviorWork()
                try:
                    table = capture_primitive_behavior_with_validator(
                        raw_kernel,
                        source,
                        validator=identity_validator,
                    )
                    behavior = minimize_primitive_behavior_with_validator(
                        table,
                        work=work,
                        validator=identity_validator,
                    )
                finally:
                    self.ledger.bump(
                        _interfaces_keys.PRIMITIVE_BEHAVIOR_REFINEMENT_OBSERVATION_CHECKS,
                        work.observation_checks,
                    )
                    self.ledger.bump(
                        _interfaces_keys.PRIMITIVE_BEHAVIOR_REFINEMENT_SUCCESSOR_CHECKS,
                        work.successor_checks,
                    )
                symmetry = (
                    identity_symmetry(behavior)
                    if symmetry_witnesses is None
                    else certify_local_symmetry(behavior, symmetry_witnesses)
                )
            if identity_validator is not None:
                identity_validator.finish()
            kernel = PrimitiveKernel(
                effect,
                raw_kernel.left,
                raw_kernel.right,
                self.ledger,
                behavior,
                self.family_hooks,
            )
        except BaseException:
            if identity_validator is not None:
                identity_validator.discard()
            for owner, entries, nodes in reversed(reservations):
                self.ledger.release(owner, entries=entries, nodes=nodes)
            self.ledger.bump(_interfaces_keys.PRIMITIVE_BEHAVIORAL_QUOTIENT_FAILURES)
            raise
        self.ledger.register_container(
            left_owner,
            kernel.left,
            node_count=lambda: left_charge,
            payloads=lambda: () if compact_domain else kernel.left,
        )
        self.ledger.register_container(
            right_owner,
            kernel.right,
            node_count=lambda: right_charge,
            payloads=lambda: () if compact_domain else kernel.right,
        )
        handle = ActionProgramID(self.owner, "diamond-kernel", len(self._kernels))
        self._kernels.append(kernel)
        self._kernel_ids[key] = handle
        if behavior is not None:
            class_count = behavior.left_count + behavior.right_count
            self._behavioral_quotients[handle.local_id] = behavior
            if symmetry is None:
                raise AssertionError(
                    "runtime primitive omitted its symmetry certificate"
                )
            self._local_symmetries[handle.local_id] = symmetry
            self.ledger.bump(_interfaces_keys.PRIMITIVE_BEHAVIORAL_QUOTIENT_EVALUATIONS)
            self.ledger.bump(_interfaces_keys.PRIMITIVE_BEHAVIORAL_CLASSES, class_count)
            self.ledger.bump(
                _interfaces_keys.PRIMITIVE_BEHAVIORAL_CLASS_POPULATION,
                class_count,
            )
        self.ledger.bump(
            _interfaces_keys.DIAMOND_PRIMITIVE_DOMAIN_STATES,
            left_count + right_count,
        )
        return handle

    def _domain(
        self, effect: BlockEffect, side: BoundarySide
    ) -> Sequence[BoundaryState] | None:
        if type(effect) is SymbolicBinaryDivisionEffect:
            # Cardinality lives in the symbolic effect and PrimitiveKernel's
            # count properties.  Retain only one immutable representative;
            # a Python container cannot expose a length above ``sys.maxsize``
            # and production must not own one state object per remainder.
            return (0,)
        if type(effect) is DigitNormalizeBlockEffect:
            return effect.boundary_universe(side)
        if type(effect) is not BaseBlockEffect:
            return cast(_BoundedBoundaryUniverse, effect).boundary_universe(
                side,
                max_states=MAX_PRIMITIVE_BEHAVIOR_TABLE_ENTRIES,
            )
        # The reverse primitive declares its reachable universe by finite BFS.
        # Keep its discovery work visible instead of hiding it in metadata.
        values: list[BoundaryState] = [effect.initial(side)]
        identities = {values[0]: 0}
        cursor = 0
        while cursor < len(values):
            state = values[cursor]
            cursor += 1
            for symbol in range(effect.blank + 1):
                self.ledger.bump(
                    _interfaces_keys.DIAMOND_KERNEL_DOMAIN_TRANSITION_EVALUATIONS
                )
                target = effect.advance(side, state, symbol)
                if target not in identities:
                    if len(values) >= MAX_PRIMITIVE_BEHAVIOR_TABLE_ENTRIES:
                        return None
                    identities[target] = len(values)
                    values.append(target)
        return tuple(values)

    def storage_is_registered(self, actual: Mapping[int, object]) -> bool:
        return (
            actual.get(self._kernel_owner) is self._kernels
            and actual.get(self._expression_owner) is self._expressions
        )

    def audit_snapshot(self) -> DiamondKernelStorageSnapshot:
        return DiamondKernelStorageSnapshot(
            self._kernel_owner,
            self._expression_owner,
            id(self._kernels),
            id(self._expressions),
            self._kernels.audit_view(),
            self._expressions.audit_view(),
        )

    def template_audit_snapshot(
        self,
    ) -> OwnedMemoAuditSnapshot[KernelTemplateKey, KernelTemplate]:
        """Expose retained primitive templates through the memo audit interface."""
        return self._templates.audit_snapshot()

    @property
    def behavioral_quotients(self) -> Mapping[int, PrimitiveBehaviorQuotient]:
        return MappingProxyType(self._behavioral_quotients)

    @property
    def kernel_bindings(self) -> Mapping[object, ActionProgramID]:
        """Read canonical primitive bindings without publishing a new kernel."""
        return self._kernel_ids

    def kernel(self, handle: ActionProgramID) -> PrimitiveKernel:
        if type(handle) is not ActionProgramID:
            raise TypeError("expected primitive kernel ID")
        handle.validate(self.owner, "diamond-kernel", size=len(self._kernels))
        kernel = self._kernels[handle.local_id]
        if type(kernel.effect) is SymbolicBinaryDivisionEffect:
            expected = SymbolicBinaryDivisionEffect(kernel.effect.radix)
            if (
                kernel.effect != expected
                or self._kernel_ids.get(expected.canonical_key()) != handle
            ):
                raise ValueError("symbolic division kernel identity is inconsistent")
        return kernel

    def behavioral_quotient(
        self,
        handle: ActionProgramID,
    ) -> PrimitiveBehaviorQuotient:
        """Return the exact minimal local quotient for one admitted primitive.

        This API is intentionally separate from proof powered-kernel tables.
        Runtime interface admission calls it for primitive leaf laws before a
        parent key is published.  The retained artifact contains only the fixed
        primitive domain and never a temporal power or source occurrence.
        """
        kernel = self.kernel(handle)
        if (
            type(kernel.effect) is FiniteBlockEffect
            and kernel.effect.exponent > 1
            or (
                kernel.family_hooks is not None
                and kernel.family_hooks.owns_compatibility(kernel.effect)
            )
        ):
            raise ValueError(
                "powered proof-machine domains cannot enter runtime behavioral quotients"
            )
        found = self._behavioral_quotients.get(handle.local_id)
        if found is None or kernel.behavior is not found:
            raise AssertionError("runtime primitive omitted its behavioral certificate")
        self.ledger.bump(_interfaces_keys.PRIMITIVE_BEHAVIORAL_QUOTIENT_HITS)
        return found

    def local_symmetry(self, handle: ActionProgramID) -> CertifiedLocalSymmetry:
        """Return the immutable complete local automorphism certificate."""
        self.behavioral_quotient(handle)
        found = self._local_symmetries.get(handle.local_id)
        if found is None:
            raise AssertionError("runtime primitive omitted its symmetry certificate")
        self.ledger.bump(_interfaces_keys.PRIMITIVE_BEHAVIORAL_SYMMETRY_HITS)
        return found

    def expression(self, handle: TransferSummaryID) -> FiniteExpression:
        if type(handle) is not TransferSummaryID:
            raise TypeError("expected finite expression ID")
        handle.validate(
            self.owner, "diamond-finite-expression", size=len(self._expressions)
        )
        return self._expressions[handle.local_id]

    def intern_expression(self, expression: FiniteExpression) -> TransferSummaryID:
        for bit in expression.bits:
            self.functions.resolve_index(bit)
        found = self._expression_ids.get(expression)
        if found is not None:
            self.ledger.bump(_interfaces_keys.FINITE_EXPRESSION_INTERNER_REQUESTS)
            self.ledger.bump(
                _interfaces_keys.FINITE_EXPRESSION_COMPONENT_CHECKS,
                len(expression.bits),
            )
            self.ledger.bump(_interfaces_keys.FINITE_EXPRESSION_INTERNER_HITS)
            return found
        self.ledger.reserve_many(
            ((self._expression_owner, 1, 1), (self._expression_key_owner, 1, 0))
        )
        handle = TransferSummaryID(
            self.owner, "diamond-finite-expression", len(self._expressions)
        )
        self._expressions.append(expression)
        self._expression_ids[expression] = handle
        self.ledger.bump(_interfaces_keys.FINITE_EXPRESSION_INTERNER_REQUESTS)
        self.ledger.bump(
            _interfaces_keys.FINITE_EXPRESSION_COMPONENT_CHECKS,
            len(expression.bits),
        )
        self.ledger.bump(_interfaces_keys.FINITE_EXPRESSION_INTERNER_EVALUATIONS)
        return handle

    def constant(self, domain: int, value: int) -> TransferSummaryID:
        PrimitiveKernel.validate_atom_index(value, domain)
        if type(domain) is not int or not 1 <= domain <= 1 << 64:
            raise ValueError("invalid finite domain")
        return self.intern_expression(
            FiniteExpression(
                domain,
                tuple(
                    self.functions.constant(bool(value & (1 << bit)))
                    for bit in range((domain - 1).bit_length())
                ),
            )
        )

    def variable(self, domain: int, port: PortVariable) -> TransferSummaryID:
        if (
            type(port) is not PortVariable
            or type(domain) is not int
            or not 1 <= domain <= 1 << 64
        ):
            raise ValueError("invalid finite variable")
        return self.intern_expression(
            FiniteExpression(
                domain,
                tuple(
                    self.functions.variable(
                        PortVariable(port.time, port.side, port.role, port.bit + bit)
                    )
                    for bit in range((domain - 1).bit_length())
                ),
            )
        )

    def evaluate(
        self, expression: TransferSummaryID, inputs: Mapping[PortVariable, bool]
    ) -> int:
        node = self.expression(expression)
        value = sum(
            int(self.functions.apply(bit, inputs)) << index
            for index, bit in enumerate(node.bits)
        )
        PrimitiveKernel.validate_atom_index(value, node.domain)
        return value

    def substitute(
        self,
        expression: TransferSummaryID,
        substitutions: Mapping[PortVariable, TransferSummaryID],
    ) -> TransferSummaryID:
        node = self.expression(expression)
        # Replacements are Boolean functions, not finite-expression IDs.
        for variable, value in substitutions.items():
            if type(variable) is not PortVariable:
                raise ValueError("invalid substitution variable")
            self.functions.resolve_index(value)
        return self.intern_expression(
            FiniteExpression(
                node.domain,
                tuple(
                    self.functions.substitute(bit, substitutions) for bit in node.bits
                ),
            )
        )

    def choose(
        self,
        condition: TransferSummaryID,
        yes: TransferSummaryID,
        no: TransferSummaryID,
    ) -> TransferSummaryID:
        first, second = self.expression(yes), self.expression(no)
        self.functions.resolve_index(condition)
        if first.domain != second.domain:
            raise ValueError("finite choice codomains disagree")
        return self.intern_expression(
            FiniteExpression(
                first.domain,
                tuple(
                    self.functions.choose(condition, left, right)
                    for left, right in zip(first.bits, second.bits, strict=True)
                ),
            )
        )

    def advance_expression(
        self,
        kernel: ActionProgramID,
        side: BoundarySide,
        state: TransferSummaryID,
        symbol: TransferSummaryID,
    ) -> TransferSummaryID:
        if type(side) is not BoundarySide:
            raise ValueError("invalid primitive boundary side")
        return self._apply(kernel, "advance", side, (state, symbol))

    def emit_expression(
        self,
        kernel: ActionProgramID,
        left: TransferSummaryID,
        symbol: TransferSummaryID,
        right: TransferSummaryID,
    ) -> TransferSummaryID:
        return self._apply(kernel, "emit", BoundarySide.LEFT, (left, symbol, right))

    def _apply(
        self,
        kernel: ActionProgramID,
        operation: Literal["advance", "emit"],
        side: BoundarySide,
        arguments: tuple[TransferSummaryID, ...],
    ) -> TransferSummaryID:
        primitive = self.kernel(kernel)
        nodes = tuple(self.expression(argument) for argument in arguments)
        domains = (
            (
                primitive.left_count
                if side is BoundarySide.LEFT
                else primitive.right_count,
                primitive.blank + 1,
            )
            if operation == "advance"
            else (primitive.left_count, primitive.blank + 1, primitive.right_count)
        )
        if tuple(node.domain for node in nodes) != domains:
            raise ValueError("primitive expression domains disagree")
        key = KernelApplication(kernel, operation, int(side), arguments)
        self.ledger.bump(_interfaces_keys.DIAMOND_KERNEL_EXPRESSION_REQUESTS)
        found = self._applications.get(key)
        if found is not None:
            self.ledger.bump(_interfaces_keys.DIAMOND_KERNEL_EXPRESSION_HITS)
            return found
        self.ledger.bump(_interfaces_keys.DIAMOND_KERNEL_EXPRESSION_EVALUATIONS)
        # A single variable input is already a bounded primitive slice. Avoid
        # constructing a complete multi-input template for constant workloads.
        nonconstant = sum(any(bit.local_id >= 2 for bit in node.bits) for node in nodes)
        if nonconstant <= 1:
            answer = self._direct(primitive, operation, side, nodes)
        else:
            constants = tuple(
                None
                if any(bit.local_id >= 2 for bit in node.bits)
                else sum(bit.local_id << index for index, bit in enumerate(node.bits))
                for node in nodes
            )
            template = self._template(
                kernel, primitive, operation, side, domains, constants
            )
            replacements: dict[PortVariable, TransferSummaryID] = {}
            for parameter, actual in zip(template.parameters, nodes, strict=True):
                for variable_bit, replacement in zip(
                    self.expression(parameter).bits, actual.bits, strict=True
                ):
                    variable = self.functions.decision_record(variable_bit).variable
                    if variable is None:
                        continue  # This primitive argument was fixed in the template key.
                    replacements[variable] = replacement
            answer = self.substitute(template.function, replacements)
        self._applications[key] = answer
        return answer

    def _template(
        self,
        kernel: ActionProgramID,
        primitive: PrimitiveKernel,
        operation: Literal["advance", "emit"],
        side: BoundarySide,
        domains: tuple[int, ...],
        constants: tuple[int | None, ...],
    ) -> KernelTemplate:
        key = KernelTemplateKey(kernel, operation, int(side), constants)
        self.ledger.bump(_interfaces_keys.DIAMOND_KERNEL_TEMPLATE_REQUESTS)
        found = self._templates.get(key)
        if found is not None:
            self.ledger.bump(_interfaces_keys.DIAMOND_KERNEL_TEMPLATE_HITS)
            return found
        parameters = tuple(
            self.variable(
                domain, PortVariable(0, argument, f"diamond-template-{operation}", 0)
            )
            if constant is None
            else self.constant(domain, constant)
            for argument, (domain, constant) in enumerate(
                zip(domains, constants, strict=True)
            )
        )
        function = self._direct(
            primitive,
            operation,
            side,
            tuple(self.expression(value) for value in parameters),
        )
        template = KernelTemplate(parameters, function)
        self._templates[key] = template
        self.ledger.bump(_interfaces_keys.DIAMOND_KERNEL_TEMPLATE_EVALUATIONS)
        return template

    def _direct(
        self,
        primitive: PrimitiveKernel,
        operation: Literal["advance", "emit"],
        side: BoundarySide,
        nodes: tuple[FiniteExpression, ...],
    ) -> TransferSummaryID:
        from number_compiler.hashlife.interfaces.diamond_truth_function import (
            compile_truth_function,
        )

        return compile_truth_function(self, primitive, operation, side, nodes)
