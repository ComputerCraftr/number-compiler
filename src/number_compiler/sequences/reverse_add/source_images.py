"""Source-bound reverse/add images with fused and guarded affine pullbacks."""

from __future__ import annotations

from collections.abc import Callable, Hashable, Iterator
from dataclasses import dataclass
from typing import Final, Literal, cast

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ExactSource,
)
from number_compiler.arithmetic.formula.skew_residue_laws import (
    skew_normalized_digit,
)
from number_compiler.hashlife.execution.field_images import FieldImageID
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageBinding,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.resources.construction_scope import RuntimeConstruction
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.resources.owned_memo import OwnedMemoAuditSnapshot
from number_compiler.sequences.reverse_add.binary_phase import admit as admit_binary
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.q19_punctured_producer import (
    admits_punctured_scheduler_block,
)
from number_compiler.sequences.reverse_add.q19_source_bootstrap import (
    publish_q19_source_root,
)
from number_compiler.sequences.reverse_add.recursive_cutover import (
    ReverseRecursiveOccurrence,
    ReverseRecursiveTemporalCutover,
)
from number_compiler.sequences.reverse_add.small_radix import SmallRadixImage
from number_compiler.sequences.reverse_add.source_actions import (
    ReverseActionArena,
    ReverseActionID,
    ReverseActionNode,
    ReverseSource,
)
from number_compiler.sequences.reverse_add.source_chamber import (
    SameCarryChamberRejected,
    iter_admitted_same_carry_digits,
    validate_same_carry_chamber,
)
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts
from number_compiler.sequences.reverse_add.source_workspace import (
    ReverseSourceImageWorkspace,
)

from .small_radix_source import radix_candidate
from .source_image_projection import ReverseImagePayload as ReverseImagePayload
from .source_image_projection import project as project_image


class ReverseCylinderConstructionUnavailable(ValueError):
    """The requested temporal image needs the unbuilt successor cylinder."""


_CARRY_ACTIONS = tuple(CarryFn)


# The legacy completed-child fallback is bounded. Q3/Q5 long requests use
# source-certified binary phases or the packed small-radix owner.
MAX_COMPLETED_CHILD_FALLBACK_STEPS = 128


REVERSE_SOURCE_IMAGE_SEMANTIC_VERSION: Final[str] = (
    "source-cylinder-v10-small-radix-owner"
)


@dataclass(frozen=True, slots=True)
class ReverseSourceImageAdapterAuditSnapshot:
    """Read-only current authority for source-image payload audits."""

    ledger: ResourceLedger
    actions: ReverseActionArena
    ports: SourceCarryPorts | None
    recursive: ReverseRecursiveTemporalCutover | None
    recursive_construction: OriginalSourceConstruction | None
    recursive_maximum_steps: int
    recursive_source: ExactSource | None
    recursive_occurrences: OwnedMemoAuditSnapshot[int, ReverseRecursiveOccurrence]
    q19_owner: ReversePairQ19OutputOwner | None
    q19_source: ExactSource | None
    radix_outputs: OwnedMemoAuditSnapshot[int, SmallRadixImage] | None
    radix_source: ExactSource | None


class ReverseSourceImageAdapter(SourceBoundImageAdapter):
    family = "reverse-add"
    semantic_version = REVERSE_SOURCE_IMAGE_SEMANTIC_VERSION

    def __init__(
        self, actions: ReverseActionArena, *, shared_cache: bool = False
    ) -> None:
        self.shared_cache = shared_cache
        self.actions = actions
        self.ledger = actions.ledger
        self._ports: SourceCarryPorts | None = None
        self._recursive: ReverseRecursiveTemporalCutover | None = None
        self._recursive_construction: OriginalSourceConstruction | None = None
        self._recursive_maximum_steps = 0
        with RuntimeConstruction(self.ledger):
            recursive_owner = self.ledger.register(
                f"reverse-source-recursive-occurrences-{self.ledger.owner_count}",
                "reverse_recursive_occurrence_binding",
            )
            self._recursive_occurrences: OwnedMemo[int, ReverseRecursiveOccurrence] = (
                OwnedMemo(self.ledger, recursive_owner)
            )
        self._recursive_source: ExactSource | None = None
        self._q19_owner: ReversePairQ19OutputOwner | None = None
        self._q19_source: ExactSource | None = None
        self._radix_outputs: OwnedMemo[int, SmallRadixImage] | None = None
        self._radix_source: ExactSource | None = None

    def ports(self, source: ExactSource) -> SourceCarryPorts:
        """One source-bound spatial projection shared by every consumer."""
        ports = self._ports
        if ports is None:
            ports = SourceCarryPorts(source, self.ledger)
            self._ports = ports
        ports.check_source(source)
        return ports

    @property
    def published_ports(self) -> SourceCarryPorts | None:
        """Read the already-published source-bound port owner without creating it."""
        return self._ports

    def audit_snapshot(self) -> ReverseSourceImageAdapterAuditSnapshot:
        """Return the current source/occurrence owners without constructing them."""
        return ReverseSourceImageAdapterAuditSnapshot(
            ledger=self.ledger,
            actions=self.actions,
            ports=self._ports,
            recursive=self._recursive,
            recursive_construction=self._recursive_construction,
            recursive_maximum_steps=self._recursive_maximum_steps,
            recursive_source=self._recursive_source,
            recursive_occurrences=self._recursive_occurrences.audit_snapshot(),
            q19_owner=self._q19_owner,
            q19_source=self._q19_source,
            radix_outputs=None
            if self._radix_outputs is None
            else self._radix_outputs.audit_snapshot(),
            radix_source=self._radix_source,
        )

    def prepare_recursive_authority(
        self,
        source: ExactSource,
        steps: int,
        construction: OriginalSourceConstruction | None = None,
    ) -> None:
        """Authorize the immutable padded pair source before any point demand.

        This allocates no source tree.  It only captures caller-supplied source
        authority so a later rejected same-carry demand can construct its exact
        pair geometry without minting authority inside the point callback.
        """
        if type(source) is not ExactSource or type(steps) is not int or steps < 1:
            raise ValueError("reverse recursive authority requires source and horizon")
        if source.base == 10:
            return
        if self._recursive_construction is not None:
            self._recursive_construction.validate_source()
            if (
                self._recursive_maximum_steps != steps
                or self._recursive_source is not source
            ):
                raise ValueError(
                    "reverse recursive authority source or horizon changed"
                )
            return
        digits = source.digits
        width = len(digits)
        blank = 2 * source.base - 1
        required = max(1, width + steps)
        extent = 1 << ((required - 1).bit_length())
        if construction is None:
            self.ledger.bump(
                _reverse_add_keys.REVERSE_SOURCE_PAIR_AUTHORITY_CONSTRUCTION_SYMBOLS,
                width,
            )
            pair = tuple(digits[i] + digits[width - 1 - i] for i in range(width))
            construction = OriginalSourceConstruction(
                ExactSource(
                    pair,
                    source.base,
                    "reverse-add-pair",
                    blank,
                    extent,
                    2 * source.base,
                )
            )
        else:
            self.ledger.bump(
                _reverse_add_keys.REVERSE_SOURCE_PAIR_AUTHORITY_VALIDATION_SYMBOLS,
                width,
            )
            pair_source = construction.validate_source()
            if (
                pair_source.base != source.base
                or pair_source.orbit != "reverse-add-pair"
                or pair_source.blank != blank
                or pair_source.extent != extent
                or pair_source.alphabet_size != 2 * source.base
                or len(pair_source.digits) != width
                or any(
                    pair_source.digits[i] != digits[i] + digits[width - 1 - i]
                    for i in range(width)
                )
            ):
                raise ValueError(
                    "recursive source authority differs from original digits"
                )
        self._recursive_construction = construction
        self._recursive_maximum_steps = steps
        self._recursive_source = source

    def dispose(self) -> None:
        cleanups: list[Callable[[], object]] = []
        if self._ports is not None:
            ports = self._ports
            cleanups.append(
                self._release_field_after_cleanup("_ports", ports, ports.dispose)
            )
        if self._recursive is not None:
            recursive = self._recursive
            cleanups.append(
                self._release_field_after_cleanup(
                    "_recursive", recursive, recursive.dispose
                )
            )
        if self._q19_owner is not None:
            q19_owner = self._q19_owner
            cleanups.append(
                self._release_field_after_cleanup(
                    "_q19_owner", q19_owner, q19_owner.dispose
                )
            )
        if self._radix_outputs is not None:
            cleanups.append(self._radix_outputs.dispose)
        cleanups.append(self._recursive_occurrences.dispose)
        cleanup_all(cleanups)
        self._recursive_source = None
        self._recursive_construction = None

    def clear_query_output(self) -> None:
        """Drop completed Q19 grammar when the scheduler invalidates images."""
        if self._radix_outputs is not None:
            self._radix_outputs.clear()
            self._radix_source = None
        owner = self._q19_owner
        if owner is None:
            return
        owner.dispose()
        if self._q19_owner is owner:
            self._q19_owner = None
            self._q19_source = None

    def _release_field_after_cleanup(
        self,
        field: Literal["_ports", "_recursive", "_q19_owner"],
        resource: object,
        cleanup: Callable[[], object],
    ) -> Callable[[], object]:
        def release() -> None:
            cleanup()
            if getattr(self, field) is resource:
                setattr(self, field, None)
            if field == "_q19_owner":
                self._q19_source = None

        return release

    def _recursive_occurrence(
        self, source: ExactSource, steps: int
    ) -> ReverseRecursiveOccurrence:
        """Construct the rejected-cylinder target from an authenticated pair occurrence.

        The initial D1 pair occurrence is compiled once.  Every later temporal
        block is applied through provider substitution, whose spatial parent joins
        are functions of their two completed child images.
        """
        authority = self._recursive_source
        if authority is not None and (
            authority is not source
            or authority.digits is not source.digits
            or authority.base != source.base
        ):
            raise ValueError("reverse recursive fallback source changed")
        found = self.recursive_for_steps(steps)
        if found is not None:
            self.ledger.bump(_reverse_add_keys.REVERSE_SOURCE_RECURSIVE_OCCURRENCE_HITS)
            return found[1]
        cutover = self._recursive
        if cutover is None:
            construction = self._recursive_construction
            if construction is None or self._recursive_maximum_steps < steps:
                raise ReverseCylinderConstructionUnavailable(
                    "reverse recursive fallback was not authorized before the point request"
                )
            cutover = ReverseRecursiveTemporalCutover(
                self.ledger,
                source.digits,
                base=source.base,
                maximum_steps=self._recursive_maximum_steps,
                source_construction=construction,
            )
            self._recursive = cutover
            self._recursive_source = source
        else:
            if steps > cutover.maximum_steps:
                raise ReverseCylinderConstructionUnavailable(
                    "reverse recursive fallback exceeded its admitted temporal horizon"
                )
        prefix: ReverseRecursiveOccurrence | None = None
        for length, candidate in self._recursive_occurrences.items():
            self.ledger.bump(_reverse_add_keys.REVERSE_SOURCE_COMPLETED_PREFIX_CHECKS)
            if (
                type(length) is not int
                or type(candidate) is not ReverseRecursiveOccurrence
                or candidate.temporal_steps != length
            ):
                raise ValueError("reverse occurrence memo has another duration")
            if length < steps and (prefix is None or length > prefix.temporal_steps):
                prefix = candidate
        occurrence = (
            cutover.pair_image(steps)
            if prefix is None
            else cutover.apply_to_occurrence(prefix, steps - prefix.temporal_steps)
        )
        if prefix is not None:
            self.ledger.bump(
                _reverse_add_keys.REVERSE_SOURCE_COMPLETED_PREFIX_APPLICATIONS
            )
        if occurrence.temporal_steps != steps:
            raise AssertionError((occurrence.temporal_steps, steps))
        self._recursive_occurrences[steps] = occurrence
        self.ledger.bump(
            _reverse_add_keys.REVERSE_SOURCE_RECURSIVE_OCCURRENCE_PUBLICATIONS
        )
        return occurrence

    def recursive_for_steps(
        self, steps: int
    ) -> tuple[ReverseRecursiveTemporalCutover, ReverseRecursiveOccurrence] | None:
        if type(steps) is not int or steps < 1:
            raise ValueError("recursive occurrence requires a positive exact duration")
        occurrence = self._recursive_occurrences.get(steps)
        cutover = self._recursive
        if occurrence is None:
            return None
        if (
            cutover is None
            or type(occurrence) is not ReverseRecursiveOccurrence
            or occurrence.temporal_steps != steps
        ):
            raise ValueError("reverse occurrence memo has another owner or duration")
        cutover.validate_occurrence(occurrence)
        return cutover, occurrence

    def validate_source(self, source: Hashable) -> None:
        if type(source) is not ReverseSource:
            raise TypeError("reverse/add image requires its exact original source")
        self.actions.source(source)

    def validate_action(self, action: Hashable) -> None:
        if type(action) is not ReverseActionID:
            raise TypeError("reverse/add image requires a scoped action ID")
        self.actions.node(action)

    def validate_payload(self, payload: Hashable) -> None:
        if type(payload) is not ReverseImagePayload:
            raise TypeError("reverse/add image has another payload sort")
        steps = self.actions.node(payload.action).steps
        if (
            sum(
                x is not None
                for x in (payload.occurrence, payload.pair_output, payload.radix_output)
            )
            > 1
        ):
            raise ValueError("reverse image cannot carry two completed outputs")
        if payload.radix_output is not None:
            if (
                type(payload.radix_output) is not SmallRadixImage
                or self._radix_outputs is None
                or self._radix_source is None
                or self._radix_outputs.get(steps) is not payload.radix_output
                or self._radix_source.base != payload.radix_output.base
            ):
                raise ValueError("small radix image differs from issued source output")
        if payload.occurrence is not None:
            if type(payload.occurrence) is not FieldImageID:
                raise TypeError("reverse completed payload requires a field image")
            completed = self.recursive_for_steps(steps)
            if completed is None or completed[1].image != payload.occurrence:
                raise ValueError("reverse payload differs from its issued occurrence")
        if payload.pair_output is not None:
            owner = self._q19_owner
            source = self._q19_source
            # Action nodes are source-independent. The enclosing view binds this
            # owner to the exact original source; here validate its issued root.
            if owner is None or source is None:
                raise ValueError("Q19 output payload has no live source owner")
            owner.validate(payload.pair_output)
            if payload.pair_output.temporal_steps != steps:
                raise ValueError("Q19 output and action have different durations")

    def audit_image_binding(
        self,
        binding: SourceImageBinding,
        payload: Hashable,
        failure_prefix: Hashable | None,
    ) -> None:
        """Check published reverse bindings without discovering new images."""
        self._validate_binding(binding, payload, failure_prefix)

    def validate_view(self, view: SourceImageView) -> ReverseImagePayload:
        self._validate_binding(view.binding, view.payload, view.failure_prefix)
        return cast(ReverseImagePayload, view.payload)

    def _validate_binding(
        self,
        binding: SourceImageBinding,
        payload_value: Hashable,
        failure_prefix: Hashable | None,
    ) -> None:
        if type(binding) is not SourceImageBinding:
            raise TypeError("reverse image audit requires its exact binding")
        self.validate_source(binding.source)
        self.validate_payload(payload_value)
        payload = cast(ReverseImagePayload, payload_value)
        steps = self.actions.node(payload.action).steps
        origin = self.actions.source(cast(ReverseSource, binding.source))
        expected_ports: tuple[int, ...]
        expected_precision: int | None
        if payload.radix_output is not None:
            if (
                self._radix_source is not origin
                or origin.base != payload.radix_output.base
            ):
                raise ValueError("small radix output belongs to another source")
            expected_ports = ()
            expected_precision = None
        elif payload.pair_output is not None:
            owner = self._q19_owner
            if origin.base != 10 or owner is None or self._q19_source is not origin:
                raise ValueError("Q19 output belongs to another source")
            if payload.pair_output.temporal_steps != steps:
                raise ValueError("Q19 output and action have different durations")
            expected_ports = ()
            expected_precision = None
        elif payload.occurrence is None:
            if origin.base == 10 and steps > 0:
                raise ValueError(
                    "decimal reverse image has an incomplete Q19 output payload"
                )
            expected_ports = (0,) if steps == 0 else (0, 1) if steps <= 2 else (0, 0)
            expected_precision = len(origin.digits) + (steps if steps <= 2 else 0)
        else:
            expected_ports = ()
            expected_precision = None
        if (
            binding.family != self.family
            or binding.semantic_version != self.semantic_version
            or binding.action != payload.action
            or binding.extent != steps
            or binding.radix != origin.base
            or binding.orientation != 1
            or failure_prefix is not None
            or binding.boundary_ports != expected_ports
            or binding.precision != expected_precision
        ):
            raise ValueError("reverse image action and source binding disagree")

    def _extend_completed(
        self, action: ReverseActionID, source: SourceImageView
    ) -> SourceImageCandidate:
        """Apply a later block to the published provider, never to its seed."""
        payload = self.validate_view(source)
        before_steps = self.actions.node(payload.action).steps
        additional = self.actions.node(action).steps
        completed = self.recursive_for_steps(before_steps)
        if payload.occurrence is None or completed is None:
            raise ReverseCylinderConstructionUnavailable(
                "reverse/add source cylinder has no completed provider occurrence"
            )
        total = before_steps + additional
        cutover, occurrence = completed
        if total > min(cutover.maximum_steps, MAX_COMPLETED_CHILD_FALLBACK_STEPS):
            raise ReverseCylinderConstructionUnavailable(
                "reverse/add completed provider exceeds its admitted temporal horizon"
            )
        cumulative = self.actions.compose(payload.action, action)
        cached = self.recursive_for_steps(total)
        if cached is None:
            target = cutover.apply_to_occurrence(occurrence, additional)
            self._recursive_occurrences[total] = target
        else:
            target = cached[1]
            self.ledger.bump(_reverse_add_keys.REVERSE_SOURCE_COMPLETED_PARENT_HITS)
        self.ledger.bump(
            _reverse_add_keys.REVERSE_SOURCE_COMPLETED_PROVIDER_APPLICATIONS
        )
        return SourceImageCandidate(
            ReverseImagePayload(cumulative, target.image),
            total,
            radix=source.binding.radix,
        )

    def identity_action(self, source: Hashable) -> ReverseActionID:
        self.validate_source(source)
        return self.actions.identity

    def action_children(
        self, action: Hashable
    ) -> tuple[ReverseActionID, ReverseActionID] | None:
        self.validate_action(action)
        node = self.actions.node(cast(ReverseActionID, action))
        if node.before is None or node.after is None:
            return None
        return node.before, node.after

    def compose_actions(self, before: Hashable, after: Hashable) -> ReverseActionID:
        self.validate_action(before)
        self.validate_action(after)
        return self.actions.compose(
            cast(ReverseActionID, before), cast(ReverseActionID, after)
        )

    def admit_source(self, source: Hashable) -> SourceImageCandidate:
        self.validate_source(source)
        exact = self.actions.source(cast(ReverseSource, source))
        return SourceImageCandidate(
            ReverseImagePayload(self.actions.identity),
            0,
            boundary_ports=(0,),
            radix=exact.base,
            precision=len(exact.digits),
        )

    def apply_primitive(
        self, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate:
        self.validate_action(action)
        payload = self.validate_view(source)
        exact = cast(ReverseActionID, action)
        node = self.actions.node(exact)
        if node.steps not in (0, 1):
            raise ValueError("reverse primitive application requires an atomic action")
        if node.steps == 0:
            return SourceImageCandidate(
                payload,
                source.binding.extent,
                boundary_ports=source.binding.boundary_ports,
                radix=source.binding.radix,
                precision=source.binding.precision,
            )
        exact_source = self.actions.source(cast(ReverseSource, source.binding.source))
        if exact_source.base in (2, 3) and (
            payload.radix_output is not None
            or self.actions.node(payload.action).steps + 1
            > MAX_COMPLETED_CHILD_FALLBACK_STEPS
        ):
            return radix_candidate(self, exact, exact_source, payload)
        if exact_source.base == 10:
            if payload.pair_output is None:
                if self.actions.node(payload.action).steps != 0:
                    raise ReverseCylinderConstructionUnavailable(
                        "decimal pair output lost its completed source occurrence"
                    )
                owner = self.q19_output_owner(exact_source)
                pair_output = owner.initial
            else:
                if self._q19_source is not exact_source or self._q19_owner is None:
                    raise ValueError("decimal pair occurrence has another source owner")
                pair_output = self._q19_owner.apply_pair_step(payload.pair_output)
            cumulative = self.actions.compose(payload.action, exact)
            return SourceImageCandidate(
                ReverseImagePayload(cumulative, pair_output=pair_output),
                source.binding.extent + node.steps,
                boundary_ports=(),
                radix=exact_source.base,
                precision=None,
            )
        if cast(ReverseImagePayload, source.payload).occurrence is not None:
            return self._extend_completed(exact, source)
        prior_steps = self.actions.node(
            cast(ReverseImagePayload, source.payload).action
        ).steps
        if node.steps not in (0, 1) or prior_steps + node.steps > 1:
            raise ReverseCylinderConstructionUnavailable(
                "reverse/add primitive application cannot extend an image "
                f"from {prior_steps} to {prior_steps + node.steps} temporal steps"
            )
        cumulative = self.actions.compose(
            cast(ReverseImagePayload, source.payload).action, exact
        )
        origin = self.actions.source(cast(ReverseSource, source.binding.source))
        width = len(origin.digits) + int(node.steps == 1)
        return SourceImageCandidate(
            ReverseImagePayload(cumulative),
            source.binding.extent + node.steps,
            boundary_ports=(0, 1),
            radix=origin.base,
            precision=width,
        )

    def radix_output_store(
        self, origin: ExactSource
    ) -> OwnedMemo[int, SmallRadixImage]:
        if self._radix_outputs is None:
            owner = self.ledger.register(
                f"reverse-small-radix-{self.ledger.owner_count}",
                "reverse_small_radix_output",
            )
            self._radix_outputs = OwnedMemo(
                self.ledger, owner, node_cost=lambda _k, v: v.retained_words
            )
        if self._radix_source is None:
            self._radix_source = origin
        if self._radix_source is not origin:
            raise ValueError("small radix source owner changed")
        return self._radix_outputs

    def q19_output_owner(self, source: ExactSource) -> ReversePairQ19OutputOwner:
        owner = self._q19_owner
        if owner is None:
            owner = ReversePairQ19OutputOwner(
                self.ledger, source.digits, base=source.base
            )
            self._q19_owner = owner
            self._q19_source = source
        elif self._q19_source is not source:
            raise ValueError("decimal pair owner is bound to another source")
        return owner

    def _q19_root_bootstrap(
        self,
        action: ReverseActionID,
        source: SourceImageView,
        origin: ExactSource,
        payload: ReverseImagePayload,
        steps: int,
    ) -> SourceImageCandidate | None:
        """Publish a source-rooted decimal endpoint or a bounded Q19 prefix."""
        result = publish_q19_source_root(
            self.actions,
            self.ledger,
            action,
            payload.action,
            origin,
            steps,
            self.q19_output_owner,
            self.clear_query_output,
            owner_already_published=self._q19_owner is not None,
            shared_cache=self.shared_cache,
        )
        if result is None:
            return None
        cumulative, occurrence = result
        return SourceImageCandidate(
            ReverseImagePayload(cumulative, pair_output=occurrence),
            source.binding.extent + steps,
            radix=origin.base,
            precision=None,
        )

    def apply_composite(
        self,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None:
        self.validate_action(action)
        self.validate_view(source)
        if demand is not None:
            demand.__post_init__()
        origin = self.actions.source(cast(ReverseSource, source.binding.source))
        payload = cast(ReverseImagePayload, source.payload)
        steps = self.actions.node(cast(ReverseActionID, action)).steps
        if steps < 2:
            raise ValueError(
                "reverse composite application requires at least two steps"
            )
        prior = self.actions.node(payload.action).steps
        if origin.base in (2, 3) and (
            payload.radix_output is not None
            or prior + steps > MAX_COMPLETED_CHILD_FALLBACK_STEPS
            or (
                origin.base == 2
                and prior == 0
                and steps >= 3
                and admit_binary(origin.digits, steps) is not None
            )
        ):
            return radix_candidate(self, cast(ReverseActionID, action), origin, payload)
        if origin.base == 10:
            if payload.pair_output is None:
                # Decimal production uses the Q19 completed-output authority
                # from its first composite request. No carry-chamber probe is
                # needed to select this exact output constructor.
                return self._q19_root_bootstrap(
                    cast(ReverseActionID, action), source, origin, payload, steps
                )
            owner = self._q19_owner
            if owner is None or self._q19_source is not origin:
                raise ValueError("punctured block has no matching Q19 source owner")
            if not admits_punctured_scheduler_block(
                steps, payload.pair_output.output_width
            ):
                return None
            pair_output = owner.apply_punctured_pair_block(
                payload.pair_output, steps=2 if steps == 3 else steps
            )
            if steps == 3:
                # The odd tail is one authenticated irreducible leaf,
                # consumed inside the completed-output owner.
                pair_output = owner.apply_pair_step(pair_output)
            cumulative = self.actions.compose(
                payload.action,
                cast(ReverseActionID, action),
            )
            if self.actions.node(cumulative).steps != pair_output.temporal_steps:
                raise ValueError(
                    "punctured pair output and action have different durations"
                )
            self.ledger.bump(
                _reverse_add_keys.REVERSE_SOURCE_PUNCTURED_COMPLETED_CHILD_PUBLICATIONS
            )
            if steps == 3:
                self.ledger.bump(
                    _reverse_add_keys.REVERSE_SOURCE_PUNCTURED_T3_LEAF_APPLICATIONS
                )
            return SourceImageCandidate(
                ReverseImagePayload(cumulative, pair_output=pair_output),
                source.binding.extent + steps,
                radix=origin.base,
                precision=None,
            )
        source_steps = self.actions.node(
            cast(ReverseImagePayload, source.payload).action
        ).steps
        if cast(ReverseImagePayload, source.payload).occurrence is not None:
            return self._extend_completed(cast(ReverseActionID, action), source)
        if source_steps == 0 and steps == 2:
            origin = self.actions.source(cast(ReverseSource, source.binding.source))
            cumulative = self.actions.compose(
                cast(ReverseImagePayload, source.payload).action,
                cast(ReverseActionID, action),
            )
            self.ledger.bump(
                _reverse_add_keys.REVERSE_SOURCE_TWO_STEP_PULLBACK_PUBLICATIONS
            )
            return SourceImageCandidate(
                ReverseImagePayload(cumulative),
                source.binding.extent + 2,
                boundary_ports=(0, 1),
                radix=origin.base,
                precision=len(origin.digits) + 2,
            )
        if source_steps == 0 and steps >= 3:
            origin = self.actions.source(cast(ReverseSource, source.binding.source))
            try:
                validate_same_carry_chamber(
                    origin, steps, self.ledger, ports=self.ports(origin)
                )
            except SameCarryChamberRejected as exc:
                if steps > MAX_COMPLETED_CHILD_FALLBACK_STEPS:
                    raise ReverseCylinderConstructionUnavailable(
                        "reverse/add source cylinder completed-child fallback is "
                        f"bounded to {MAX_COMPLETED_CHILD_FALLBACK_STEPS} temporal steps"
                    ) from exc
                occurrence = self._recursive_occurrence(origin, steps)
                cumulative = self.actions.compose(
                    cast(ReverseImagePayload, source.payload).action,
                    cast(ReverseActionID, action),
                )
                self.ledger.bump(
                    _reverse_add_keys.REVERSE_SOURCE_COMPLETED_CHILD_PUBLICATIONS
                )
                return SourceImageCandidate(
                    ReverseImagePayload(cumulative, occurrence.image),
                    source.binding.extent + steps,
                    boundary_ports=(),
                    radix=origin.base,
                    precision=None,
                )
            cumulative = self.actions.compose(
                cast(ReverseImagePayload, source.payload).action,
                cast(ReverseActionID, action),
            )
            self.ledger.bump(_reverse_add_keys.REVERSE_SOURCE_SAME_CARRY_PUBLICATIONS)
            return SourceImageCandidate(
                ReverseImagePayload(cumulative),
                source.binding.extent + steps,
                boundary_ports=(0, 0),
                radix=origin.base,
                precision=len(origin.digits),
            )
        self.ledger.bump(_reverse_add_keys.REVERSE_CYLINDER_CONSTRUCTION_FAILURES)
        raise ReverseCylinderConstructionUnavailable(
            "reverse/add cannot answer this demand: the successor-closed "
            f"source cylinder for {source_steps + steps} temporal steps "
            "has not been constructed"
        )

    def compose_chronological(
        self,
        action: Hashable,
        source: SourceImageView,
        before: SourceImageView,
        after: SourceImageView,
    ) -> SourceImageCandidate:
        self.validate_action(action)
        original = self.validate_view(source)
        middle = self.validate_view(before)
        final = self.validate_view(after)
        children = self.action_children(action)
        if (
            children is None
            or before.binding.source != source.binding.source
            or after.binding.source != source.binding.source
            or middle.action != self.actions.compose(original.action, children[0])
            or final.action != self.actions.compose(middle.action, children[1])
        ):
            raise ValueError("reverse chronological children have another binding")
        if (
            final.occurrence is None
            and final.pair_output is None
            and final.radix_output is None
        ):
            raise ReverseCylinderConstructionUnavailable(
                "reverse chronology requires a completed final occurrence"
            )
        self.ledger.bump(_reverse_add_keys.REVERSE_SOURCE_COMPLETED_CHRONOLOGICAL_JOINS)
        return SourceImageCandidate(
            final,
            after.binding.extent,
            radix=after.binding.radix,
        )

    def admitted_input_key(
        self, action: Hashable, source: SourceImageView
    ) -> Hashable | None:
        self.validate_action(action)
        payload = self.validate_view(source)
        action_steps = self.actions.node(cast(ReverseActionID, action)).steps
        source_steps = self.actions.node(
            cast(ReverseImagePayload, source.payload).action
        ).steps
        total = source_steps + action_steps
        if (
            total >= 2
            and source_steps != 0
            and payload.occurrence is None
            and payload.pair_output is None
            and payload.radix_output is None
            and not (
                source.binding.radix in (2, 3)
                and total > MAX_COMPLETED_CHILD_FALLBACK_STEPS
            )
        ):
            self.ledger.bump(_reverse_add_keys.REVERSE_CYLINDER_CONSTRUCTION_FAILURES)
            raise ReverseCylinderConstructionUnavailable(
                "reverse/add source cylinder construction is unavailable for "
                f"{total} temporal steps"
            )
        return None

    def transport_reuse(
        self,
        action: Hashable,
        cached_source: SourceImageView,
        cached_result: SourceImageView,
        source: SourceImageView,
    ) -> SourceImageCandidate:
        del action, cached_source, cached_result, source
        raise ValueError("reverse/add images do not admit relative transport")

    def primitive_width(self, source: ExactSource) -> int:
        ports = self.ports(source)
        return ports.width + ports.terminal

    def normalize_pair(self, pair: int, incoming: int, base: int) -> tuple[int, int]:
        transfer = value_carry_fn(pair, base)
        outgoing = apply_carry_fn(transfer, incoming)
        if base == 10:
            domain = _CARRY_ACTIONS.index(transfer)
            digit = skew_normalized_digit(domain, pair % 9, incoming)
            self.ledger.bump(
                _reverse_add_keys.REVERSE_SOURCE_MOD9_DIGIT_RECONSTRUCTIONS
            )
        else:
            digit = pair + incoming - base * outgoing
            self.ledger.bump(
                _reverse_add_keys.REVERSE_SOURCE_RADIX_DIGIT_RECONSTRUCTIONS
            )
        return outgoing, digit

    def iter_second_digits(self, source: ExactSource) -> Iterator[int]:
        """Emit D2 with one forward carry over the pulled pair-field stream."""
        ports = self.ports(source)
        carry = 0
        for pair in ports.iter_second_pairs():
            carry, digit = self.normalize_pair(pair, carry, source.base)
            self.ledger.bump(_reverse_add_keys.REVERSE_SOURCE_SECOND_STEP_COORDINATES)
            yield digit
        if carry:
            yield carry

    def second_digit(self, source: ExactSource, position: int) -> int:
        ports = self.ports(source)
        width = ports.width + ports.terminal
        if position == width:
            carry = ports.second_carry(width)
            if not carry:
                raise IndexError(position)
            return carry
        if not 0 <= position < width:
            raise IndexError(position)
        _, digit = self.normalize_pair(
            ports.second_pair(position), ports.second_carry(position), source.base
        )
        self.ledger.bump(_reverse_add_keys.REVERSE_SOURCE_SECOND_STEP_COORDINATES)
        return digit

    def iter_same_carry_digits(self, source: ExactSource, steps: int) -> Iterator[int]:
        """Consume the chamber already checked by image admission."""
        ports = self.ports(source)
        yield from iter_admitted_same_carry_digits(ports, steps)

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
        return project_image(self, image, demand)

    def iter_primitive_digits(self, source: ExactSource) -> Iterator[int]:
        """Stream one physical carry over original source pairs in LSD order."""
        ports = self.ports(source)
        carry = 0
        for position in range(ports.width):
            carry, digit = self.normalize_pair(ports.pair(position), carry, source.base)
            self.ledger.bump(_reverse_add_keys.REVERSE_SOURCE_CARRY_COORDINATES)
            yield digit
        if carry:
            yield 1

    def first_failure(self, image: SourceImageView) -> None:
        self.validate_view(image)


__all__ = [
    "ReverseActionArena",
    "ReverseActionID",
    "ReverseActionNode",
    "ReverseCylinderConstructionUnavailable",
    "ReverseSource",
    "ReverseSourceImageAdapter",
    "ReverseSourceImageWorkspace",
]
