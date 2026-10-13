"""Source-bound reverse/add images with fused and guarded affine pullbacks."""

from __future__ import annotations

from collections.abc import Hashable, Iterator
from dataclasses import dataclass
from typing import cast

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
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
    SourceImageBinding,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairOutputOccurrence,
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.recursive_cutover import (
    ReverseRecursiveOccurrence,
    ReverseRecursiveTemporalCutover,
)
from number_compiler.sequences.reverse_add.source_actions import (
    ReverseActionArena,
    ReverseActionID,
    ReverseActionNode,
    ReverseSource,
)
from number_compiler.sequences.reverse_add.source_chamber import (
    SameCarryChamberRejected,
    iter_admitted_same_carry_digits,
    same_carry_digit,
    validate_same_carry_chamber,
)
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts
from number_compiler.sequences.reverse_add.source_workspace import (
    ReverseSourceImageWorkspace,
)
from number_compiler.sequences.reverse_add.successor_width import (
    compile_reverse_successor_width,
)


class ReverseCylinderConstructionUnavailable(ValueError):
    """The requested temporal image needs the unbuilt successor cylinder."""


_CARRY_ACTIONS = tuple(CarryFn)


# The legacy nondecimal completed-child fallback is deliberately bounded.
# Decimal output uses its exact scheduler-owned Q19 occurrence without this cap.
MAX_COMPLETED_CHILD_FALLBACK_STEPS = 128


@dataclass(frozen=True, slots=True)
class ReverseImagePayload:
    """Chronological action and one authenticated completed-output form."""

    action: ReverseActionID
    occurrence: FieldImageID | None = None
    pair_output: ReversePairOutputOccurrence | None = None

    def __post_init__(self) -> None:
        if self.occurrence is not None and self.pair_output is not None:
            raise ValueError("reverse image cannot carry two completed outputs")


def _source_digit(source: ExactSource, position: int) -> int:
    return source.digits[position]


class _ReverseSourceImageAdapter(SourceBoundImageAdapter):
    family = "reverse-add"
    semantic_version = "source-cylinder-v8-successor-width-projection"

    def __init__(
        self, actions: ReverseActionArena, *, successor_width_root: ReverseActionID
    ) -> None:
        self.actions = actions
        self.ledger = actions.ledger
        self._successor_width_root = successor_width_root
        self.actions.node(successor_width_root)
        self._ports: SourceCarryPorts | None = None
        self._recursive: ReverseRecursiveTemporalCutover | None = None
        self._recursive_construction: OriginalSourceConstruction | None = None
        self._recursive_maximum_steps = 0
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
        self._q19_mode_source: ExactSource | None = None
        self._successor_width_workspace_owner: int | None = None

    def ports(self, source: ExactSource) -> SourceCarryPorts:
        """One source-bound spatial projection shared by every consumer."""
        ports = self._ports
        if ports is None:
            ports = SourceCarryPorts(source, self.ledger)
            self._ports = ports
        ports.check_source(source)
        return ports

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
                "reverse_source_pair_authority_construction_symbols", width
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
            self.ledger.bump("reverse_source_pair_authority_validation_symbols", width)
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
        if self._ports is not None:
            self._ports.dispose()
            self._ports = None
        if self._recursive is not None:
            self._recursive.dispose()
            self._recursive = None
        if self._q19_owner is not None:
            self._q19_owner.dispose()
            self._q19_owner = None
        self._q19_source = None
        self._q19_mode_source = None
        self._recursive_source = None
        self._recursive_construction = None
        self._recursive_occurrences.dispose()
        if self._successor_width_workspace_owner is not None:
            self.ledger.mark_disposed(self._successor_width_workspace_owner)
            self._successor_width_workspace_owner = None

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
        found = self._recursive_for_steps(steps)
        if found is not None:
            self.ledger.bump("reverse_source_recursive_occurrence_hits")
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
            self.ledger.bump("reverse_source_completed_prefix_checks")
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
            self.ledger.bump("reverse_source_completed_prefix_applications")
        if occurrence.temporal_steps != steps:
            raise AssertionError((occurrence.temporal_steps, steps))
        self._recursive_occurrences[steps] = occurrence
        self.ledger.bump("reverse_source_recursive_occurrence_publications")
        return occurrence

    def _recursive_for_steps(
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
        if payload.occurrence is not None and payload.pair_output is not None:
            raise ValueError("reverse image cannot carry two completed outputs")
        if payload.occurrence is not None:
            if type(payload.occurrence) is not FieldImageID:
                raise TypeError("reverse completed payload requires a field image")
            completed = self._recursive_for_steps(steps)
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

    def _validate_view(self, view: SourceImageView) -> ReverseImagePayload:
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
        if payload.pair_output is not None:
            owner = self._q19_owner
            if origin.base != 10 or owner is None or self._q19_source is not origin:
                raise ValueError("Q19 output belongs to another source")
            if payload.pair_output.temporal_steps != steps:
                raise ValueError("Q19 output and action have different durations")
            expected_ports = ()
            expected_precision = None
        elif payload.occurrence is None:
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
        payload = self._validate_view(source)
        before_steps = self.actions.node(payload.action).steps
        additional = self.actions.node(action).steps
        completed = self._recursive_for_steps(before_steps)
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
        cached = self._recursive_for_steps(total)
        if cached is None:
            target = cutover.apply_to_occurrence(occurrence, additional)
            self._recursive_occurrences[total] = target
        else:
            target = cached[1]
            self.ledger.bump("reverse_source_completed_parent_hits")
        self.ledger.bump("reverse_source_completed_provider_applications")
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
        payload = self._validate_view(source)
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
        if exact_source.base == 10:
            if payload.pair_output is None:
                if self.actions.node(payload.action).steps != 0:
                    raise ReverseCylinderConstructionUnavailable(
                        "decimal pair output lost its completed source occurrence"
                    )
                owner = self._q19_owner
                if owner is None:
                    owner = ReversePairQ19OutputOwner(
                        self.ledger, exact_source.digits, base=exact_source.base
                    )
                    self._q19_owner = owner
                    self._q19_source = exact_source
                elif self._q19_source is not exact_source:
                    raise ValueError("decimal pair owner is bound to another source")
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

    def apply_composite(
        self,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None:
        self.validate_action(action)
        self._validate_view(source)
        if demand is not None:
            demand.__post_init__()
        origin = self.actions.source(cast(ReverseSource, source.binding.source))
        payload = cast(ReverseImagePayload, source.payload)
        steps = self.actions.node(cast(ReverseActionID, action)).steps
        if origin.base == 10 and (
            self._q19_mode_source is origin or payload.pair_output is not None
        ):
            # Keep the canonical scheduler's completed-parent cache check first,
            # then let its postorder action traversal apply the spatial pair
            # transducer once per temporal primitive.
            return None
        source_steps = self.actions.node(
            cast(ReverseImagePayload, source.payload).action
        ).steps
        if steps < 2:
            raise ValueError(
                "reverse composite application requires at least two steps"
            )
        if cast(ReverseImagePayload, source.payload).occurrence is not None:
            return self._extend_completed(cast(ReverseActionID, action), source)
        if source_steps == 0 and steps == 2:
            origin = self.actions.source(cast(ReverseSource, source.binding.source))
            cumulative = self.actions.compose(
                cast(ReverseImagePayload, source.payload).action,
                cast(ReverseActionID, action),
            )
            self.ledger.bump("reverse_source_two_step_pullback_publications")
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
                if origin.base == 10:
                    # This fallback retains each primitive image until reset.
                    # Use only an absolute storage lower bound: prior prefixes
                    # may already occupy entries. A powered replacement must
                    # remove this implementation-specific admission check.
                    cache_limit = self.ledger.max_cache_entries
                    if cache_limit is not None and steps > cache_limit:
                        raise BlockContextBudgetExceeded(
                            "cache budget exceeded before Q19 source-image "
                            f"descent: at least {steps} retained cache entries "
                            f"are required, limit is {cache_limit}"
                        ) from exc
                    # Decimal output has the canonical Q19 scheduler route.
                    # Select it only after the existing same-carry admission
                    # rejects this source, keeping admitted algebra actions
                    # intact and avoiding the legacy recursive fallback.
                    self._q19_mode_source = origin
                    return None
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
                self.ledger.bump("reverse_source_completed_child_publications")
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
            self.ledger.bump("reverse_source_same_carry_publications")
            return SourceImageCandidate(
                ReverseImagePayload(cumulative),
                source.binding.extent + steps,
                boundary_ports=(0, 0),
                radix=origin.base,
                precision=len(origin.digits),
            )
        self.ledger.bump("reverse_cylinder_construction_failures")
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
        original = self._validate_view(source)
        middle = self._validate_view(before)
        final = self._validate_view(after)
        children = self.action_children(action)
        if (
            children is None
            or before.binding.source != source.binding.source
            or after.binding.source != source.binding.source
            or middle.action != self.actions.compose(original.action, children[0])
            or final.action != self.actions.compose(middle.action, children[1])
        ):
            raise ValueError("reverse chronological children have another binding")
        if final.occurrence is None and final.pair_output is None:
            raise ReverseCylinderConstructionUnavailable(
                "reverse chronology requires a completed final occurrence"
            )
        self.ledger.bump("reverse_source_completed_chronological_joins")
        return SourceImageCandidate(
            final,
            after.binding.extent,
            radix=after.binding.radix,
        )

    def admitted_input_key(
        self, action: Hashable, source: SourceImageView
    ) -> Hashable | None:
        self.validate_action(action)
        payload = self._validate_view(source)
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
        ):
            self.ledger.bump("reverse_cylinder_construction_failures")
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

    def _width(self, source: ExactSource) -> int:
        ports = self.ports(source)
        return ports.width + ports.terminal

    def _normalized(self, pair: int, incoming: int, base: int) -> tuple[int, int]:
        transfer = value_carry_fn(pair, base)
        outgoing = apply_carry_fn(transfer, incoming)
        if base == 10:
            domain = _CARRY_ACTIONS.index(transfer)
            digit = skew_normalized_digit(domain, pair % 9, incoming)
            self.ledger.bump("reverse_source_mod9_digit_reconstructions")
        else:
            digit = pair + incoming - base * outgoing
            self.ledger.bump("reverse_source_radix_digit_reconstructions")
        return outgoing, digit

    def iter_second_digits(self, source: ExactSource) -> Iterator[int]:
        """Emit D2 with one forward carry over the pulled pair-field stream."""
        ports = self.ports(source)
        carry = 0
        for pair in ports.iter_second_pairs():
            carry, digit = self._normalized(pair, carry, source.base)
            self.ledger.bump("reverse_source_second_step_coordinates")
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
        _, digit = self._normalized(
            ports.second_pair(position), ports.second_carry(position), source.base
        )
        self.ledger.bump("reverse_source_second_step_coordinates")
        return digit

    def iter_same_carry_digits(self, source: ExactSource, steps: int) -> Iterator[int]:
        """Consume the chamber already checked by image admission."""
        ports = self.ports(source)
        yield from iter_admitted_same_carry_digits(ports, steps)

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
        payload = self._validate_view(image)
        source = self.actions.source(cast(ReverseSource, image.binding.source))
        source_width = len(source.digits)
        steps = self.actions.node(payload.action).steps
        if demand.name == "successor-width":
            if source.base != 10 or steps != 0 or len(demand.parameters) != 2:
                raise ValueError("successor width demand needs a decimal source origin")
            root_action, requested_steps = demand.parameters
            if type(root_action) is not ReverseActionID:
                raise TypeError("successor width demand needs a scoped action ID")
            if root_action != self._successor_width_root:
                raise ValueError("successor width demand has another root action")
            if type(requested_steps) is not int or requested_steps < 3:
                raise ValueError("successor width demand needs an exact horizon")
            action_node = self.actions.node(root_action)
            if (
                action_node.steps != requested_steps
                or self.actions.action(requested_steps) != root_action
            ):
                raise ValueError("successor width demand action and horizon disagree")
            scratch_owner = self._successor_width_workspace_owner
            if source.digits != (0,) and scratch_owner is None:
                scratch_owner = self.ledger.register(
                    f"reverse-successor-width-workspace-{self.ledger.owner_count}",
                    "reverse_successor_width_workspace",
                )
                self._successor_width_workspace_owner = scratch_owner
            width_action = compile_reverse_successor_width(
                source.digits,
                requested_steps,
                ledger=self.ledger,
                scratch_owner=scratch_owner,
            )
            return SourceImageProjection(width_action)
        if payload.pair_output is not None:
            owner = self._q19_owner
            if owner is None or self._q19_source is not source:
                raise ValueError("decimal pair output lost its source owner")
            if demand == SourceImageDemand("width"):
                return SourceImageProjection(payload.pair_output.output_width)
            if demand.name != "digit" or len(demand.parameters) != 1:
                raise ValueError("unsupported decimal pair output demand")
            position = demand.parameters[0]
            if type(position) is not int:
                raise TypeError("decimal digit coordinate must be an integer")
            return SourceImageProjection(owner.digit(payload.pair_output, position))
        if demand == SourceImageDemand("width"):
            if steps == 0:
                return SourceImageProjection(source_width)
            if steps == 2:
                self.ledger.bump("reverse_source_two_step_width_demands")
                return SourceImageProjection(self.ports(source).second_width())
            if steps >= 3:
                recursive = self._recursive_for_steps(steps)
                if recursive is not None:
                    cutover, occurrence = recursive
                    self.ledger.bump("reverse_source_recursive_width_demands")
                    return SourceImageProjection(cutover.width(occurrence))
                self.ledger.bump("reverse_source_same_carry_width_demands")
                return SourceImageProjection(source_width)
            return SourceImageProjection(self._width(source))
        if demand.name != "digit" or len(demand.parameters) != 1:
            raise ValueError("unsupported reverse/add source image demand")
        position = demand.parameters[0]
        if type(position) is not int:
            raise TypeError("reverse/add digit coordinate must be an integer")
        if position < 0:
            raise IndexError(position)
        if steps >= 3:
            recursive = self._recursive_for_steps(steps)
            if recursive is not None:
                cutover, occurrence = recursive
                self.ledger.bump("reverse_source_recursive_digit_demands")
                return SourceImageProjection(cutover.digit(occurrence, position))
            if position >= source_width:
                raise IndexError(position)
            self.ledger.bump("reverse_source_same_carry_digit_demands")
            return SourceImageProjection(
                same_carry_digit(self.ports(source), steps, position)
            )
        if steps == 2:
            self.ledger.bump("reverse_source_two_step_digit_demands")
            return SourceImageProjection(self.second_digit(source, position))
        if steps == 0:
            if position >= source_width:
                raise IndexError(position)
            self.ledger.bump("reverse_source_digit_reads")
            return SourceImageProjection(_source_digit(source, position))
        if position > source_width:
            raise IndexError(position)
        ports = self.ports(source)
        if position == source_width:
            if not ports.terminal:
                raise IndexError(position)
            digit = 1
        else:
            _, digit = self._normalized(
                ports.pair(position), ports.carry(position), source.base
            )
            self.ledger.bump("reverse_source_carry_coordinates")
        return SourceImageProjection(digit)

    def iter_primitive_digits(self, source: ExactSource) -> Iterator[int]:
        """Stream one physical carry over original source pairs in LSD order."""
        ports = self.ports(source)
        carry = 0
        for position in range(ports.width):
            carry, digit = self._normalized(ports.pair(position), carry, source.base)
            self.ledger.bump("reverse_source_carry_coordinates")
            yield digit
        if carry:
            yield 1

    def first_failure(self, image: SourceImageView) -> None:
        self._validate_view(image)


__all__ = [
    "ReverseActionArena",
    "ReverseActionID",
    "ReverseActionNode",
    "ReverseCylinderConstructionUnavailable",
    "ReverseSource",
    "ReverseSourceImageWorkspace",
]
