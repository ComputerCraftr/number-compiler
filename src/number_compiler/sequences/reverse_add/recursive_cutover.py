"""Bounded completed-child migration for reverse/add pair occurrences.

The workspace builds pair occurrences from completed source/action images and
applies later blocks through provider substitution. Nonleaf parent images are
composed from their exact completed children. This bounded route does not close
the generic temporal construction or observation-cost proof obligations.
"""

from __future__ import annotations

from collections.abc import Generator, Iterator
from dataclasses import dataclass, field

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
)
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.hashlife.actions.field_actions import (
    FieldCellActionID,
    FieldGeometry,
    FieldGeometryArena,
)
from number_compiler.hashlife.execution.continuations.higher_bimachine import (
    HigherBimachineRuntime,
)
from number_compiler.hashlife.execution.continuations.higher_interfaces import (
    HigherLocalInterfaceArena,
)
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.provider_absorption import (
    ProviderAbsorptionArena,
    ProviderAction,
)
from number_compiler.hashlife.execution.continuations.provider_field_executor import (
    ProviderFieldImageExecutor,
)
from number_compiler.hashlife.execution.continuations.provider_image_input import (
    ProviderImageInputArena,
    ProviderImageInputID,
)
from number_compiler.hashlife.execution.field_executor import (
    RecursiveFieldImageExecutor,
)
from number_compiler.hashlife.execution.field_images import (
    FieldImageID,
    RecursiveFieldImageArena,
    SourceCellArena,
    SourceCellID,
)
from number_compiler.hashlife.execution.recursive_outputs import (
    RecursiveCoordinateMorphismArena,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.resources.output_stream_metrics import closing_output_stream
from number_compiler.sequences.reverse_add.coordinate_program import (
    ReverseCoordinateProgramArena,
)
from number_compiler.sequences.reverse_add.field_action import (
    ReverseActionAutomorphisms,
    ReverseFieldActionArena,
)
from number_compiler.sequences.reverse_add.higher_interface import (
    ReverseHigherInterfaceCompiler,
)
from number_compiler.sequences.reverse_add.higher_schema import (
    ReverseHigherActionSchema,
)
from number_compiler.sequences.reverse_add.recursive_adapters import (
    _ReverseProviderAdapter,
    _ReverseRecursiveFieldAdapter,
)


def _same_semantics(_before: object, _after: object) -> str:
    return "reverse-runtime"


@dataclass(frozen=True, slots=True)
class ReverseRecursiveOccurrence:
    """Issued pair-field image with exact temporal and source authority."""

    image: FieldImageID
    action: FieldCellActionID
    temporal_steps: int
    source: SourceCellID
    _authority: object = field(repr=False, compare=False)
    active_extent: int | None = None

    def __post_init__(self) -> None:
        if (
            type(self.image) is not FieldImageID
            or type(self.action) is not FieldCellActionID
            or type(self.source) is not SourceCellID
            or type(self._authority) is not object
        ):
            raise TypeError(
                "reverse recursive occurrence requires scoped image/source/action authority"
            )
        if type(self.temporal_steps) is not int or self.temporal_steps < 1:
            raise ValueError(
                "reverse recursive occurrence starts after one temporal step"
            )
        if self.active_extent is not None and (
            type(self.active_extent) is not int or self.active_extent < 0
        ):
            raise ValueError("reverse recursive occurrence has invalid active extent")


class ReverseRecursiveTemporalCutover:
    """Bounded pair recurrence over a padded immutable pair-source cell."""

    def __init__(
        self,
        ledger: ResourceLedger,
        source_digits: tuple[int, ...],
        *,
        base: int,
        maximum_steps: int,
        source_construction: OriginalSourceConstruction | None = None,
    ) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("reverse recursive cutover requires a resource ledger")
        if type(source_digits) is not tuple or not source_digits:
            raise ValueError("reverse recursive cutover requires original digits")
        if (
            type(base) is not int
            or base < 2
            or type(maximum_steps) is not int
            or maximum_steps < 0
        ):
            raise ValueError(
                "reverse recursive cutover has invalid radix/time geometry"
            )
        self.ledger, self.base = ledger, base
        self.source_digits = source_digits
        self.maximum_steps = maximum_steps
        blank = 2 * base - 1
        if source_construction is not None:
            exact = source_construction.validate_source()
            required = max(1, len(exact.digits) + maximum_steps)
            expected_extent = 1 << ((required - 1).bit_length())
            if (
                exact.base != base
                or exact.orbit != "reverse-add-pair"
                or exact.blank != blank
                or exact.extent != expected_extent
                or exact.alphabet_size != 2 * base
                or len(exact.digits) != len(source_digits)
                or any(
                    exact.digits[i]
                    != source_digits[i] + source_digits[len(source_digits) - 1 - i]
                    for i in range(len(source_digits))
                )
            ):
                raise ValueError(
                    "recursive construction authority differs from source digits"
                )
        else:
            from number_compiler.sequences.reverse_add.power import (
                _pair_field_from_digits,
            )

            pair = _pair_field_from_digits(source_digits)
            required = max(1, len(pair) + maximum_steps)
            extent = 1 << ((required - 1).bit_length())
            exact = ExactSource(pair, base, "reverse-add-pair", blank, extent, 2 * base)
        exact_extent = exact.extent
        if type(exact_extent) is not int:
            raise AssertionError("reverse pair source requires a padded extent")
        extent = exact_extent
        level = extent.bit_length() - 1
        self.extent, self.level, self.blank = extent, level, blank
        pair = exact.digits
        source_geometry = SourceGeometry(ledger, exact, source_construction)
        source_geometry.span(pair, blank, extent)
        sources = SourceCellArena(source_geometry)
        root = sources.intern(0, level)
        self.source_geometry, self.sources, self.source = source_geometry, sources, root

        programs = ReverseCoordinateProgramArena(base, ledger)
        actions = ReverseFieldActionArena(
            base=base,
            order=8,
            residual_identity="reverse-runtime",
            output_identity="reverse-runtime",
            residual_compose=_same_semantics,
            output_compose=_same_semantics,
            automorphisms=ReverseActionAutomorphisms.trivial(),
            ledger=ledger,
            coordinate_programs=programs,
        )
        residual = actions.intern_residual("reverse-runtime")
        action_geometry = actions.resolve(actions.identity).geometry
        primitive = actions.intern(
            base=base,
            innovation=ReverseAddCyclotomicInnovationBlock.atom(
                (1,), 0, order=8, bits=5
            ),
            carry_forward=CarryFn.ID,
            carry_backward=CarryFn.ID,
            residual=residual,
            output=programs.primitive,
            geometry=action_geometry,
        )
        terminal = actions.intern(
            base=base,
            innovation=ReverseAddCyclotomicInnovationBlock.identity(order=8, bits=5),
            carry_forward=CarryFn.ID,
            carry_backward=CarryFn.ID,
            residual=residual,
            output=programs.terminal,
            geometry=action_geometry,
        )
        schema = ReverseHigherActionSchema(actions, primitive, terminal)
        semantics = HigherSemanticArena(schema)
        runtime = HigherBimachineRuntime(semantics, sources)
        interfaces = HigherLocalInterfaceArena(semantics)
        compiler = ReverseHigherInterfaceCompiler(
            actions, schema, semantics, runtime, interfaces
        )
        outputs = RecursiveCoordinateMorphismArena(
            interfaces, evaluate=semantics.evaluate
        )
        geometries = FieldGeometryArena(ledger)
        root_geometry = geometries.intern(
            FieldGeometry(level, phase_count=action_geometry.phase_count)
        )
        adapter = _ReverseRecursiveFieldAdapter(
            ledger,
            actions,
            sources,
            semantics,
            runtime,
            interfaces,
            outputs,
            compiler,
            blank=blank,
        )
        adapter.bind_geometries(geometries)
        images = RecursiveFieldImageArena(
            ledger,
            sources,
            geometries,
            interfaces,  # HigherLocalInterfaceArena implements the same scoped interface contract.
            action_owner=actions.owner,
            output_owner=outputs.owner,
            signature_owner=interfaces.owner,
            action_validate=actions.validate_action,
            output_validate=outputs.resolve,
            signature_for=adapter.signature,
            action_authority=actions,
            output_authority=outputs,
            signature_authority=adapter,
            action_kind=actions.action_kind,
            output_kind=outputs.kind,
            signature_kind=interfaces.signature_kind,
            retain_occurrence_authority=True,
        )
        adapter.bind_images(images)
        executor = RecursiveFieldImageExecutor(sources, images, adapter)
        providers = ProviderAbsorptionArena(
            ledger,
            sources,
            validate_output=outputs.resolve,
            validate_bound_output=outputs.resolve,
            validate_interface=interfaces.resolve,
            validate_bound_interface=interfaces.resolve,
            validate_action=actions.validate_action,
            validate_boundary=lambda _value: None,
            observe=outputs.observe,
            validate_image=images.resolve,
            validate_image_occurrence=images.validate_occurrence,
        )
        inputs = ProviderImageInputArena(providers, images)
        provider_adapter = _ReverseProviderAdapter(adapter, providers)
        provider_executor = ProviderFieldImageExecutor(
            providers, inputs, images, provider_adapter
        )
        self.programs, self.actions = programs, actions
        self.primitive, self.terminal = primitive, terminal
        self.schema, self.semantics, self.runtime = schema, semantics, runtime
        self.interfaces, self.outputs = interfaces, outputs
        self.geometries, self.geometry = geometries, root_geometry
        self.adapter, self.images, self.executor = adapter, images, executor
        self.providers, self.inputs = providers, inputs
        self.provider_adapter, self.provider_executor = (
            provider_adapter,
            provider_executor,
        )
        pair_owner = ledger.register(
            f"reverse-recursive-pair-actions-{ledger.owner_count}",
            "reverse_recursive_pair_action_memo",
        )
        digit_owner = ledger.register(
            f"reverse-recursive-digit-images-{ledger.owner_count}",
            "query_memo",
        )
        width_owner = ledger.register(
            f"reverse-recursive-pair-widths-{ledger.owner_count}",
            "width_query_memo",
        )
        boundary_owner = ledger.register(
            f"reverse-recursive-boundaries-{ledger.owner_count}",
            "observation_memo",
        )
        self._pair_actions: OwnedMemo[int, FieldCellActionID] = OwnedMemo(
            ledger, pair_owner
        )
        self._digit_images: OwnedMemo[
            tuple[FieldImageID, FieldCellActionID],
            tuple[FieldImageID, FieldCellActionID],
        ] = OwnedMemo(ledger, digit_owner, evictable=True)
        self._pair_widths: OwnedMemo[tuple[FieldImageID, FieldCellActionID], int] = (
            OwnedMemo(ledger, width_owner, evictable=True)
        )
        self._boundary_cache: OwnedMemo[FieldCellActionID, tuple[object, object]] = (
            OwnedMemo(ledger, boundary_owner, evictable=True)
        )
        self._disposed = False
        self._occurrence_authority = object()
        self.ledger.register_execution_root(self)

    def pair_action(self, temporal_steps: int) -> FieldCellActionID:
        if self._disposed:
            raise ValueError("reverse recursive workspace is disposed")
        if (
            type(temporal_steps) is not int
            or not 1 <= temporal_steps <= self.maximum_steps
        ):
            raise ValueError("pair action is outside the admitted temporal horizon")
        found = self._pair_actions.get(temporal_steps)
        if found is not None:
            return found
        found = self.actions.power(self.primitive, temporal_steps - 1)
        self._pair_actions[temporal_steps] = found
        return found

    def pair_image(self, temporal_steps: int) -> ReverseRecursiveOccurrence:
        if self._disposed:
            raise ValueError("reverse recursive workspace is disposed")
        if (
            type(temporal_steps) is not int
            or not 1 <= temporal_steps <= self.maximum_steps
        ):
            raise ValueError("pair occurrence is outside the admitted temporal horizon")
        occurrence = self._base_pair_image()
        for bit in bin(temporal_steps)[3:]:
            occurrence = self.square_occurrence(occurrence)
            if bit == "1":
                occurrence = self.apply_to_occurrence(occurrence, 1)
        if occurrence.temporal_steps != temporal_steps:
            raise AssertionError((occurrence.temporal_steps, temporal_steps))
        self.validate_occurrence(occurrence)
        self.adapter.clear_construction_memos()
        self.ledger.bump(_reverse_add_keys.REVERSE_RECURSIVE_OCCURRENCE_PUBLICATIONS)
        return occurrence

    def _base_pair_image(self) -> ReverseRecursiveOccurrence:
        action = self.pair_action(1)
        signature = self.adapter.signature(action, self.geometry)
        image = self.executor.image(action, self.source, self.geometry, signature)
        occurrence = self._new_occurrence(image, action, 1, None)
        self.validate_occurrence(occurrence)
        return occurrence

    def _new_occurrence(
        self,
        image: FieldImageID,
        action: FieldCellActionID,
        temporal_steps: int,
        active_extent: int | None,
    ) -> ReverseRecursiveOccurrence:
        occurrence = ReverseRecursiveOccurrence(
            image,
            action,
            temporal_steps,
            self.source,
            self._occurrence_authority,
            active_extent,
        )
        return occurrence

    def validate_occurrence(self, occurrence: ReverseRecursiveOccurrence) -> None:
        """Purely authenticate one issued occurrence without compiling its image."""
        if self._disposed:
            raise ValueError("disposed reverse recursive cutover")
        if type(occurrence) is not ReverseRecursiveOccurrence:
            raise TypeError("reverse operation requires an issued pair occurrence")
        occurrence.__post_init__()
        if (
            occurrence._authority is not self._occurrence_authority
            or occurrence.source != self.source
            or occurrence.temporal_steps > self.maximum_steps
            or occurrence.active_extent not in (None, self.extent)
            or self._pair_actions.get(occurrence.temporal_steps) != occurrence.action
        ):
            raise ValueError(
                "reverse occurrence authority/source/action was not issued here"
            )
        program = self.programs.resolve(self.actions.resolve(occurrence.action).output)
        if (
            not program.executable
            or program.normalized
            or program.pair_steps != occurrence.temporal_steps - 1
        ):
            raise ValueError(
                "reverse occurrence action differs from its temporal duration"
            )
        self.images.validate_occurrence(
            occurrence.image,
            occurrence.source,
            occurrence.action,
            occurrence.active_extent,
            None,
        )
        image = self.images.resolve(occurrence.image)
        if image.geometry != self.geometry or image.level != self.level:
            raise ValueError("reverse occurrence image has another spatial admission")

    def _provider_input(
        self, occurrence: ReverseRecursiveOccurrence
    ) -> ProviderImageInputID:
        record = self.images.resolve(occurrence.image)
        provider_id = self.providers.intern(
            ProviderAction(record.output, record.interface, occurrence.action, 0, 0, 1)
        )
        binding = self.providers.bind(
            provider_id,
            self.source,
            record.output,
            record.interface,
            occurrence.image,
            occurrence.active_extent,
        )
        return self.inputs.bind(binding, self.source, self.extent)

    def apply_to_occurrence(
        self,
        occurrence: ReverseRecursiveOccurrence,
        additional_steps: int,
    ) -> ReverseRecursiveOccurrence:
        """Apply an action to an authenticated occurrence without reading digits."""
        occurrence.__post_init__()
        if type(additional_steps) is not int or additional_steps < 0:
            raise ValueError("additional reverse steps must be nonnegative")
        self.validate_occurrence(occurrence)
        if additional_steps == 0:
            return occurrence
        target_steps = occurrence.temporal_steps + additional_steps
        if target_steps > self.maximum_steps:
            raise ValueError("reverse recursive fallback exceeded its admitted horizon")
        consumer = self.actions.power(self.primitive, additional_steps)
        provider_input = self._provider_input(occurrence)
        target = self.provider_executor.image(consumer, provider_input, self.geometry)
        target_action = self.actions.compose(occurrence.action, consumer)
        existing = self._pair_actions.get(target_steps)
        if existing is not None and existing != target_action:
            raise ValueError("reverse temporal action differs from its issued power")
        self._pair_actions[target_steps] = target_action
        result = self._new_occurrence(target, target_action, target_steps, self.extent)
        self.validate_occurrence(result)
        self.adapter.clear_construction_memos()
        self.ledger.bump(_reverse_add_keys.REVERSE_RECURSIVE_PROVIDER_APPLICATIONS)
        return result

    def square_occurrence(
        self, occurrence: ReverseRecursiveOccurrence
    ) -> ReverseRecursiveOccurrence:
        """Double the temporal duration through provider substitution."""
        occurrence.__post_init__()
        self.validate_occurrence(occurrence)
        result = self.apply_to_occurrence(occurrence, occurrence.temporal_steps)
        if result.temporal_steps != 2 * occurrence.temporal_steps:
            raise AssertionError(
                "reverse source-relative square changed temporal duration"
            )
        self.ledger.bump(_reverse_add_keys.REVERSE_RECURSIVE_SOURCE_RELATIVE_SQUARES)
        return result

    def pair_width(self, occurrence: ReverseRecursiveOccurrence) -> int:
        """Return the active recurrent pair-field width without digit normalization."""
        occurrence.__post_init__()
        self.validate_occurrence(occurrence)
        key = occurrence.image, occurrence.action
        found = self._pair_widths.get(key)
        if found is not None:
            self.ledger.bump(_reverse_add_keys.REVERSE_RECURSIVE_PAIR_WIDTH_CACHE_HITS)
            return found
        self.ledger.bump(_reverse_add_keys.REVERSE_RECURSIVE_PAIR_WIDTH_CACHE_MISSES)
        try:
            record = self.images.resolve(occurrence.image)
            output = record.output
            left, right = self._boundaries(occurrence.action)
            low, high = 0, self.extent
            while low < high:
                middle = (low + high) // 2
                value = self.outputs.observe_extent(output, middle, left, right)
                if value == self.blank:
                    high = middle
                else:
                    low = middle + 1
                self.ledger.bump(
                    _reverse_add_keys.REVERSE_RECURSIVE_PAIR_WIDTH_DESCENTS
                )
            self._pair_widths[key] = low
            self.ledger.bump(
                _reverse_add_keys.REVERSE_RECURSIVE_PAIR_WIDTH_PUBLICATIONS
            )
            return low
        except BaseException:
            self.ledger.bump(_reverse_add_keys.REVERSE_RECURSIVE_PAIR_WIDTH_FAILURES)
            raise

    def digit_image(
        self, occurrence: ReverseRecursiveOccurrence
    ) -> tuple[FieldImageID, FieldCellActionID]:
        occurrence.__post_init__()
        self.validate_occurrence(occurrence)
        key = occurrence.image, occurrence.action
        found = self._digit_images.get(key)
        if found is not None:
            return found
        provider_input = self._provider_input(occurrence)
        image = self.provider_executor.image(
            self.terminal, provider_input, self.geometry
        )
        action = self.actions.compose(occurrence.action, self.terminal)
        self.images.validate_occurrence(image, self.source, action, self.extent)
        self.adapter.clear_construction_memos()
        self._digit_images[key] = image, action
        self.ledger.bump(_reverse_add_keys.REVERSE_RECURSIVE_TERMINAL_PUBLICATIONS)
        return image, action

    def _boundaries(self, action: FieldCellActionID) -> tuple[object, object]:
        found = self._boundary_cache.get(action)
        if found is not None:
            return found
        result = (
            self.semantics.evaluate(self.runtime.initial(action, 0)),
            self.semantics.evaluate(self.runtime.initial(action, 1)),
        )
        self._boundary_cache[action] = result
        return result

    def _pair_stream(
        self,
        occurrence: ReverseRecursiveOccurrence,
        width: int,
        stop: int | None = None,
    ) -> Iterator[int]:
        """Stream active pair values for terminal digit normalization."""
        occurrence.__post_init__()
        self.validate_occurrence(occurrence)
        if type(width) is not int or not 0 <= width <= self.extent:
            raise ValueError(width)
        if stop is None:
            stop = width
        if type(stop) is not int or not 0 <= stop <= width:
            raise ValueError((stop, width))
        record = self.images.resolve(occurrence.image)
        left, right = self._boundaries(occurrence.action)
        with closing_output_stream(
            self.outputs.iter_observe_range(record.output, 0, stop, left, right)
        ) as output:
            while True:
                try:
                    value = next(output)
                except StopIteration:
                    return
                yield value

    def _terminal_carry(
        self, occurrence: ReverseRecursiveOccurrence, pair_width: int
    ) -> int:
        """Use mirror symmetry to read only the first decisive carry domain.

        The admitted recurrent pair field is symmetric. Its last nonidentity
        domain therefore equals its first, and controls the outgoing carry.
        The all-neutral field preserves incoming zero. No temporal closure or
        constant bound on the neutral prefix is implied by this shortcut.
        """
        with closing_output_stream(self._pair_stream(occurrence, pair_width)) as pairs:
            for pair in pairs:
                if not 0 <= pair < self.blank:
                    raise AssertionError(
                        "reverse pair stream encountered an invalid symbol"
                    )
                effect = value_carry_fn(pair, self.base)
                self.ledger.bump(
                    _reverse_add_keys.REVERSE_RECURSIVE_TERMINAL_RESET_PREFIX_SYMBOLS
                )
                if effect is not CarryFn.ID:
                    self.ledger.bump(
                        _reverse_add_keys.REVERSE_RECURSIVE_TERMINAL_RESET_HITS
                    )
                    return apply_carry_fn(effect, 0)
        self.ledger.bump(_reverse_add_keys.REVERSE_RECURSIVE_TERMINAL_NEUTRAL_FIELDS)
        return 0

    def _normalize_pair(self, pair: int, carry: int) -> tuple[int, int]:
        if not 0 <= pair < self.blank:
            raise AssertionError("reverse pair stream encountered an invalid symbol")
        return divmod(pair + carry, self.base)

    def digit(self, occurrence: ReverseRecursiveOccurrence, coordinate: int) -> int:
        if type(coordinate) is not int or coordinate < 0:
            raise IndexError(coordinate)
        pair_width = self.pair_width(occurrence)
        if coordinate > pair_width:
            raise IndexError(coordinate)
        if coordinate == pair_width:
            carry = self._terminal_carry(occurrence, pair_width)
            if carry:
                self.ledger.bump(_reverse_add_keys.REVERSE_RECURSIVE_DIGIT_OBSERVATIONS)
                return carry
            raise IndexError(coordinate)
        carry = 0
        with closing_output_stream(
            self._pair_stream(occurrence, pair_width, coordinate + 1)
        ) as pairs:
            for position, pair in enumerate(pairs):
                outgoing, digit = self._normalize_pair(pair, carry)
                self.ledger.bump(_reverse_add_keys.REVERSE_RECURSIVE_DIRECT_CARRY_STEPS)
                if position == coordinate:
                    self.ledger.bump(
                        _reverse_add_keys.REVERSE_RECURSIVE_DIGIT_OBSERVATIONS
                    )
                    return digit
                carry = outgoing
        raise IndexError(coordinate)

    def width(self, occurrence: ReverseRecursiveOccurrence) -> int:
        pair_width = self.pair_width(occurrence)
        carry = self._terminal_carry(occurrence, pair_width)
        self.ledger.bump(_reverse_add_keys.REVERSE_RECURSIVE_DIRECT_WIDTH_DEMANDS)
        return pair_width + carry

    def iter_digits(
        self, occurrence: ReverseRecursiveOccurrence
    ) -> Generator[int, None, None]:
        """Stream terminal digits directly from the completed pair grammar."""
        occurrence.__post_init__()
        pair_width = self.pair_width(occurrence)
        carry = 0
        emitted = 0
        with closing_output_stream(self._pair_stream(occurrence, pair_width)) as pairs:
            for pair in pairs:
                outgoing, digit = self._normalize_pair(pair, carry)
                carry = outgoing
                emitted += 1
                self.ledger.bump(_reverse_add_keys.REVERSE_RECURSIVE_DIRECT_CARRY_STEPS)
                self.ledger.bump(_reverse_add_keys.REVERSE_RECURSIVE_STREAMED_DIGITS)
                yield digit
        if carry:
            emitted += 1
            self.ledger.bump(_reverse_add_keys.REVERSE_RECURSIVE_STREAMED_DIGITS)
            yield carry
        if emitted != pair_width + int(carry):
            raise AssertionError("reverse direct output stream width mismatch")

    def dispose(self) -> None:
        """Release evictable query state under the shared ledger contract."""
        if self._disposed:
            return
        self.adapter.dispose()
        self.providers.clear_observations()
        self.images.clear_bindings()
        self._pair_actions.dispose()
        self._digit_images.dispose()
        self._pair_widths.dispose()
        self._boundary_cache.dispose()
        self._disposed = True
        self.ledger.bump(_reverse_add_keys.REVERSE_RECURSIVE_CUTOVER_DISPOSALS)


__all__ = ["ReverseRecursiveOccurrence", "ReverseRecursiveTemporalCutover"]
