"""Source-bound point observer for admitted higher-bimachine actions.

The provider retains an original source binding and a fixed producer action.
It observes a supplied composed action through the higher bimachine's dyadic
summaries without constructing a midpoint word. This observer does not build
or certify a complete temporal successor image for arbitrary consumers.
"""

from __future__ import annotations

from collections.abc import Callable, MutableMapping

from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
)
from number_compiler.hashlife.execution.continuations.higher_bimachine import (
    HigherBimachineRuntime,
)
from number_compiler.hashlife.execution.field_images import (
    SourceBindingID,
    SourceCellID,
    SourceForestID,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)


class HigherTemporalProviderEvaluator:
    """Bind outputs to admitted sources for canonical-boundary point demands.

    Bindings are occurrence metadata. The temporal output arena can normalize
    nested action syntax, but this evaluator remains an observation consumer;
    it does not establish successor right-congruence of output IDs.
    """

    def __init__(
        self,
        runtime: HigherBimachineRuntime,
        *,
        validate_output: Callable[[CoordinateOutputMorphismID], object],
        validate_binding: Callable[
            [CoordinateOutputMorphismID, SourceBindingID, FieldCellActionID], None
        ],
        compose_actions: Callable[
            [FieldCellActionID, FieldCellActionID], FieldCellActionID
        ],
    ) -> None:
        if (
            type(runtime) is not HigherBimachineRuntime
            or not callable(validate_output)
            or not callable(validate_binding)
            or not callable(compose_actions)
        ):
            raise TypeError("higher temporal provider requires scoped runtime objects")
        self.runtime = runtime
        self.ledger: ResourceLedger = runtime.ledger
        self._validate_output = validate_output
        self._validate_binding = validate_binding
        self._compose_actions = compose_actions
        self.ledger.register_execution_root(self)
        prefix = f"higher-temporal-provider-{len(self.ledger.inventory())}"
        self._binding_owner = self.ledger.register(
            prefix + "-bindings",
            "output_provider_binding",
        )
        self._bindings: MutableMapping[
            CoordinateOutputMorphismID, tuple[SourceBindingID, FieldCellActionID]
        ] = self.ledger.make_dict(self._binding_owner)
        self.ledger.register_container(
            self._binding_owner,
            self._bindings,
            payloads=self._bindings.items,
        )

        self._authority = self._authority_objects()

    def _authority_objects(self) -> tuple[object, ...]:
        return (
            self.runtime,
            self.ledger,
            self.runtime.ledger,
            self.runtime.owner,
            self.runtime.sources,
            self.runtime.sources.owner,
            self.runtime.schema,
            self.runtime.semantics,
            self.runtime.summaries,
            self._validate_output,
            self._validate_binding,
            self._compose_actions,
            self._binding_owner,
            self._bindings,
        )

    def _check_authority(self) -> None:
        expected = self._authority
        actual = self._authority_objects()
        if (
            type(expected) is not tuple
            or len(expected) != len(actual)
            or any(a is not b for a, b in zip(actual, expected, strict=True))
            or self.ledger is not self.runtime.ledger
        ):
            raise ValueError("higher temporal provider lost its issued authority")

    def bind(
        self,
        provider: CoordinateOutputMorphismID,
        source: SourceBindingID,
        action: FieldCellActionID,
    ) -> None:
        """Associate one canonical output provider with immutable source geometry."""
        self._check_authority()
        self._validate_output(provider)
        self.runtime.schema.validate_action(action)
        if type(source) is SourceCellID:
            self.runtime.sources.resolve(source)
        elif type(source) is SourceForestID:
            self.runtime.sources.resolve_forest(source)
        else:
            raise TypeError("temporal provider requires a scoped source binding")
        self._validate_binding(provider, source, action)
        found = self._bindings.get(provider)
        if found is not None:
            # The configured producer validated this occurrence for the same
            # output. The first binding remains the observation witness; an
            # output alias is not authority for a different future successor.
            self.ledger.bump(_execution_keys.TEMPORAL_PROVIDER_BINDING_ALIASES)
            return
        self.ledger.reserve(self._binding_owner, entries=1)
        self._bindings[provider] = (source, action)
        self.ledger.bump(_execution_keys.TEMPORAL_PROVIDER_BINDINGS)

    def complete_action(
        self,
        provider: CoordinateOutputMorphismID,
        after: FieldCellActionID,
    ) -> FieldCellActionID:
        """Resolve and compose the provider action once, before publication."""
        self._check_authority()
        self._validate_output(provider)
        self.runtime.schema.validate_action(after)
        binding = self._bindings.get(provider)
        if binding is None:
            raise ValueError("recursive output provider has no source binding")
        _source, before = binding
        return self._compose_actions(before, after)

    def __call__(
        self,
        provider: CoordinateOutputMorphismID,
        action: FieldCellActionID,
        _interface: LocalInterfaceID,
        coordinate: int,
        left: object,
        right: object,
    ) -> int:
        """Observe a composed action through dyadic context summaries.

        This adapter intentionally accepts only the action's canonical exterior
        boundary.  Arbitrary bound-port observations belong to a family codec's
        complete local-interface evaluator; silently ignoring those values would
        equate carry exits with output-complete behavior.
        """
        self._check_authority()
        self._validate_output(provider)
        self.runtime.schema.validate_action(action)
        binding = self._bindings.get(provider)
        if binding is None:
            raise ValueError("recursive output provider has no source binding")
        source, _provider_action = binding
        expected_left = self.runtime.semantics.evaluate(self.runtime.initial(action, 0))
        expected_right = self.runtime.semantics.evaluate(
            self.runtime.initial(action, 1)
        )
        if left != expected_left or right != expected_right:
            raise ValueError(
                "higher temporal provider received noncanonical exterior boundaries"
            )
        self.ledger.bump(_execution_keys.TEMPORAL_PROVIDER_OBSERVATIONS)
        return self.runtime.point(action, source, coordinate)


__all__ = ["HigherTemporalProviderEvaluator"]
