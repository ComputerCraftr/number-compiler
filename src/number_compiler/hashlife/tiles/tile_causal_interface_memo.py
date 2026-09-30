"""Atomic bindings for completed output-independent causal interfaces."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
)
from number_compiler.hashlife.tiles.result_reverse_indexes import publish_indexed_result
from number_compiler.hashlife.tiles.tile_result_records import (
    CausalInterfaceKey,
    CompletedInterfaceResult,
    PoweredResultKey,
    causal_interface_snapshot,
    execution_request_snapshot,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.cache_gc_metrics import record_cache_event, temporal_span
from number_compiler.resources.result_cache_kinds import (
    record_unattributed_post_eviction_miss,
)


def causal_interface_key(
    result: PoweredResultKey, *, observation: str = "interface"
) -> CausalInterfaceKey:
    """Project one exact causal execution context to its interface binding."""
    if type(result) is not PoweredResultKey:
        raise TypeError("causal interface binding requires a powered request")
    if result.region is not None:
        raise ValueError("causal interface binding requires a complete input tile")
    return CausalInterfaceKey(
        result.action,
        result.input,
        result.ports,
        result.wiring,
        result.boundaries,
        result.fusion,
        observation=observation,
    )


def _validate_key(arena: CompletedResultArena, key: CausalInterfaceKey) -> None:
    if type(arena) is not CompletedResultArena:
        raise TypeError("causal interface binding requires the shared result arena")
    if type(key) is not CausalInterfaceKey:
        raise TypeError("causal interface binding has another key sort")
    if type(key.observation) is not str or key.observation not in (
        "interface",
        "reverse-output-carry",
    ):
        raise ValueError("causal interface binding has an unsupported observation")
    arena._validate_base(key.action, key.input, key.wiring)
    arena._validate_ports(key.wiring.signature, key.ports)
    if key.fusion is None:
        arena._validate_boundaries(key.boundaries, key.input)
    else:
        arena._validate_fusion(
            key.action,
            key.fusion,
            key.fusion.consumer,
            key.input,
            counted=False,
        )
        if (
            key.ports != key.fusion.consumer.ports
            or key.boundaries != key.fusion.consumer.boundaries
            or key.wiring != key.fusion.consumer.wiring
        ):
            raise ValueError("causal interface key disagrees with its consumer edge")


def _record(payload: CausalInterfacePayload) -> CompletedInterfaceResult:
    if type(payload) is not CausalInterfacePayload:
        raise TypeError("causal interface binding requires a bounded payload")
    payload.__post_init__()
    return CompletedInterfaceResult(
        payload.interface,
        payload.incoming_ports,
        payload.outgoing_ports,
        payload.level,
        payload.active,
        payload.physical_ticks,
        payload.event_weight,
        payload.frame_shift,
        physical_support=payload.physical_support,
        bound_reverse_output=payload.bound_reverse_output,
    )


def _seal_record(
    arena: CompletedResultArena,
    key: CausalInterfaceKey,
    value: CompletedInterfaceResult,
) -> CompletedInterfaceResult:
    return CompletedInterfaceResult(
        value.interface,
        value.observed_input_ports,
        value.outgoing_ports,
        value.level,
        value.active,
        value.physical_ticks,
        value.event_weight,
        value.frame_shift,
        arena._interface_publication_seal,
        causal_interface_snapshot(key, value),
        physical_support=value.physical_support,
        bound_reverse_output=value.bound_reverse_output,
    )


def _payload(
    value: CompletedInterfaceResult,
    key: CausalInterfaceKey,
) -> CausalInterfacePayload:
    from number_compiler.hashlife.execution.tile_causal_interfaces import (
        _attach_bound_reverse_output,
        _bind_bound_reverse_output_request,
    )

    value.__post_init__()
    if len(value.observed_input_ports) != 2 or len(value.outgoing_ports) != 2:
        raise ValueError("causal interface binding requires two directed ports")
    payload = CausalInterfacePayload(
        value.interface,
        (value.observed_input_ports[0], value.observed_input_ports[1]),
        (value.outgoing_ports[0], value.outgoing_ports[1]),
        value.level,
        value.active,
        value.physical_ticks,
        value.event_weight,
        value.frame_shift,
        physical_support=value.physical_support,
    )
    if value.bound_reverse_output is None:
        return payload
    return _bind_bound_reverse_output_request(
        _attach_bound_reverse_output(payload, value.bound_reverse_output),
        execution_request_snapshot(key),
    )


def _bind_reverse_output_request(
    key: CausalInterfaceKey,
    payload: CausalInterfacePayload,
) -> CausalInterfacePayload:
    """Give one internally derived active summary its complete request proof."""
    from number_compiler.hashlife.execution.tile_causal_interfaces import (
        _bind_bound_reverse_output_request,
    )

    if type(key) is not CausalInterfaceKey:
        raise TypeError("active output proof requires a causal interface key")
    if type(payload) is not CausalInterfacePayload:
        raise TypeError("active output proof requires a causal interface payload")
    return _bind_bound_reverse_output_request(
        payload,
        execution_request_snapshot(key),
    )


def _validate_reverse_output_profile(
    arena: CompletedResultArena,
    key: CausalInterfaceKey,
    value: CompletedInterfaceResult,
) -> None:
    """Match a sealed carry summary to its producing action's exact radix."""
    output = value.bound_reverse_output
    if output is None:
        return
    authority = arena.action_authority
    records = getattr(authority, "_actions", None)
    record_lookup = getattr(records, "get", None)
    kernels = getattr(authority, "kernels", None)
    kernel_lookup = getattr(kernels, "kernel", None)
    if (
        not callable(record_lookup)
        or getattr(record_lookup, "__self__", None) is not records
        or not callable(kernel_lookup)
        or getattr(kernel_lookup, "__self__", None) is not kernels
    ):
        raise ValueError("reverse carry observation has no action authority")
    # _validate_key has already authenticated this action and its live record.
    # Read that exact record directly so a warm memo hit does not repeat the
    # complete temporal-DAG validation merely to compare one radix.
    record = record_lookup(key.action.local_id)
    if record is None:
        raise ValueError("reverse carry observation has a stale action")
    kernel = kernel_lookup(record.kernel)
    effect = kernel.effect
    if type(effect) not in (BaseBlockEffect, DigitNormalizeBlockEffect):
        raise ValueError("reverse carry observation has another action family")
    if type(kernel.base) is not int or output.left.base != kernel.base:
        raise ValueError("reverse carry observation has another radix")


def _validate_value(
    arena: CompletedResultArena,
    key: CausalInterfaceKey,
    value: CompletedInterfaceResult,
) -> None:
    _validate_observation_payload(arena, key, value)
    if key.observation == "reverse-output-carry" and value.bound_reverse_output is None:
        raise ValueError(
            "reverse carry observation requires its complete output transfer"
        )
    _validate_reverse_output_profile(arena, key, value)
    if arena.interfaces.resolve(value.interface).signature != key.wiring.signature:
        raise ValueError("causal interface result has another signature")
    arena._validate_ports(key.wiring.signature, value.observed_input_ports)
    arena._validate_ports(key.wiring.signature, value.outgoing_ports)
    if value.level != arena.tiles.resolve(key.input).level:
        raise ValueError("causal interface result has another spatial level")
    authority = arena.action_authority
    observe = getattr(authority, "_observe", None)
    if not callable(observe) or getattr(observe, "__self__", None) is not authority:
        raise ValueError("causal interface result has no bound observation authority")
    expected = (
        observe(value.interface, "boundary_left", value.observed_input_ports),
        observe(value.interface, "boundary_right", value.observed_input_ports),
    )
    if value.outgoing_ports != expected:
        raise ValueError(
            "causal interface result disagrees with its boundary functions"
        )
    active = bool(observe(value.interface, "activity", value.observed_input_ports))
    if value.active != active:
        raise ValueError("causal interface result disagrees with its activity function")


def _validate_published_value(
    arena: CompletedResultArena,
    key: CausalInterfaceKey,
    value: CompletedInterfaceResult,
) -> None:
    """Validate a warm record without executing its semantic functions."""
    _validate_observation_payload(arena, key, value)
    _validate_reverse_output_profile(arena, key, value)
    if value._publication_owner is not arena._interface_publication_seal:
        raise ValueError("causal interface result was not issued by this arena")
    if value._publication_snapshot != causal_interface_snapshot(key, value):
        raise ValueError("causal interface publication metadata was modified")
    if arena.interfaces.resolve(value.interface).signature != key.wiring.signature:
        raise ValueError("causal interface result has another signature")
    arena._validate_ports(
        key.wiring.signature, value.observed_input_ports, counted=False
    )
    arena._validate_ports(key.wiring.signature, value.outgoing_ports, counted=False)
    if value.level != arena.tiles.resolve(key.input).level:
        raise ValueError("causal interface result has another spatial level")


def lookup_causal_interface(
    arena: CompletedResultArena,
    key: CausalInterfaceKey,
) -> CausalInterfacePayload | None:
    """Return a complete bounded parent before any descendant task executes."""
    _validate_key(arena, key)
    found = arena._memo.get(key)
    arena.ledger.bump("causal_interface_result_requests")
    level = arena.tiles.resolve(key.input).level
    span = temporal_span(arena.action_authority, key.action)
    if found is None:
        record_unattributed_post_eviction_miss(arena.ledger, "interface")
        record_cache_event(
            arena.tiles._cache_metrics,
            "interface",
            "miss",
            spatial_level=level,
            temporal_span=span,
        )
        return None
    if type(found) is not CompletedInterfaceResult:
        raise TypeError("causal interface memo contains another value sort")
    _validate_published_value(arena, key, found)
    arena.ledger.bump("causal_interface_result_early_hits")
    record_cache_event(
        arena.tiles._cache_metrics,
        "interface",
        "early_hit",
        spatial_level=level,
        temporal_span=span,
        allow_new=False,
    )
    return _payload(found, key)


def publish_causal_interface(
    arena: CompletedResultArena,
    key: CausalInterfaceKey,
    payload: CausalInterfacePayload,
) -> CausalInterfacePayload:
    """Publish one complete interface binding under atomic ledger reservation."""
    _validate_key(arena, key)
    if payload.bound_reverse_output is not None and (
        payload._bound_output_request_snapshot != execution_request_snapshot(key)
    ):
        raise ValueError("causal active behavior belongs to another request")
    value = _record(payload)
    _validate_value(arena, key, value)
    value = _seal_record(arena, key, value)
    arena.ledger.bump("causal_interface_result_publication_requests")
    found = arena._memo.get(key)
    if found is not None:
        if type(found) is not CompletedInterfaceResult or found != value:
            raise ValueError("causal interface already has another complete value")
        arena.ledger.bump("causal_interface_result_late_duplicates")
        record_cache_event(
            arena.tiles._cache_metrics,
            "interface",
            "late_duplicate",
            spatial_level=arena.tiles.resolve(key.input).level,
            temporal_span=temporal_span(arena.action_authority, key.action),
        )
        return _payload(found, key)
    publish_indexed_result(
        arena,
        key,
        value,
        retained_nodes=(
            0
            if value.bound_reverse_output is None
            else value.bound_reverse_output.retained_slots
        ),
    )
    arena.ledger.bump("causal_interface_result_publications")
    level = arena.tiles.resolve(key.input).level
    span = temporal_span(arena.action_authority, key.action)
    arena.tiles._cache_metrics.prepare(
        "interface",
        "early_hit",
        spatial_level=level,
        temporal_span=span,
    )
    record_cache_event(
        arena.tiles._cache_metrics,
        "interface",
        "publication",
        spatial_level=level,
        temporal_span=span,
    )
    return payload


__all__ = [
    "causal_interface_key",
    "lookup_causal_interface",
    "publish_causal_interface",
]


def _validate_observation_payload(
    arena: CompletedResultArena,
    key: CausalInterfaceKey,
    value: CompletedInterfaceResult,
) -> None:
    value.__post_init__()
    if value.physical_support is not None:
        arena.validate_physical_support(value.physical_support)
    if (key.observation == "reverse-output-carry") != (
        value.bound_reverse_output is not None
    ):
        raise ValueError("causal interface result omits its requested observation")
