"""Cacheless composition definitions, separate from compatibility runtimes."""

from __future__ import annotations

from dataclasses import dataclass
from typing import ClassVar, Protocol, TypeGuard, cast

from number_compiler.arithmetic.contracts.block_effect import BlockEffect, _effect_key
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity


class CompatibilityCompositionRuntime:
    """Marker for the legacy executable composition compatibility object.

    Production compilers use this cacheless marker to recognize an already
    constructed compatibility value without importing its execution modules.
    The marker deliberately supplies no executor, cache, or semantic behavior.
    """

    __slots__ = ()
    _runtime_type: ClassVar[type[CompatibilityCompositionRuntime] | None] = None

    def __init_subclass__(cls) -> None:
        if (
            CompatibilityCompositionRuntime._runtime_type is not None
            or cls.__module__ != "devtools.proofs.block_composed"
            or cls.__name__ != "ComposedBlockEffect"
        ):
            raise TypeError("compatibility composition runtime is sealed")
        CompatibilityCompositionRuntime._runtime_type = cls

    @property
    def definition(self) -> ComposedBlockDefinition:
        raise NotImplementedError

    @property
    def first(self) -> BlockEffect:
        raise NotImplementedError

    @property
    def second(self) -> BlockEffect:
        raise NotImplementedError


def is_compatibility_composition(
    value: object,
) -> TypeGuard[CompatibilityCompositionRuntime]:
    """Recognize only the one registered legacy runtime concrete type."""
    runtime_type = CompatibilityCompositionRuntime._runtime_type
    return runtime_type is not None and type(value) is runtime_type


class BlockDefinition(Protocol):
    @property
    def base(self) -> int: ...
    @property
    def blank(self) -> int: ...
    @property
    def exponent(self) -> int: ...
    @property
    def blank_left_tail(self) -> int: ...
    @property
    def blank_right_tail(self) -> int: ...
    @property
    def stable_blank_output(self) -> bool: ...
    @property
    def canonical_key(self) -> tuple[object, ...]: ...


def immutable_definition(
    effect: BlockEffect | ComposedBlockDefinition,
) -> BlockDefinition:
    """Strip execution owners; accept only known immutable primitive definitions."""
    from number_compiler.arithmetic.contracts.kernel_admission import immutable_atom

    if type(effect) is ComposedBlockDefinition:
        return effect
    if is_compatibility_composition(effect):
        return effect.definition
    return cast(BlockDefinition, immutable_atom(cast(BlockEffect, effect)))


@dataclass(frozen=True, slots=True, init=False, eq=False)
class ComposedBlockDefinition:
    """Complete immutable syntax; executing it requires a separate context.

    Children are definitions, never residual dictionaries or execution owners.
    Exact child identities accompany the digest so collisions cannot alias
    distinct compositions. No boundary universe is enumerated here.
    """

    first: BlockDefinition
    second: BlockDefinition
    base: int
    blank: int
    exponent: int
    blank_left_tail: int
    blank_right_tail: int
    stable_blank_output: bool
    supports_predecessor_trace: bool
    eager_boundary_quotient: bool
    canonical_key: tuple[object, ...]

    def __init_subclass__(cls, **kwargs: object) -> None:
        raise TypeError("composition definitions cannot contain mutable extensions")

    def __init__(
        self,
        first: BlockEffect | ComposedBlockDefinition,
        second: BlockEffect | ComposedBlockDefinition,
    ) -> None:
        left = immutable_definition(first)
        right = left if first is second else immutable_definition(second)
        if left.base != right.base or left.blank != right.blank:
            raise ValueError("composition definition alphabets do not match")
        stable = left.stable_blank_output and right.stable_blank_output
        first_ready = max(left.blank_left_tail, left.blank_right_tail)
        behavior = (
            "composed-block-definition-v1",
            _effect_key(left),
            _effect_key(right),
        )
        identity = SemanticIdentity("composed-block-definition", behavior)
        values: dict[str, object] = {
            "first": left,
            "second": right,
            "base": left.base,
            "blank": left.blank,
            "exponent": left.exponent + right.exponent,
            "blank_left_tail": first_ready + right.blank_left_tail if stable else 0,
            "blank_right_tail": first_ready + right.blank_right_tail if stable else 0,
            "stable_blank_output": stable,
            "supports_predecessor_trace": False,
            "eager_boundary_quotient": bool(
                getattr(left, "eager_boundary_quotient", False)
                and getattr(right, "eager_boundary_quotient", False)
            ),
            "canonical_key": ("composed-block-definition-v1", identity),
        }
        for name, value in values.items():
            object.__setattr__(self, name, value)
