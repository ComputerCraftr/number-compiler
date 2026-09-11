"""Typed boundaries between original input, lazy actions, and explicit lowering."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Self, TypeAlias


@dataclass(frozen=True, slots=True, eq=False)
class ArenaToken:
    """Identity of one arena lifetime; equal labels never imply equal owners."""

    label: str = ""

    def __post_init__(self) -> None:
        if type(self.label) is not str:
            raise TypeError("arena label must be a string")


@dataclass(frozen=True, slots=True)
class ArenaHandle:
    owner: ArenaToken
    kind: str
    local_id: int

    def __post_init__(self) -> None:
        if type(self.owner) is not ArenaToken:
            raise TypeError("a handle requires an arena owner")
        if type(self.kind) is not str or type(self.local_id) is not int:
            raise TypeError("handle kind must be a string and local ID an integer")
        if not self.kind or self.local_id < 0:
            raise ValueError("handle kind must be nonempty and id nonnegative")

    def validate(
        self, owner: ArenaToken, kind: str, *, size: int | None = None
    ) -> Self:
        # Recheck at every public boundary: dataclass construction is not an
        # authority when a forged/deserialized object can bypass __post_init__.
        if (
            type(self.owner) is not ArenaToken
            or type(self.kind) is not str
            or not self.kind
            or type(self.local_id) is not int
            or self.local_id < 0
        ):
            raise ValueError("malformed scoped handle")
        if (
            type(owner) is not ArenaToken
            or type(kind) is not str
            or not kind
            or size is not None
            and (type(size) is not int or size < 0)
        ):
            raise ValueError("invalid scoped handle validation domain")
        if self.owner is not owner or self.kind != kind:
            raise ValueError("handle belongs to a different arena or node kind")
        if size is not None and not 0 <= self.local_id < size:
            raise ValueError("handle is outside its arena's allocated range")
        return self


@dataclass(frozen=True, slots=True)
class ActionProgramID(ArenaHandle):
    """A scoped executable program identity, distinct from an observer."""


@dataclass(frozen=True, slots=True)
class TransferSummaryID(ArenaHandle):
    """A scoped finite transfer function identity, never an action program."""


ActionProgramRef: TypeAlias = ActionProgramID
TransferSummaryRef: TypeAlias = TransferSummaryID


@dataclass(frozen=True, slots=True)
class WordLimb:
    """Bounded local arithmetic payload, never an unbounded future integer."""

    value: int
    bits: int = 64

    def __post_init__(self) -> None:
        if type(self.value) is not int or type(self.bits) is not int:
            raise TypeError("word limbs require exact integer value and width")
        if not 1 <= self.bits <= 64 or not 0 <= self.value < (1 << self.bits):
            raise ValueError("word limb must fit its declared width of at most 64 bits")


@dataclass(frozen=True, slots=True)
class CarryBit:
    value: int

    def __post_init__(self) -> None:
        if type(self.value) is not int:
            raise TypeError("carry ports require an exact integer")
        if self.value not in (0, 1):
            raise ValueError("carry port must be binary")


@dataclass(frozen=True, slots=True)
class ExactSource:
    """Only original input may carry an eagerly available digit tuple."""

    digits: tuple[int, ...]
    base: int
    orbit: str = ""
    blank: int = 0
    extent: int | None = None
    alphabet_size: int | None = None

    def __post_init__(self) -> None:
        if type(self.digits) is not tuple:
            raise TypeError("original digits must be an immutable tuple")
        if (
            type(self.base) is not int
            or type(self.blank) is not int
            or type(self.orbit) is not str
            or self.extent is not None
            and type(self.extent) is not int
            or self.alphabet_size is not None
            and type(self.alphabet_size) is not int
            or any(type(digit) is not int for digit in self.digits)
        ):
            raise TypeError("source symbols and geometry require exact integer fields")
        if self.blank < 0:
            raise ValueError("source blank must be nonnegative")
        alphabet = self.base if self.alphabet_size is None else self.alphabet_size
        if (
            self.base < 2
            or alphabet < 1
            or any(not 0 <= d < alphabet for d in self.digits)
        ):
            raise ValueError("invalid original radix digits")
        if self.extent is not None and self.extent < len(self.digits):
            raise ValueError("source extent cannot truncate original digits")


@dataclass(frozen=True, slots=True)
class FrameTransform:
    shift: int = 0
    mirrored: bool = False

    def __post_init__(self) -> None:
        if type(self.shift) is not int or type(self.mirrored) is not bool:
            raise TypeError(
                "frame transform requires integer shift and Boolean orientation"
            )


@dataclass(frozen=True, slots=True)
class LazyFieldRef:
    """A future field has references and geometry, never an output payload."""

    source: ArenaHandle
    program: ActionProgramRef
    frame: FrameTransform = FrameTransform()
    extent: int | None = None

    def __post_init__(self) -> None:
        if (
            type(self.source) is not ArenaHandle
            or type(self.program) is not ActionProgramID
        ):
            raise TypeError("lazy fields require exact source and program handle sorts")
        ArenaHandle.__post_init__(self.source)
        self.program.__post_init__()
        if self.source.kind != "source" or self.source.owner is not self.program.owner:
            raise ValueError("lazy field source and program require the same arena")
        if type(self.frame) is not FrameTransform:
            raise TypeError("lazy field frame must be geometry metadata")
        self.frame.__post_init__()
        if self.extent is not None and (
            type(self.extent) is not int or self.extent < 0
        ):
            raise ValueError("negative field extent")


@dataclass(frozen=True, slots=True)
class LoweringCapability:
    """Explicit opt-in to output materialization, scoped to the owning arena."""

    owner: ArenaToken
    purpose: str = "explicit endpoint output"

    def __post_init__(self) -> None:
        from number_compiler.arithmetic.contracts.exact_tree_context import (
            require_endpoint_construction,
        )

        require_endpoint_construction()
        if (
            type(self.owner) is not ArenaToken
            or type(self.purpose) is not str
            or not self.purpose
        ):
            raise ValueError("endpoint lowering requires a scoped owner and purpose")


@dataclass(frozen=True, slots=True)
class MaterializedEndpoint:
    """Materialized output is distinct from every lazy computation reference."""

    field: LazyFieldRef
    digits: tuple[int, ...]
    base: int
    capability: LoweringCapability

    def __post_init__(self) -> None:
        from number_compiler.arithmetic.contracts.exact_tree_context import (
            require_endpoint_construction,
        )

        require_endpoint_construction()
        if type(self.field) is not LazyFieldRef:
            raise TypeError("materialized endpoints require a lazy field")
        self.field.__post_init__()
        if type(self.capability) is not LoweringCapability:
            raise TypeError(
                "materialized endpoints require an explicit lowering capability"
            )
        self.capability.__post_init__()
        if self.capability.owner is not self.field.program.owner:
            raise ValueError("endpoint lowering capability belongs to another arena")
        if type(self.digits) is not tuple:
            raise TypeError("endpoint digits must be immutable")
        if type(self.base) is not int or any(
            type(digit) is not int for digit in self.digits
        ):
            raise TypeError("endpoint digits and radix require exact integers")
        if self.base < 2 or any(not 0 <= d < self.base for d in self.digits):
            raise ValueError("invalid endpoint radix digits")


# Compatibility name; this remains one explicit output type, never a field ref.
ExactEndpoint: TypeAlias = MaterializedEndpoint
