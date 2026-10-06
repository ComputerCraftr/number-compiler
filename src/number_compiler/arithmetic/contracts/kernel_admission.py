"""Immutable kernel admission, independent of compatibility execution.

Admission inspects the entire original composition DAG before semantic-key
reuse. This module owns no execution state, caches, or resource allocations.
"""

from __future__ import annotations

from typing import cast

from number_compiler.arithmetic.contracts.block_definition import (
    is_compatibility_composition,
)
from number_compiler.arithmetic.contracts.block_effect import (
    BlockEffect,
    BlockEffectAdmissionAdapter,
)
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
)
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect


def immutable_atom(
    effect: BlockEffect,
    *,
    family_hooks: BlockEffectAdmissionAdapter | None = None,
) -> BlockEffect:
    from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
    from number_compiler.hashlife.observation.diamond_observers import (
        NonblankBlockEffect,
    )

    # The only extensible atom is an immutable complete finite table. Unknown
    # callbacks cannot silently bypass the representation/resource contract.
    if type(effect) is FiniteBlockEffect:
        return effect
    if type(effect) is BaseBlockEffect:
        clone: BlockEffect = BaseBlockEffect(effect.base)
    elif type(effect) is DigitNormalizeBlockEffect:
        clone = DigitNormalizeBlockEffect(effect.base)
    elif type(effect) is NonblankBlockEffect:
        clone = NonblankBlockEffect(effect.base, effect.blank)
    elif family_hooks is not None and family_hooks.owns_effect(effect):
        clone = family_hooks.clone(effect)
    elif family_hooks is not None and family_hooks.owns_compatibility(effect):
        family_hooks.validate_compatibility(effect)
        clone = effect
    else:
        raise UnsupportedInterfaceError(
            "generic lazy atoms require a complete immutable finite interface"
        )
    return clone


def admit_effect(
    effect: BlockEffect,
    *,
    family_hooks: BlockEffectAdmissionAdapter | None = None,
) -> int:
    """Validate every syntactic child before semantic-key deduplication.

    Equal composition keys do not establish that unseen descendants are
    supported immutable kernels. Admission deduplicates object identities
    only, independently of the semantic compilation memo.
    """
    from number_compiler.hashlife.actions.lazy_compiler import (
        ProgramComposition,
        UnsupportedInterfaceError,
    )

    pending = [(effect, False)]
    admitted: set[int] = set()
    active: set[int] = set()
    visits = 0
    while pending:
        current, ready = pending.pop()
        visits += 1
        if id(current) in admitted:
            continue
        if is_compatibility_composition(current) or isinstance(
            current, ProgramComposition
        ):
            if not ready:
                if id(current) in active:
                    raise UnsupportedInterfaceError("cyclic operator program")
                active.add(id(current))
                pending.extend(
                    (
                        (cast(BlockEffect, current), True),
                        (current.second, False),
                        (current.first, False),
                    )
                )
                continue
            effect = cast(BlockEffect, current)
            if any(
                child.base != effect.base or child.blank != effect.blank
                for child in (current.first, current.second)
            ):
                raise ValueError("operator program contains mixed alphabets")
            active.remove(id(current))
        else:
            immutable_atom(current, family_hooks=family_hooks)
        admitted.add(id(current))
    return visits


__all__ = ["admit_effect", "immutable_atom"]
