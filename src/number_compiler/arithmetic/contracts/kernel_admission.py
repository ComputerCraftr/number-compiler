"""Immutable kernel admission, independent of compatibility execution.

Admission inspects the entire original composition DAG before semantic-key
reuse. This module owns no execution state, caches, or resource allocations.
"""

from __future__ import annotations

from typing import cast

from number_compiler.arithmetic.contracts.block_definition import (
    is_compatibility_composition,
)
from number_compiler.arithmetic.contracts.block_effect import BlockEffect
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
)
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect


def immutable_atom(effect: BlockEffect) -> BlockEffect:
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
    else:
        from number_compiler.sequences.collatz.block_power import (
            CollatzPhysicalBlockEffect,
        )

        if type(effect) is CollatzPhysicalBlockEffect:
            clone = CollatzPhysicalBlockEffect()
        else:
            # Import the proof C4 recognizer only for an explicit candidate;
            # ordinary family compilation must not load proof state domains.
            if type(effect).__name__ != "PhysicalCollatzFourBlockEffect":
                raise UnsupportedInterfaceError(
                    "generic lazy atoms require a complete immutable finite interface"
                )
            from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
                is_verified_physical_four,
            )

            if not is_verified_physical_four(effect):
                raise UnsupportedInterfaceError(
                    "generic lazy atoms require a complete immutable finite interface"
                )
            clone = effect
    return clone


def admit_effect(effect: BlockEffect) -> int:
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
            immutable_atom(current)
        admitted.add(id(current))
    return visits


__all__ = ["admit_effect", "immutable_atom"]
