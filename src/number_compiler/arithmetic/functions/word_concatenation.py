"""Iterative reassociation of interned words to largest dyadic prefixes."""

from __future__ import annotations

from collections.abc import Callable, MutableMapping
from typing import TypeVar

N = TypeVar("N")
U = TypeVar("U")


def concatenate_words(
    first: N,
    second: N,
    *,
    key_of: Callable[[N], int],
    length: Callable[[N], int],
    children: Callable[[N], tuple[N, N]],
    uniform: Callable[[N], U | None],
    run: Callable[[U, int], N],
    join: Callable[[N, N], N],
    cache: MutableMapping[tuple[int, int], N],
    reserve: Callable[[], None],
) -> N:
    """One canonical association owner; callers retain atom semantics/budgets.

    Inputs must already be canonical words. A non-None uniform label certifies
    a run of equal atoms. Observer values never participate in this operation.
    """
    pending = [(first, second, 0)]
    while pending:
        a, b, phase = pending.pop()
        key = key_of(a), key_of(b)
        if key in cache:
            continue
        reserve()
        na, nb = length(a), length(b)
        if not na or not nb:
            cache[key] = b if not na else a
            continue
        label = uniform(a)
        if label is not None and label == uniform(b):
            cache[key] = run(label, na + nb)
            continue
        prefix = 1 << ((na + nb - 1).bit_length() - 1)
        if na == prefix:
            cache[key] = join(a, b)
        elif na > prefix:
            left, right = children(a)
            if phase == 0:
                pending.extend(((a, b, 1), (right, b, 0)))
            else:
                cache[key] = join(left, cache[(key_of(right), key_of(b))])
        else:
            left, right = children(b)
            if phase == 0:
                pending.extend(((a, b, 1), (a, left, 0)))
            else:
                middle = cache[(key_of(a), key_of(left))]
                if phase == 1:
                    pending.extend(((a, b, 2), (middle, right, 0)))
                else:
                    cache[key] = cache[(key_of(middle), key_of(right))]
    return cache[(key_of(first), key_of(second))]
