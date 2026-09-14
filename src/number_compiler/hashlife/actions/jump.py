"""Strict binary index driver and hard powered-jump production guard.

A backend called through :class:`StrictBinaryRootBuilder` executes inside the
powered guard.  Ordinary successor replay, growth-bit evaluation, per-position
queries, materialization, raw carry construction, and branch compilation are
therefore impossible to hide inside ``jump_bit``.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Generic, Protocol, TypeVar, runtime_checkable

from number_compiler.arithmetic.automata.guard import (
    JumpAudit,
    JumpAuditSnapshot,
    powered_jump_scope,
)

RootT = TypeVar("RootT")


class NoExactJumpBackend(RuntimeError):
    pass


@runtime_checkable
class ExactJumpBackend(Protocol[RootT]):
    def seed_root(self) -> RootT: ...
    def jump_bit(self, prefix_index: int, root: RootT, bit: int) -> RootT: ...


@dataclass(frozen=True, slots=True)
class IndexedRoot(Generic[RootT]):
    index: int
    root: RootT
    jump_calls: int
    audit: JumpAuditSnapshot


class StrictBinaryRootBuilder(Generic[RootT]):
    __slots__ = ("jump_backend",)

    def __init__(self, jump_backend: ExactJumpBackend[RootT]):
        if not isinstance(jump_backend, ExactJumpBackend):
            raise TypeError("jump backend does not implement ExactJumpBackend")
        self.jump_backend = jump_backend

    def root_at(self, n: int) -> IndexedRoot[RootT]:
        n = int(n)
        if n < 0:
            raise ValueError(n)
        root = self.jump_backend.seed_root()
        audit = JumpAudit()
        if n == 0:
            return IndexedRoot(0, root, 0, audit.snapshot())
        prefix = 0
        calls = 0
        for bit in map(int, bin(n)[2:]):
            with powered_jump_scope(audit):
                audit.jump_calls += 1
                root = self.jump_backend.jump_bit(prefix, root, bit)
            prefix = 2 * prefix + bit
            calls += 1
        snap = audit.snapshot()
        if not snap.clean:
            # Normally impossible because forbidden operations raise at the call
            # site.  Keep this postcondition as defense in depth.
            raise AssertionError(f"dirty jump audit: {snap.forbidden_attempts}")
        return IndexedRoot(n, root, calls, snap)


class MissingJumpBackend(Generic[RootT]):
    __slots__ = ("_seed",)

    def __init__(self, seed_root: RootT) -> None:
        self._seed = seed_root

    def seed_root(self) -> RootT:
        return self._seed

    def jump_bit(self, prefix_index: int, root: RootT, bit: int) -> RootT:
        raise NoExactJumpBackend(
            f"No exact J_{bit} installed for {prefix_index}->{2 * prefix_index + bit}"
        )


__all__ = [
    "ExactJumpBackend",
    "IndexedRoot",
    "MissingJumpBackend",
    "NoExactJumpBackend",
    "StrictBinaryRootBuilder",
]
