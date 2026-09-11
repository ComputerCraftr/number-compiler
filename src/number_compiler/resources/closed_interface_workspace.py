"""Ledger-owned bounded workspace for closed arithmetic interfaces."""

from __future__ import annotations

from collections.abc import Iterator
from contextlib import contextmanager
from typing import Literal

from number_compiler.resources.ledger import ResourceLedger


# Leaf construction retains at most 24 closed-function slots, a 76-slot sector
# summary, two MacroComponents records, and bounded codec/signature scratch.
_LEAF_NODES = 128
# Parent construction additionally holds four 13-channel reference tuples and
# the fixed m=1,2,4,8 sector shifts.  Their final 75 limbs and at most 225
# simultaneous shift/add limbs fit with the closed records below this bound.
_PARENT_NODES = 512


class ClosedInterfaceWorkspace:
    """Track the live allocation bound while closed records become retained."""

    __slots__ = ("ledger", "owner", "nodes")

    def __init__(self, ledger: ResourceLedger, prefix: str) -> None:
        self.ledger = ledger
        self.owner = ledger.register(
            prefix + "-closed-workspace", "closed_interface_workspace"
        )
        self.nodes = 0
        ledger.register_container(
            self.owner,
            self,
            node_count=lambda: self.nodes,
            payloads=lambda: (),
        )

    def __len__(self) -> int:
        return 0

    @contextmanager
    def scope(self, kind: Literal["leaf", "parent"]) -> Iterator[None]:
        if self.nodes:
            raise RuntimeError("closed interface workspace is already active")
        if kind not in ("leaf", "parent"):
            raise ValueError("unknown closed interface construction kind")
        nodes = _LEAF_NODES if kind == "leaf" else _PARENT_NODES
        self.ledger.reserve(self.owner, nodes=nodes)
        self.nodes = nodes
        peak = self.ledger.counters.get("reverse_port_construction_workspace_peak", 0)
        if nodes > peak:
            self.ledger.bump("reverse_port_construction_workspace_peak", nodes - peak)
        try:
            yield
        finally:
            self.ledger.release(self.owner, nodes=nodes)
            self.nodes = 0


__all__ = ["ClosedInterfaceWorkspace"]
