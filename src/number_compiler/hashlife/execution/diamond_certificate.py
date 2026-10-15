"""Evidence that a root uses the executable, output-complete diamond algebra."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.execution.diamond_law_contracts import (
    BIMACHINE_TWO_SIDED_SUBSTITUTION_LAW,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


@dataclass(frozen=True, slots=True)
class DiamondCompositionCertificate:
    root: ActionProgramID
    kernels: tuple[tuple[ActionProgramID, ActionProgramID], ...]
    law: str = BIMACHINE_TWO_SIDED_SUBSTITUTION_LAW

    def validate(self, runtime: DiamondRuntime, root: ActionProgramID) -> bool:
        """Read-only validation; a compiler node count is not execution evidence."""
        if self.root != root or self.law != BIMACHINE_TWO_SIDED_SUBSTITUTION_LAW:
            return False
        runtime.actions.resolve(root)
        admitted = dict(self.kernels)
        pending = [root]
        seen: set[int] = set()
        while pending:
            action = pending.pop()
            node = runtime.actions.resolve(action)
            if action.local_id in seen:
                continue
            seen.add(action.local_id)
            if node.kind == "compose":
                pending.extend(
                    (
                        runtime.actions.reference(node.first),
                        runtime.actions.reference(node.second),
                    )
                )
            elif node.kind == "atom":
                handle = admitted.get(action)
                if handle is None:
                    return False
                kernel = runtime.kernels.kernel(handle)
                if runtime.actions.primitive(action) is not kernel.effect:
                    return False
        return True


def certify(
    runtime: DiamondRuntime, root: ActionProgramID
) -> DiamondCompositionCertificate:
    """Admit only complete immutable primitive interfaces, then bind the root."""
    pending = [root]
    seen: set[int] = set()
    kernels: list[tuple[ActionProgramID, ActionProgramID]] = []
    visits = peak = 0
    while pending:
        peak = max(peak, len(pending))
        visits += 1
        action = pending.pop()
        node = runtime.actions.resolve(action)
        if action.local_id in seen:
            continue
        seen.add(action.local_id)
        if node.kind == "compose":
            pending.extend(
                (
                    runtime.actions.reference(node.first),
                    runtime.actions.reference(node.second),
                )
            )
        elif node.kind == "atom":
            handle = runtime.kernels.intern(runtime.actions.primitive(action))
            kernels.append((action, handle))
    runtime.ledger.bump(_execution_keys.DIAMOND_CERTIFICATE_CONSTRUCTION_VISITS, visits)
    prior = runtime.ledger.counters.get(
        _execution_keys.DIAMOND_CERTIFICATE_CONSTRUCTION_STACK_PEAK, 0
    )
    runtime.ledger.bump(
        _execution_keys.DIAMOND_CERTIFICATE_CONSTRUCTION_STACK_PEAK,
        max(0, peak - prior),
    )
    return DiamondCompositionCertificate(root, tuple(kernels))
