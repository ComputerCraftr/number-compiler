"""Small executable checks for current lazy compiler contracts."""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.contracts.block_effect import _effect_key
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.actions.lazy_compiler import (
    LazyCompiler,
    ProgramComposition,
    UnsupportedInterfaceError,
)
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics


class _SameKeyImpostor(BaseBlockEffect):
    def emit(self, left: object, symbol: int, right: object) -> int:
        return 0


def current_lazy_compiler_checks() -> dict[str, bool]:
    left, right = LazyCompiler(ResourceLedger()), LazyCompiler(ResourceLedger())
    atom = left.atom(BaseBlockEffect(10))
    other = right.atom(BaseBlockEffect(10))
    local, foreign = left.compose(atom, atom), right.compose(other, other)
    before = left.ledger.snapshot()
    rejected = 0
    operations: tuple[Callable[[], object], ...] = (
        lambda: left.compose(foreign, atom),
        lambda: left.power(foreign, 0),
    )
    for operation in operations:
        try:
            operation()
        except ValueError:
            rejected += 1
    ownership = rejected == 2 and left.ledger.snapshot() == before
    semantic = local is not foreign and _effect_key(local) == _effect_key(foreign)
    admission = False
    try:
        left.compose(atom, _SameKeyImpostor(10))
    except UnsupportedInterfaceError:
        admission = left.ledger.snapshot() == before
    program = left.compose(atom, left.atom(DigitNormalizeBlockEffect(10)))
    application = HashLifeBlockIndex(
        program,
        (2,),
        logical_length=3,
        ledger=left.ledger,
        compiler=left,
    )
    # One reverse-add step sends pair2 to pair4; normalization emits digit4.
    exact = (
        application.direct_powered_point(0) == 4
        and application.direct_active_width() == 1
    )
    metrics = collect_ledger_metrics(left.ledger)
    complete = (
        metrics.resource_audit_complete == 1 and metrics.forbidden_future_payloads == 0
    )
    return {
        "compiler_program_ids_are_owner_scoped_before_shortcuts": ownership,
        "compiler_program_identity_is_semantic_across_owners": semantic,
        "lazy_compiler_admits_definitions_before_warm_lookup": admission,
        "lazy_composition_projects_complete_outputs_without_partition_product": (
            isinstance(program, ProgramComposition)
            and not hasattr(program, "_left_partition")
            and exact
            and complete
        ),
    }
