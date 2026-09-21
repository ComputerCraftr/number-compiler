"""Compressed carry observation of the bounded live-forcing residue view.

The input is the pair field P modulo 32, not its derivative or centered Delta.
A caller must separately establish P in [0,18] on the admitted source before
interpreting this arithmetic observation as that source's exact carries.
The returned SLP is a projection and cannot authorize a temporal successor.
"""

from number_compiler.arithmetic.automata.residue_carry_slp import (
    ResidueCarrySLPProjector,
    ResidueCarrySLPResult,
)
from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.fields.centered_carry import uncenter_pair_field
from number_compiler.arithmetic.fields.live_forcing import LiveForcingProjection
from number_compiler.arithmetic.fields.symbolic_innovation import (
    InnovationID,
    SymbolicInnovationArena,
)


def project_live_pair_carries(
    view: LiveForcingProjection, *, start: int, stop: int, incoming: int = 0
) -> ResidueCarrySLPResult:
    """Feed compressed modular intervals to the existing grammar transducer.

    No integer positions or represented carry words are visited. Input grammar
    construction is charged before allocation and discarded after projection.
    The caller owns the returned result and must close it after observation.
    """
    if type(view) is not LiveForcingProjection:
        raise TypeError("carry projection requires the bounded forcing view")
    if view.bits != 5:
        raise ValueError("decimal pair carry projection requires modulo 32")
    if type(incoming) is not int or incoming not in (0, 1):
        raise ValueError("incoming carry must be zero or one")
    ledger = view.ledger
    owner = ledger.register(f"live-carry-input-{ledger.owner_count}", "query_memo")
    units = 0
    grammar: SLPArena | None = None
    projector: ResidueCarrySLPProjector | None = None
    try:
        # Admit the initial empty grammar node before constructing the arena.
        ledger.reserve(owner, nodes=1)
        units = 1
        grammar = SLPArena()
        root = grammar.empty()
        runs = view.residue_runs(start, stop)
        ledger.reserve(owner, nodes=3 * len(runs))
        units += 3 * len(runs)
        for run in runs:
            if not 0 <= run.residue <= 18:
                raise ValueError("pair residue is outside the decimal pair range")
            # At most terminal, repeat and concat; intern hits are conservatively
            # admitted too. Length arithmetic uses binary metadata, not a scan.
            size = run.stop - run.start
            required = 3 + 3 * max(1, (size.bit_length() + 63) // 64)
            ledger.reserve(owner, nodes=required)
            units += required
            leaf = grammar.terminal(run.residue)
            repeated = grammar.repeat(leaf, size)
            root = grammar.concat(root, repeated)
            ledger.bump("live_carry_input_runs")
        projector = ResidueCarrySLPProjector(ledger)
        result = projector.project(grammar, grammar.nodes[root], incoming=incoming)
        ledger.bump("live_carry_input_nodes", len(grammar.nodes))
        return result
    finally:
        if projector is not None:
            projector.close()
        if grammar is not None:
            grammar.nodes.clear()
            grammar._cat.clear()
            grammar._rep.clear()
            grammar._term.clear()
        ledger.release(owner, nodes=units)
        ledger.mark_disposed(owner)


def project_centered_residue_carries(
    arena: SymbolicInnovationArena,
    residual: InnovationID,
    *,
    extent: int,
    incoming: int = 0,
) -> ResidueCarrySLPResult:
    """Observe Delta through P=Delta+9E_m, preserving the polynomial basis.

    This uses the existing symbolic uncentering law and bounded modulo-32
    projection. It does not infer that supplied Delta is source-reachable.
    """
    if type(incoming) is not int or incoming not in (0, 1):
        raise ValueError("incoming carry must be zero or one")
    pair = uncenter_pair_field(arena, residual, extent=extent)
    with LiveForcingProjection(arena, pair) as view:
        return project_live_pair_carries(view, start=0, stop=extent, incoming=incoming)
