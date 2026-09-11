"""Scale-free S/M/B formula views derived from the canonical pair FormulaRoot.

These are *views*, not additional semantic state.  They provide the useful
single-B carry representation to materializers and powered/source-transducer
code without duplicating pair/carry data.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.formula.derived import border_view, threshold_views
from number_compiler.arithmetic.formula.formula import (
    FormulaArena,
    FormulaRoot,
    canonical_root_key,
)
from number_compiler.arithmetic.formula.types import RadixSpec


@dataclass(frozen=True, slots=True)
class SMBFormulaView:
    pair: FormulaRoot  # S coefficient bit planes
    domain: FormulaRoot  # M values: R0=0, I=1, R1=2
    border: FormulaRoot  # B_i = L_i xor L_(i+1), one binary plane

    @property
    def width(self) -> int:
        return self.pair.width


def smb_formula_view(
    arena: FormulaArena, pair: FormulaRoot, spec: RadixSpec
) -> SMBFormulaView:
    key = ("smb-formula-view", spec.base, canonical_root_key(pair))
    cached = arena.metadata_get(key)
    if isinstance(cached, SMBFormulaView):
        return cached
    _less, equal, greater = threshold_views(arena, pair, spec)
    # Ternary monoid labels use exact binary encoding 0,1,2.
    domain = FormulaRoot((equal, greater))
    border = FormulaRoot((border_view(arena, pair, spec),))
    view = SMBFormulaView(pair, domain, border)
    arena.metadata_set(key, view)
    return view


__all__ = ["SMBFormulaView", "smb_formula_view"]
