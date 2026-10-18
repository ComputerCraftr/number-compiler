from __future__ import annotations

from collections.abc import Iterable, Sequence
from typing import Any

from number_compiler.arithmetic.formula.types import Expr, FormulaStorage, _bits, _mask


class FormulaBuildMixin(FormulaStorage):
    """Hash-consing and symbolic-construction half of :class:`FormulaArena`."""

    __slots__ = ()

    def __init__(self) -> None:
        self._next_id = 1
        self._nodes: dict[tuple[object, ...], Expr] = {}
        self._closed_known: dict[int, int] = {}
        self._closed_values: dict[int, int] = {}
        self._closed_bit_count = 0
        self._derived: dict[tuple[object, ...], Expr] = {}
        self._metadata: dict[tuple[object, ...], Any] = {}

    def _raw(
        self,
        kind: str,
        width: int,
        args: Iterable[Expr] = (),
        param: Iterable[int | str] = (),
        pbits: int = 0,
    ) -> Expr:
        from number_compiler.arithmetic.automata.guard import record_symbolic_op

        record_symbolic_op(kind)
        width = int(width)
        if width <= 0:
            raise ValueError(width)
        args = tuple(args)
        for argument in args:
            self.require_owned(argument)
        param = tuple(param)
        key = (kind, width, tuple(a.id for a in args), param)
        old = self._nodes.get(key)
        if old is not None:
            return old
        node = Expr(self._next_id, kind, width, args, param, int(pbits) + _bits(width))
        self._next_id += 1
        self._nodes[key] = node
        return node

    def zero(self, width: int) -> Expr:
        return self._raw("ZERO", width)

    def ones(self, width: int) -> Expr:
        return self._raw("ONES", width)

    def literal(self, value: int, width: int) -> Expr:
        from number_compiler.arithmetic.automata.guard import forbid_in_powered_jump

        forbid_in_powered_jump("literal")
        return self._raw(
            "LITERAL", width, param=(int(value) & _mask(width),), pbits=int(width)
        )

    def variable(self, slot: int, width: int) -> Expr:
        slot = int(slot)
        if slot < 0:
            raise ValueError(slot)
        return self._raw("VAR", width, param=(slot,), pbits=_bits(slot))

    def range_mask(self, lo: int, hi: int, width: int) -> Expr:
        lo, hi, width = int(lo), int(hi), int(width)
        if not 0 <= lo <= hi <= width:
            raise ValueError((lo, hi, width))
        if lo == hi:
            return self.zero(width)
        if lo == 0 and hi == width:
            return self.ones(width)
        return self._raw("RANGE", width, param=(lo, hi), pbits=_bits(lo) + _bits(hi))

    def not_(self, x: Expr) -> Expr:
        self.require_owned(x)
        if x.kind == "ZERO":
            return self.ones(x.width)
        if x.kind == "ONES":
            return self.zero(x.width)
        if x.kind == "NOT":
            return x.args[0]
        return self._raw("NOT", x.width, (x,))

    def _flatten(self, kind: str, items: Iterable[Expr]) -> list[Expr]:
        out: list[Expr] = []
        for item in items:
            self.require_owned(item)
            out.extend(item.args if item.kind == kind else (item,))
        return out

    @staticmethod
    def _complements(items: Iterable[Expr]) -> tuple[set[int], set[int]]:
        pos, neg = set(), set()
        for item in items:
            if item.kind == "NOT":
                neg.add(item.args[0].id)
            else:
                pos.add(item.id)
        return pos, neg

    def _shallow_many(self, kind: str, items: Iterable[Expr], width: int) -> Expr:
        """Build one Boolean layer without recursive factoring.

        ``and_many``/``or_many``/``xor_many`` use this after they have already
        proved a reconvergent factorization.  The old implementation called the
        public combiners again, creating direct/mutual recursion merely to
        canonicalize the newly exposed one-level residual.  One local pass is
        sufficient here and keeps formula construction stack-bounded.
        """
        args = tuple(items)
        if kind == "AND":
            if not args:
                return self.ones(width)
            if len(args) == 1:
                return args[0]
        elif kind in ("OR", "XOR"):
            if not args:
                return self.zero(width)
            if len(args) == 1:
                return args[0]
        else:
            raise ValueError(kind)
        return self._raw(kind, width, sorted(args, key=lambda x: x.id))

    def and_many(self, items: Iterable[Expr], width: int) -> Expr:
        width = int(width)
        flat = self._flatten("AND", items)
        if not flat:
            return self.ones(width)
        if any(x.width != width for x in flat):
            raise ValueError("width mismatch")
        if any(x.kind == "ZERO" for x in flat):
            return self.zero(width)
        flat = [x for x in flat if x.kind != "ONES"]
        if not flat:
            return self.ones(width)
        flat = list({x.id: x for x in flat}.values())
        pos, neg = self._complements(flat)
        if pos & neg:
            return self.zero(width)
        atomic = {x.id for x in flat if x.kind != "OR"}
        if atomic:
            flat = [
                x
                for x in flat
                if not (x.kind == "OR" and any(a.id in atomic for a in x.args))
            ]
        if len(flat) == 1:
            return flat[0]
        # Diamond factoring: (a|b)&(a|c) -> a|(b&c).  Hash-consing alone
        # cannot discover this reconvergent equivalence because the two parent
        # nodes have different child tuples.  Factoring before interning keeps
        # the common dependency once.
        if len(flat) >= 2 and all(x.kind == "OR" for x in flat):
            common_ids = {a.id for a in flat[0].args}
            for term in flat[1:]:
                common_ids.intersection_update(a.id for a in term.args)
            if common_ids:
                by_id = {a.id: a for a in flat[0].args}
                common = [by_id[i] for i in sorted(common_ids)]
                residual = [
                    self._shallow_many(
                        "OR", (a for a in term.args if a.id not in common_ids), width
                    )
                    for term in flat
                ]
                inner = self._shallow_many("AND", residual, width)
                return self._shallow_many("OR", (*common, inner), width)
        return self._raw("AND", width, sorted(flat, key=lambda x: x.id))

    def _factor_conjunctions(
        self, terms: Sequence[Expr], common_ids: set[int], kind: str, width: int
    ) -> Expr:
        by_id = {argument.id: argument for argument in terms[0].args}
        common = [by_id[index] for index in sorted(common_ids)]
        residual = [
            self._shallow_many(
                "AND",
                (argument for argument in term.args if argument.id not in common_ids),
                width,
            )
            for term in terms
        ]
        inner = self._shallow_many(kind, residual, width)
        return self._shallow_many("AND", (*common, inner), width)

    def or_many(self, items: Iterable[Expr], width: int) -> Expr:
        width = int(width)
        flat = self._flatten("OR", items)
        if not flat:
            return self.zero(width)
        if any(x.width != width for x in flat):
            raise ValueError("width mismatch")
        if any(x.kind == "ONES" for x in flat):
            return self.ones(width)
        flat = [x for x in flat if x.kind != "ZERO"]
        if not flat:
            return self.zero(width)
        flat = list({x.id: x for x in flat}.values())
        pos, neg = self._complements(flat)
        if pos & neg:
            return self.ones(width)
        atomic = {x.id for x in flat if x.kind != "AND"}
        if atomic:
            flat = [
                x
                for x in flat
                if not (x.kind == "AND" and any(a.id in atomic for a in x.args))
            ]
        if len(flat) == 1:
            return flat[0]
        # Dual reconvergence factoring: (a&b)|(a&c) -> a&(b|c).
        if len(flat) >= 2 and all(x.kind == "AND" for x in flat):
            common_ids = {a.id for a in flat[0].args}
            for term in flat[1:]:
                common_ids.intersection_update(a.id for a in term.args)
            if common_ids:
                return self._factor_conjunctions(flat, common_ids, "OR", width)
        return self._raw("OR", width, sorted(flat, key=lambda x: x.id))

    def xor_many(self, items: Iterable[Expr], width: int) -> Expr:
        width = int(width)
        flat = self._flatten("XOR", items)
        if any(x.width != width for x in flat):
            raise ValueError("width mismatch")
        parity: dict[int, Expr] = {}
        invert = False
        for x in flat:
            if x.kind == "ZERO":
                continue
            if x.kind == "ONES":
                invert = not invert
                continue
            if x.id in parity:
                del parity[x.id]
            else:
                parity[x.id] = x
        args = sorted(parity.values(), key=lambda x: x.id)
        if not args:
            out = self.zero(width)
        elif len(args) == 1:
            out = args[0]
        elif all(x.kind == "AND" for x in args):
            common_ids = {a.id for a in args[0].args}
            for term in args[1:]:
                common_ids.intersection_update(a.id for a in term.args)
            if common_ids:
                out = self._factor_conjunctions(args, common_ids, "XOR", width)
            else:
                out = self._raw("XOR", width, args)
        else:
            out = self._raw("XOR", width, args)
        return self.not_(out) if invert else out

    def and_(self, a: Expr, b: Expr) -> Expr:
        if a.width != b.width:
            raise ValueError((a.width, b.width))
        return self.and_many((a, b), a.width)

    def or_(self, a: Expr, b: Expr) -> Expr:
        if a.width != b.width:
            raise ValueError((a.width, b.width))
        return self.or_many((a, b), a.width)

    def xor(self, a: Expr, b: Expr) -> Expr:
        if a.width != b.width:
            raise ValueError((a.width, b.width))
        return self.xor_many((a, b), a.width)

    def _shift(self, x: Expr, amount: int, kind: str) -> Expr:
        self.require_owned(x)
        amount = int(amount)
        if kind not in ("SHL", "SHR"):
            raise ValueError(kind)
        if amount < 0:
            amount = -amount
            kind = "SHR" if kind == "SHL" else "SHL"
        if amount == 0:
            return x
        if amount >= x.width or x.kind == "ZERO":
            return self.zero(x.width)
        # Collapse chains iteratively; no recursive opposite-shift dispatch.
        while x.kind == kind:
            amount += int(x.param[0])
            x = x.args[0]
            if amount >= x.width or x.kind == "ZERO":
                return self.zero(x.width)
        return self._raw(kind, x.width, (x,), (amount,), _bits(amount))

    def shl(self, x: Expr, amount: int) -> Expr:
        return self._shift(x, amount, "SHL")

    def shr(self, x: Expr, amount: int) -> Expr:
        return self._shift(x, amount, "SHR")

    def mirror(self, x: Expr) -> Expr:
        self.require_owned(x)
        if x.kind in ("ZERO", "ONES"):
            return x
        if x.kind == "MIRROR":
            return x.args[0]
        return self._raw("MIRROR", x.width, (x,))

    def resize(self, x: Expr, width: int) -> Expr:
        self.require_owned(x)
        width = int(width)
        if width < x.width:
            raise ValueError("resize only zero-extends")
        if width == x.width:
            return x
        if x.kind == "ZERO":
            return self.zero(width)
        return self._raw("PAD_RIGHT", width, (x,), (x.width,), _bits(x.width))

    def crop(self, x: Expr, width: int) -> Expr:
        """Keep the least-significant ``width`` positions without materializing."""
        self.require_owned(x)
        width = int(width)
        if width <= 0 or width > x.width:
            raise ValueError((x.width, width))
        if width == x.width:
            return x
        if x.kind == "ZERO":
            return self.zero(width)
        if x.kind == "ONES":
            return self.ones(width)
        while x.kind == "CROP":
            x = x.args[0]
            if width == x.width:
                return x
        return self._raw("CROP", width, (x,), (x.width,), _bits(x.width))

    def predicate(self, op: str, threshold: int, planes: Sequence[Expr]) -> Expr:
        planes = tuple(planes)
        if not planes:
            raise ValueError("empty planes")
        width = planes[0].width
        if any(p.width != width for p in planes):
            raise ValueError("plane width mismatch")
        if op not in ("EQ", "GT"):
            raise ValueError(op)
        return self._raw(
            "PRED", width, planes, (op, int(threshold)), _bits(threshold) + 1
        )

    def ite(self, selector: Expr, when_false: Expr, when_true: Expr) -> Expr:
        """Canonical pointwise if-then-else used by reduced decision DAGs."""
        for argument in (selector, when_false, when_true):
            self.require_owned(argument)
        if selector.width != when_false.width or selector.width != when_true.width:
            raise ValueError((selector.width, when_false.width, when_true.width))
        if when_false.id == when_true.id:
            return when_false
        if selector.kind == "ZERO":
            return when_false
        if selector.kind == "ONES":
            return when_true
        if when_false.kind == "ZERO" and when_true.kind == "ONES":
            return selector
        if when_false.kind == "ONES" and when_true.kind == "ZERO":
            return self.not_(selector)
        return self._raw("ITE", selector.width, (selector, when_false, when_true))

    def boolfunc(self, args: Sequence[Expr], truth_table: int) -> Expr:
        """Canonical bounded pointwise Boolean function.

        The truth table uses little-endian assignment indices: argument ``j``
        contributes bit ``j``.  Duplicate and inessential arguments are removed
        and the surviving arguments are ordered by canonical Expr id.  The full
        truth table is retained in the node parameters and charged in
        ``local_param_bits``; this primitive therefore cannot hide an unbounded
        Boolean relation behind a constant-size token.
        """
        args = tuple(args)
        if not args:
            raise ValueError("BOOLFUNC requires at least one width-bearing argument")
        for argument in args:
            self.require_owned(argument)
        width = args[0].width
        if any(a.width != width for a in args):
            raise ValueError("BOOLFUNC width mismatch")
        n = len(args)
        if n > 16:
            raise ValueError("BOOLFUNC arity is deliberately bounded")
        table = int(truth_table) & ((1 << (1 << n)) - 1)

        # Canonicalize duplicate arguments and argument order by translating the
        # complete table onto the sorted unique argument tuple.
        unique = tuple(sorted({a.id: a for a in args}.values(), key=lambda a: a.id))
        if unique != args:
            pos_by_id = {a.id: j for j, a in enumerate(unique)}
            reduced = 0
            for assignment in range(1 << len(unique)):
                old_assignment = 0
                for old_j, arg in enumerate(args):
                    old_assignment |= ((assignment >> pos_by_id[arg.id]) & 1) << old_j
                reduced |= ((table >> old_assignment) & 1) << assignment
            args, table, n = unique, reduced, len(unique)

        # Exact essential-variable reduction.
        keep: list[tuple[int, Expr]] = []
        for j, arg in enumerate(args):
            dependent = False
            for assignment in range(1 << n):
                if (assignment >> j) & 1:
                    continue
                if ((table >> assignment) & 1) != (
                    (table >> (assignment | (1 << j))) & 1
                ):
                    dependent = True
                    break
            if dependent:
                keep.append((j, arg))
        if len(keep) != n:
            new_args = tuple(arg for _, arg in keep)
            new_table = 0
            for assignment in range(1 << len(new_args)):
                old_assignment = 0
                for new_j, (old_j, _arg) in enumerate(keep):
                    old_assignment |= ((assignment >> new_j) & 1) << old_j
                new_table |= ((table >> old_assignment) & 1) << assignment
            args, table, n = new_args, new_table, len(new_args)

        if n == 0:
            return self.ones(width) if table & 1 else self.zero(width)
        if n == 1:
            if table == 0b10:
                return args[0]
            if table == 0:
                return self.zero(width)
            if table == 0b11:
                return self.ones(width)
        return self._raw(
            "BOOLFUNC",
            width,
            args,
            (table,),
            pbits=(1 << n) + _bits(n),
        )

    def coeffmap(
        self, mode: str, bit: int, base: int, nplanes: int, args: Sequence[Expr]
    ) -> Expr:
        args = tuple(args)
        if not args:
            raise ValueError("empty coeffmap")
        width = args[0].width
        if any(a.width != width for a in args):
            raise ValueError("width mismatch")
        if mode not in (
            "NO_GROWTH",
            "GROWTH_INTERNAL",
            "GROWTH_EDGE",
            "DIGIT_NORMALIZE",
        ):
            raise ValueError(mode)
        return self._raw(
            "COEFFMAP",
            width,
            args,
            (mode, int(bit), int(base), int(nplanes)),
            _bits(base) + _bits(bit) + _bits(nplanes) + 2,
        )
