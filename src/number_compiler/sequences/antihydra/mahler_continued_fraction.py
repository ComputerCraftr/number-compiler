"""Finite ordered continued-fraction projections of the decimal powers of five.

A band belongs to one exponent/cut clock and retains chronological row order.
The source certificate is the lifted dyadic value; equal observed rows alone
cannot authorize a repeat.
"""

from __future__ import annotations

from contextlib import AbstractContextManager, nullcontext
from typing import TYPE_CHECKING, Final

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_integer_tuple,
    is_exact_object_tuple,
    require_integer,
)
from number_compiler.arithmetic.fields.ordered_matrix import (
    Matrix2,
    compile_dyadic_ordered_band,
    fold_fixed_decimal_row,
)
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.resources.process_cache import CacheLease

_BAND_NAMESPACE: Final = "mahler-cf-diagonal"
_BAND_VERSION: Final = "1"
_BAND_ACTION_ISSUER = object()


def _checked_cached_band(lease: CacheLease, cut: int) -> tuple[int, Matrix2] | None:
    response = lease.get_issued((cut,), _BAND_ACTION_ISSUER, None)
    if response is None:
        return None
    if is_exact_object_tuple(response) and len(response) == 2:
        quotient, entries = response
        if type(quotient) is int and quotient >= 0 and is_exact_integer_tuple(entries):
            if len(entries) == 4:
                a, b, c, d = entries
                return quotient, Matrix2((a, b, c, d))
    raise ValueError("continued-fraction cache returned an invalid issued band")


def _drop_first_band_row(quotient: int, width: int, product: Matrix2) -> Matrix2:
    row = fold_fixed_decimal_row(
        quotient % 10**width, 10 ** (width - 1), Matrix2.identity()
    )
    a, b, c, d = row.entries
    sign = 1 if width % 2 == 0 else -1
    return Matrix2((sign * d, -sign * b, -sign * c, sign * a)).multiply(product)


def validate_cf_resources(ledger: ResourceLedger, shared_cache: bool) -> None:
    if type(ledger) is not ResourceLedger:
        raise TypeError("continued-fraction projection requires its query ledger")
    if type(shared_cache) is not bool:
        raise TypeError("shared cache selector must be Boolean")


def continuant_rows(matrix: Matrix2) -> tuple[tuple[int, int], tuple[int, int]]:
    a, b, c, d = matrix.entries
    return ((a, b), (c, d))


def continued_fraction_band(
    exponent: int,
    cut: int,
    width: int,
    rows: int,
    *,
    ledger: ResourceLedger,
    shared_cache: bool = True,
) -> dict[str, object]:
    """Project an exact ordered CF matrix from one certified physical band."""
    validate_cf_resources(ledger, shared_cache)
    require_integer(exponent, "source exponent", 1, 4096)
    require_integer(cut, "decimal cut", 1, exponent)
    require_integer(width, "band width", 1, min(cut, 128))
    require_integer(rows, "band rows", 1, 4096)
    if rows * width > 4096 or exponent + rows - 1 > 4096:
        raise ValueError("continued-fraction band exceeds its finite source budget")
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "mahler-cf-band")
    scope: AbstractContextManager[CacheLease | None] = nullcontext()
    if shared_cache and exponent >= 1024 and rows >= 6 and rows * width >= 1024:
        from number_compiler.resources.process_cache import get_process_cache

        cache = get_process_cache()
        if cache.enabled:
            try:
                scope = cache.acquire(
                    _BAND_NAMESPACE,
                    _BAND_VERSION,
                    (exponent - cut, width, cut + rows - 1),
                )
            except BlockContextBudgetExceeded:
                # A process lease is optional. The query ledger still decides
                # whether the existing exact constructor can run.
                pass
    with scope as lease:
        with scratch.scope():
            action = _band_action(
                exponent, cut, width, rows, scratch, shared_cache, lease
            )
        packet: dict[str, object] = {
            "source_law": "decimal-powers-of-five",
            "clock_unit": "power-of-five-exponent",
            "exponent": exponent,
            "cut": cut,
            "width": width,
            "rows": rows,
        }
        if action is None:
            return {
                "status": "unavailable",
                "reason": "moving band leaves the significant source digits",
                **packet,
            }
        quotient, product, retained = action
        if lease is not None and not retained:
            lease.put_issued((cut,), (quotient, product.entries), _BAND_ACTION_ISSUER)
        return {
            "status": "available",
            **packet,
            "lifted_source": quotient,
            "coefficient_count": rows * width,
            "matrix": continuant_rows(product),
            "orientation": "msd-first-right-product",
            "authority_scope": "bounded-physical-diagonal-band",
        }


def _band_action(
    exponent: int,
    cut: int,
    width: int,
    rows: int,
    scratch: RunArithmeticWorkspace,
    shared_cache: bool,
    lease: CacheLease | None,
) -> tuple[int, Matrix2, bool] | None:
    scratch.require_bits(16 * (3 * exponent + cut + rows + 4 * width + 128))
    direct_bits = 32 * (3 * exponent + cut + rows + 8 * rows * width + 128)
    if lease is not None:
        # The source binding fixes the diagonal origin, significant-width
        # inequality, and lift precision before deciding the requested cut.
        same = _checked_cached_band(lease, cut)
        previous = (
            _checked_cached_band(lease, cut - 1)
            if same is None and cut > width
            else None
        )
        following = (
            _checked_cached_band(lease, cut + 1)
            if same is None and previous is None
            else None
        )
        if same is not None or previous is not None or following is not None:
            try:
                scratch.require_bits(direct_bits)
            except BlockContextBudgetExceeded:
                # The current query may still admit the exact fallback.
                pass
            else:
                if same is not None:
                    return same[0], same[1], True
                if previous is not None:
                    q, action = previous
                    return q >> 1, _drop_first_band_row(q, width, action), False
                assert following is not None
                q, action = following
                # The cached band begins one row later at the same endpoint.
                # Recover the missing low lift bit at precisely the required
                # precision, then prepend the admitted first row.
                low = 10**width * int.__pow__(5, exponent - cut, 1 << (cut + 1))
                quotient = 2 * q + ((low >> cut) & 1)
                first = fold_fixed_decimal_row(
                    quotient % 10**width,
                    10 ** (width - 1),
                    Matrix2.identity(),
                )
                return quotient, first.multiply(action), False

    # Significant-width admission is invariant on the same ended diagonal.
    if pow(5, exponent - cut + 1) < 1 << (cut + rows - 2):
        return None
    base = 10**width
    modulus = 1 << (cut + rows - 1)
    quotient = base * int.__pow__(5, exponent - cut, modulus) >> cut

    def reserve_action(_q: int, _count: int, retained_bits: int) -> None:
        # The direct admission bound already covers disjoint pending children
        # and their ordered products. Charge only additional retained motifs.
        scratch.require_bits(direct_bits + retained_bits)

    memo = shared_cache and width == 1
    try:
        product = compile_dyadic_ordered_band(
            quotient, rows, width, reserve_action, use_memo=memo
        )
    except BlockContextBudgetExceeded:
        if not memo:
            raise
        # Optional memo admission must not reject a previously feasible
        # exact action. Retry before opening any children, without memo.
        product = compile_dyadic_ordered_band(
            quotient, rows, width, reserve_action, use_memo=False
        )
    return quotient, product, False
