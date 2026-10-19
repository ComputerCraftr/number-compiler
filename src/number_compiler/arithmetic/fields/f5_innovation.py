"""F5 affine forcing composition in the existing ledger-owned innovation DAG.

This binds the production Frobenius operator to shared arithmetic handles.
The resulting integer expressions represent forcing modulo five only. They
must not replace an exact decimal innovation or an authenticated source image.
Both forcing operands must already be pulled back into the same source/chart
environment. This operation neither discovers nor certifies that environment.
"""

from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.fields.radial_innovation import InnovationID
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.arithmetic.polynomials.f5_transport import F5AffineTransport
from number_compiler.resources.metric_keys import (
    arithmetic_fields as _fields_keys,
)


def compose_f5_forcing(
    arena: SymbolicInnovationArena,
    before: F5AffineTransport[InnovationID],
    after: F5AffineTransport[InnovationID],
) -> F5AffineTransport[InnovationID]:
    """Construct ``L_after B_before + B_after`` without visiting coefficients.

    Shift/add callbacks intern closed charts and shared sum nodes. Existing
    arena admission accounts for retained integer sizes and normalization work.
    For the later growth exponent r, construction uses sum(base5_digits(r))
    shifts and additions, plus a scale and the final forcing addition. This
    counts arithmetic construction only, not discovery or evaluation of atoms.
    """
    if type(arena) is not SymbolicInnovationArena:
        raise TypeError("F5 forcing requires the ledger-owned innovation arena")
    if type(before) is not F5AffineTransport or type(after) is not F5AffineTransport:
        raise TypeError("F5 forcing requires two typed affine transports")
    # Validate both operands before constructing anything, even if the later
    # forcing or a homogeneous factor might simplify away a dependency.
    arena.resolve(before.forcing)
    arena.resolve(after.forcing)
    combined = before.linear.then(after.linear)
    arena.ledger.bump(_fields_keys.SYMBOLIC_INNOVATION_F5_COMPOSITION_REQUESTS)
    metadata_bits = max(1, after.linear.no_growths.bit_length()) + max(
        1, after.linear.growths.bit_length()
    )
    memo = arena.f5_composition_cache((metadata_bits + 63) // 64)
    key = (
        arena.copy_reference(before.forcing),
        arena.copy_reference(after.forcing),
        after.linear.no_growths,
        after.linear.growths,
    )
    found = memo.get(key)
    if found is not None:
        arena.resolve(found)
        arena.ledger.bump(_fields_keys.SYMBOLIC_INNOVATION_F5_COMPOSITION_HITS)
        return F5AffineTransport(combined, arena.copy_reference(found))

    def shift(value: InnovationID, distance: int) -> InnovationID:
        arena.ledger.bump(_fields_keys.SYMBOLIC_INNOVATION_F5_SHIFT_REQUESTS)
        return arena.chart(value, CylinderChart(1, -distance))

    def scale(value: InnovationID, scalar: int) -> InnovationID:
        return arena.linear_combination(((scalar, value),))

    try:
        result = before.then(after, shift=shift, add=arena.add, scale=scale)
        memo[key] = arena.copy_reference(result.forcing)
    except BaseException:
        # Successfully interned subexpressions remain accounted reusable
        # arithmetic; no complete action or source image is published.
        arena.ledger.bump(_fields_keys.SYMBOLIC_INNOVATION_F5_COMPOSITION_FAILURES)
        raise
    arena.ledger.bump(_fields_keys.SYMBOLIC_INNOVATION_F5_COMPOSITIONS)
    return result
