"""Audit complete dyadic image germs at actual powered cylinder horizons.

This is a bounded experiment, not a constructor or a merge rule.  It asks the
production balanced source-cylinder builder for each complete effect, then
checks smaller boundary proposals against outputs, safety, branch support and
the next chronological block.  Source occurrences remain separate throughout.
"""

from __future__ import annotations

import json
from collections import defaultdict
from collections.abc import Iterable
from dataclasses import dataclass
from operator import add, mul
from random import Random

from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
)
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnLaw,
    DyadicReturnSupportID,
    DyadicReturnSupportRecord,
)
from number_compiler.hashlife.execution.dyadic_return_transport import (
    balanced_residue_effect,
    balanced_residue_macro,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.arithmetic_images import (
    ANTIHYDRA_ARITHMETIC_LAW,
)
from number_compiler.sequences.collatz.physical_images import COLLATZ_PHYSICAL_LAW


@dataclass(frozen=True, slots=True)
class PoweredGerm:
    """Exact retained effect plus separate source/target occurrences.

    Scalar output/safety demands use ``scalar_effect``. A chronology demand
    additionally requires ``branch_word`` or equivalent retained support.
    """

    source: int
    target: int
    width: int
    transfer: tuple[int, int, int]
    odd_steps: int
    delta: int
    minimum: int
    branch_word: int

    @property
    def complete_effect(self) -> tuple[object, ...]:
        return (*self.scalar_effect, self.branch_word)

    @property
    def scalar_effect(self) -> tuple[object, ...]:
        return (
            self.width,
            self.transfer,
            self.odd_steps,
            self.delta,
            self.minimum,
        )

    def edge_germ(self, radius: int) -> tuple[int, int, int, int, int]:
        """A test candidate, never an ActionID or source admission key."""
        if radius < 0:
            raise ValueError("boundary radius must be nonnegative")
        mask = (1 << min(radius, self.width)) - 1
        return (
            self.odd_steps,
            self.delta,
            self.minimum,
            self.branch_word & mask,
            (self.branch_word >> max(0, self.width - radius)) & mask,
        )


def _branch_word(
    workspace: DyadicReturnImageWorkspace, support: DyadicReturnSupportID
) -> int:
    """Demand actual retained leaf support once for this research audit."""
    pending = [support]
    offset = word = 0
    while pending:
        node = workspace.support_node(pending.pop())
        if node.children is not None:
            left, right = node.children
            pending.extend((right, left))
            continue
        if node.branch_word is None:
            raise ValueError("powered boundary audit requires complete branch support")
        word |= node.branch_word << offset
        offset += node.width
    if offset != workspace.support_node(support).width:
        raise AssertionError("retained support lost its chronological extent")
    return word


def _effect_germ(
    workspace: DyadicReturnImageWorkspace, source: int, width: int
) -> PoweredGerm:
    support = balanced_residue_macro(workspace, width, source % (1 << width))
    node: DyadicReturnSupportRecord = workspace.support_node(support)
    transfer = node.transfer
    numerator = transfer.upper * source + transfer.offset
    target, remainder = divmod(numerator, transfer.lower)
    if remainder:
        raise AssertionError("powered skew transport was not integral")
    return PoweredGerm(
        source,
        target,
        width,
        (transfer.upper, transfer.offset, transfer.lower),
        node.odd_steps,
        node.delta,
        node.minimum,
        _branch_word(workspace, support),
    )


def _advance(law: DyadicReturnLaw, source: int) -> int:
    bit = source & 1
    return (law.gains[bit] * source + law.offsets[bit]) // 2


def source_occurrences(
    law: DyadicReturnLaw, *, random_count: int = 48, orbit_steps: int = 160
) -> tuple[int, ...]:
    """Include non-root orbit states, low cylinders and high-fiber sources."""
    if random_count < 0 or orbit_steps < 0:
        raise ValueError("corpus sizes must be nonnegative")
    sources = set(range(128))
    seed = 931386509544713451 if law.family.startswith("collatz") else 8
    current = seed
    for _ in range(orbit_steps):
        sources.add(current)
        current = _advance(law, current)
    rng = Random(0xD1AD1C)
    for _ in range(random_count):
        residue = rng.getrandbits(24)
        sources.add(residue)
        sources.add(residue + (1 << 97))
    return tuple(sorted(sources))


def _conflicts(
    rows: Iterable[tuple[tuple[object, ...], int, tuple[object, ...]]],
) -> tuple[int, dict[str, object] | None]:
    groups: dict[tuple[object, ...], dict[tuple[object, ...], int]] = defaultdict(dict)
    for key, source, effect in rows:
        groups[key].setdefault(effect, source)
    conflicts = [(key, values) for key, values in groups.items() if len(values) > 1]
    if not conflicts:
        return 0, None
    key, values = min(conflicts, key=lambda pair: repr(pair[0]))
    (left_effect, left_source), (right_effect, right_source) = list(values.items())[:2]
    return len(conflicts), {
        "key": key,
        "left_source": left_source,
        "left_effect": left_effect,
        "right_source": right_source,
        "right_effect": right_effect,
    }


def audit_horizon(
    law: DyadicReturnLaw,
    width: int,
    sources: Iterable[int],
    *,
    radius: int = 3,
) -> dict[str, object]:
    """Measure one power and its next block through production support nodes.

    A complete-effect collision is valid sharing only if its full branch word
    and affine/safety data agree.  Continuation is measured against the exact
    returned occurrence; it is never inferred solely from a scalar summary.
    """
    if width <= 0 or width & (width - 1):
        raise ValueError("powered horizon must be a positive power of two")
    if radius < 0:
        raise ValueError("boundary radius must be nonnegative")
    workspace = DyadicReturnImageWorkspace(ResourceLedger(), 0, 0, law)
    try:
        germs: list[PoweredGerm] = []
        doubled: list[PoweredGerm] = []
        right: list[PoweredGerm] = []
        for source in sources:
            if type(source) is not int or source < 0:
                raise ValueError("source occurrences must be nonnegative integers")
            left_germ = _effect_germ(workspace, source, width)
            right_germ = _effect_germ(workspace, left_germ.target, width)
            double_germ = _effect_germ(workspace, source, 2 * width)
            if right_germ.target != double_germ.target:
                raise AssertionError("powered temporal square changed its target")
            left_transfer = SkewTransfer(*left_germ.transfer)
            right_transfer = SkewTransfer(*right_germ.transfer)
            composed = left_transfer.then(right_transfer, multiply=mul, add=add)
            if (composed.upper, composed.offset, composed.lower) != (
                double_germ.transfer
            ):
                raise AssertionError("powered temporal square changed its skew")
            if double_germ.odd_steps != left_germ.odd_steps + right_germ.odd_steps:
                raise AssertionError("powered temporal square changed odd-event count")
            if (
                left_germ.branch_word | (right_germ.branch_word << width)
                != double_germ.branch_word
            ):
                raise AssertionError("powered temporal square changed branch support")
            if double_germ.delta != left_germ.delta + right_germ.delta or (
                double_germ.minimum
                != min(left_germ.minimum, left_germ.delta + right_germ.minimum)
            ):
                raise AssertionError("powered temporal square changed safety")
            germs.append(left_germ)
            right.append(right_germ)
            doubled.append(double_germ)
        complete: dict[tuple[object, ...], set[int]] = defaultdict(set)
        for germ in germs:
            complete[germ.complete_effect].add(germ.source)
        scalar_word_conflicts, scalar_word_witness = _conflicts(
            (germ.scalar_effect, germ.source, (germ.branch_word,)) for germ in germs
        )
        edge_conflicts, edge_witness = _conflicts(
            (germ.edge_germ(radius), germ.source, germ.scalar_effect) for germ in germs
        )
        doubled_differences, doubled_witness = _conflicts(
            (germ.edge_germ(radius), germ.source, future.complete_effect)
            for germ, future in zip(germs, doubled, strict=True)
        )
        fiber_checks = 0
        for germ in germs[:8]:
            lifted = _effect_germ(workspace, germ.source + (1 << (width + 11)), width)
            if lifted.complete_effect != germ.complete_effect:
                raise AssertionError("a high-fiber lift changed the complete effect")
            transfer = germ.transfer
            expected = (transfer[0] * lifted.source + transfer[1]) // transfer[2]
            if lifted.target != expected:
                raise AssertionError("a high-fiber lift changed the output function")
            fiber_checks += 1
        # Source/target occurrence is intentionally not a semantic action key.
        return {
            "family": law.family,
            "horizon": width,
            "source_occurrences": len(germs),
            "complete_effect_classes": len(complete),
            # Distinct exact sources in each class; duplicate input rows do not
            # increase this count. An alias is not a source-identity merge.
            "complete_effect_alias_classes": sum(len(s) > 1 for s in complete.values()),
            "largest_complete_effect_fiber": max(
                map(len, complete.values()), default=0
            ),
            "edge_radius": radius,
            "scalar_to_branch_conflicts": scalar_word_conflicts,
            "scalar_to_branch_witness": scalar_word_witness,
            "edge_to_scalar_conflicts": edge_conflicts,
            "edge_to_doubled_effect_differences_across_occurrences": doubled_differences,
            "edge_witness": edge_witness,
            "doubled_witness": doubled_witness,
            "high_fiber_checks": fiber_checks,
            "retained_support_records": len(workspace.support),
            "right_occurrences": len(right),
            "constructor_memo_hits": workspace.ledger.counters.get(
                workspace.counter_prefix + "_balanced_effect_memo_hits", 0
            ),
        }
    finally:
        workspace.dispose()


def memo_opportunity_audit(
    sources: Iterable[int], *, steps: int = 1024, leaf_width: int = 64
) -> dict[str, int]:
    """Compare repeated leaf keys with hypothetical reduced domains.

    Every leaf effect comes from the production balanced constructor. The
    candidate domain ``p=min(n,n-odd+1)`` is used only for this measurement.
    Each source has a fresh sample table; this does not trace parent-node
    publications, the production FIFO lifecycle or admission of a new cache.
    The production memo is unchanged. An unindexed scan is counted explicitly
    so apparent aliases cannot hide a slower cold path.
    """
    if steps <= 0 or leaf_width <= 0 or leaf_width > 64:
        raise ValueError("positive steps and bounded leaf width required")
    workspace = DyadicReturnImageWorkspace(ResourceLedger(), 0, 0, COLLATZ_PHYSICAL_LAW)
    counts = {
        "sources": 0,
        "leaf_requests": 0,
        "exact_leaf_key_repeats": 0,
        "hypothetical_verified_nonexact_leaf_aliases": 0,
        "hypothetical_unindexed_comparisons": 0,
    }
    try:
        for source in sources:
            if type(source) is not int or source < 0:
                raise ValueError("source occurrences must be nonnegative integers")
            counts["sources"] += 1
            value = source
            seen: list[tuple[int, int, int, tuple[object, ...]]] = []
            exact_keys: set[tuple[int, int]] = set()
            for start in range(0, steps, leaf_width):
                span = min(steps - start, leaf_width)
                residue = value % (1 << span)
                node = balanced_residue_effect(workspace, span, residue)
                transfer = node.transfer
                signature: tuple[object, ...] = (
                    transfer.upper,
                    transfer.offset,
                    transfer.lower,
                    node.odd_steps,
                    node.delta,
                    node.minimum,
                    node.branch_word,
                )
                counts["leaf_requests"] += 1
                key = (span, residue)
                if key in exact_keys:
                    counts["exact_leaf_key_repeats"] += 1
                else:
                    for old_span, old_residue, old_p, old_signature in seen:
                        counts["hypothetical_unindexed_comparisons"] += 1
                        if old_span != span:
                            continue
                        if residue % (1 << old_p) == old_residue % (1 << old_p):
                            if signature != old_signature:
                                raise AssertionError(
                                    "reduced source domain changed a scalar leaf"
                                )
                            current_support = balanced_residue_macro(
                                workspace, span, residue
                            )
                            old_support = balanced_residue_macro(
                                workspace, span, old_residue
                            )
                            if _branch_word(workspace, current_support) != _branch_word(
                                workspace, old_support
                            ):
                                raise AssertionError(
                                    "reduced source domain changed retained support"
                                )
                            counts["hypothetical_verified_nonexact_leaf_aliases"] += 1
                            break
                    p = min(span, span - node.odd_steps + 1)
                    seen.append((span, residue, p, signature))
                    exact_keys.add(key)
                for _ in range(span):
                    value = _advance(COLLATZ_PHYSICAL_LAW, value)
        return counts
    finally:
        workspace.dispose()


def main() -> None:
    for law in (COLLATZ_PHYSICAL_LAW, ANTIHYDRA_ARITHMETIC_LAW):
        sources = source_occurrences(law)
        for horizon in (2, 4, 8, 16, 32, 64):
            print(json.dumps(audit_horizon(law, horizon, sources), sort_keys=True))
    rng = Random(0xC011A72)
    print(
        json.dumps(
            memo_opportunity_audit(rng.getrandbits(256) | 1 for _ in range(128)),
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
