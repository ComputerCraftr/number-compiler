"""Bounded, source-derived joint future quotient audit.

Each row is one exact reachable source cylinder and one witness of it.  Equality
of observer keys is tested against coarsened finite continuation outputs; it
does not identify source occurrences or prove an infinite safety invariant.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import prod

from devtools.experiments.antihydra.event_domain import (
    EventExponentDomain,
    source_event_exponent_domain,
)
from devtools.experiments.antihydra.future_grammar import ReachableFutureGrammar
from number_compiler.arithmetic.fields.consumer_pullback import (
    HalfOpenInterval as Interval,
)
from number_compiler.arithmetic.fields.branch_quotients import (
    BranchChoiceSuffix,
    PrimeBucketWorkspace,
)
from devtools.experiments.antihydra.source_safety import (
    PRIME_BANK,
    SourceBlockID,
    SourceSafetyWorkspace,
    event_prime_lanes,
    source_event,
)
from number_compiler.arithmetic.fields.consumer_pullback import ExactRational as Q
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class JointRow:
    """One source-authenticated finite observation, with its witness retained."""

    depth: int
    residue: int
    width: int
    source: int
    high_fiber_probe: int
    fraction: Q
    fraction_probe: str
    middle: int
    event_endpoint: int
    mahler_exponent: int
    collatz_exponent: int | None
    legal_menu: tuple[int, ...]
    full_domain: EventExponentDomain
    suffix: BranchChoiceSuffix
    pre_key: tuple[object, ...]
    after_only_key: tuple[object, ...]
    key: tuple[object, ...]
    output: tuple[object, ...]
    diagnostics: tuple[int | None, int | None, int | None, int]


def _collatz_gap(odd_source: int) -> int:
    if odd_source <= 0 or odd_source % 2 != 1:
        raise ValueError("Collatz accelerated gap requires a positive odd source")
    value = 3 * odd_source + 1
    return (value & -value).bit_length() - 1


def _legal_menu(
    workspace: SourceSafetyWorkspace, parent: SourceBlockID, max_event: int
) -> tuple[EventExponentDomain, tuple[int, ...]]:
    domain = source_event_exponent_domain(workspace, parent)
    # The suffix digit is an index in the complete possible-q domain.  We
    # explore only absolute q<=max_event, even when the first legal q is larger.
    # An unbounded domain remains unbounded in the returned domain.
    if domain.first is None:
        return domain, ()
    return domain, tuple(
        q
        for q in range(domain.first, min(max_event, domain.first + 2) + 1)
        if domain.contains(q)
    )


def _dyadic_inside(interval: Interval) -> Q:
    if interval.empty:
        raise ValueError("empty fractional interval has no witness")
    bits = (interval.lower.denominator * interval.upper.denominator).bit_length() + 2
    denominator = 1 << bits
    numerator = (
        interval.lower.numerator * denominator + interval.lower.denominator - 1
    ) // interval.lower.denominator
    witness = Q(numerator, denominator)
    if not interval.contains(witness):
        raise ArithmeticError("dyadic grid failed to enter exact guard intersection")
    return witness


def _fraction_witnesses(
    grammar: ReachableFutureGrammar,
    child: SourceBlockID,
    source: int,
    canonical: Q,
) -> tuple[tuple[str, Q], ...]:
    """Sample both sides of the exact source-selected next-event guard."""
    block = grammar.workspace.view(child)
    endpoint = block.endpoint + 3**block.width * (source >> block.width)
    if endpoint <= 0:
        return (("canonical", canonical),)
    q = (endpoint & -endpoint).bit_length()
    scale = Q(3**q, 1 << q)
    next_guard = Interval(Q(1, 2) / scale, Q(3, 4) / scale).pullback(block.fractional)
    intersection = block.guard.intersect(next_guard)
    samples = [("canonical", canonical)]
    if not intersection.empty:
        samples.append(("next_safe", _dyadic_inside(intersection)))
    for outside in (
        Interval(block.guard.lower, min(block.guard.upper, next_guard.lower)),
        Interval(max(block.guard.lower, next_guard.upper), block.guard.upper),
    ):
        if not outside.empty:
            samples.append(("next_fail", _dyadic_inside(outside)))
            break
    distinct: dict[Q, str] = {}
    for label, fraction in samples:
        distinct.setdefault(fraction, label)
    grammar.workspace.ledger.bump(
        "joint_fraction_safe_intersections", int(not intersection.empty)
    )
    grammar.workspace.ledger.bump(
        "joint_fraction_no_safe_intersection", int(intersection.empty)
    )
    return tuple((label, fraction) for fraction, label in distinct.items())


def _row(
    grammar: ReachableFutureGrammar,
    parent: SourceBlockID,
    child: SourceBlockID,
    exponent: int,
    menu: tuple[int, ...],
    domain: EventExponentDomain,
    previous_suffix: BranchChoiceSuffix,
    suffix: BranchChoiceSuffix,
    depth: int,
    mahler_partitions: dict[int, tuple[int, ...]],
    collatz_partitions: dict[int, tuple[int, ...]],
    *,
    source_override: int | None = None,
    high_fiber_probe: int = 0,
    fraction_override: Q | None = None,
    fraction_probe: str = "canonical",
) -> JointRow:
    workspace = grammar.workspace
    parent_block, block = workspace.view(parent), workspace.view(child)
    if exponent not in menu or domain.first is None or len(menu) > 3:
        raise ValueError("suffix requires a source-admitted menu of at most three")
    base_source, fraction = grammar.witness(child)
    source = base_source if source_override is None else source_override
    if fraction_override is not None:
        fraction = fraction_override
    if not grammar.admits(child, source, fraction):
        raise ArithmeticError("joint witness escaped its authenticated cylinder")
    middle = parent_block.endpoint + 3**parent_block.width * (
        source >> parent_block.width
    )
    middle_fraction = parent_block.fractional.apply(fraction)
    if middle_fraction is None:
        raise ArithmeticError("source fractional transport unexpectedly saturated")
    event = source_event(workspace, middle, middle_fraction)
    if event.exponent != exponent or event.endpoint != (
        block.endpoint + 3**block.width * (source >> block.width)
    ):
        raise ArithmeticError("joint event differs from its complete source edge")
    lanes = event_prime_lanes(event)
    # The deck is the explicit 64-sheet projection of the original source;
    # the three-adic chart and high fiber retain distinct coordinates.
    deck = source % 64
    mahler = tuple(
        (p, mahler_partitions[p][before], mahler_partitions[p][after])
        for p, before, after in lanes
        if p in mahler_partitions
    )
    collatz_q: int | None = None
    collatz: tuple[tuple[int, int, int], ...] | None = None
    if middle % 2:
        collatz_q = _collatz_gap(middle)
        next_odd = (3 * middle + 1) >> collatz_q
        collatz = tuple(
            (
                p,
                collatz_partitions[p][(-3 * middle - 1) % p],
                collatz_partitions[p][(-3 * next_odd - 1) % p],
            )
            for p in collatz_partitions
        )
    # Finite chart precision is explicit.  A matching residue is an observer
    # collision, never a complete source identity or a pumping certificate.
    key: tuple[object, ...] = (
        deck,
        (source // 64) % 729,
        block.endpoint % 729,
        mahler,
        collatz,
        suffix,
    )
    pre_key: tuple[object, ...] = (
        deck,
        (source // 64) % 729,
        parent_block.endpoint % 729,
        tuple((p, before) for p, before, _ in mahler),
        None if collatz is None else tuple((p, before) for p, before, _ in collatz),
        previous_suffix,
    )
    after_only_key: tuple[object, ...] = (
        deck,
        (source // 64) % 729,
        block.endpoint % 729,
        tuple((p, after) for p, _, after in mahler),
        None if collatz is None else tuple((p, after) for p, _, after in collatz),
        suffix,
    )
    next_domain, _ = _legal_menu(workspace, child, grammar.max_event)
    next_source_q: int | None = None
    if event.endpoint > 0:
        candidate_q = (event.endpoint & -event.endpoint).bit_length()
        scaled_w = Q(3**candidate_q, 1 << candidate_q) * Q(4) * event.next_fraction
        if Q(2) <= scaled_w < Q(3):
            next_source_q = candidate_q
    # The exact witness may leave the safe fractional domain.  The full
    # cylinder's possible menu is not its witness-selected next event.
    available_ranks = 0
    if next_domain.first is not None:
        for rank in range(3):
            if next_domain.contains(next_domain.first + rank):
                available_ranks |= 1 << rank
    selected_rank = 0
    if next_source_q is not None:
        if next_domain.first is None or not next_domain.contains(next_source_q):
            raise ArithmeticError("candidate next source q escaped possible domain")
        rank = next_source_q - next_domain.first + 1
        selected_rank = rank if rank <= 3 else 4
    output: tuple[object, ...] = (
        int(block.ledger_minimum < 0),
        int(next_source_q is not None),
        available_ranks,
        selected_rank,
    )
    workspace.ledger.bump("joint_source_rows")
    return JointRow(
        depth,
        block.residue,
        block.width,
        source,
        high_fiber_probe,
        fraction,
        fraction_probe,
        middle,
        event.endpoint,
        exponent,
        collatz_q,
        menu,
        domain,
        suffix,
        pre_key,
        after_only_key,
        key,
        output,
        (next_domain.first, next_domain.last, next_source_q, event.endpoint % 256),
    )


def audit_joint_future(
    *,
    depth: int = 6,
    max_event: int = 3,
    primes: tuple[int, ...] = PRIME_BANK,
    max_nodes: int = 100_000,
    high_fiber_probes: bool = False,
    fractional_probes: bool = False,
) -> dict[str, object]:
    """Audit exact finite source families with charged construction and cleanup.

    The suffix stores only the first three ranks in each complete possible-q
    domain.  Every excluded larger rank is reported as an open continuation.
    """
    if (
        type(depth) is not int
        or not 1 <= depth <= 64
        or type(max_event) is not int
        or not 1 <= max_event <= 3
    ):
        raise ValueError("depth 1..64 and event bound 1..3 required")
    if type(max_nodes) is not int or max_nodes < 1:
        raise ValueError("positive node budget required")
    if type(high_fiber_probes) is not bool:
        raise TypeError("high-fiber probe option must be Boolean")
    if type(fractional_probes) is not bool:
        raise TypeError("fractional probe option must be Boolean")
    if (
        type(primes) is not tuple
        or len(set(primes)) != len(primes)
        or any(type(p) is not int or p not in PRIME_BANK for p in primes)
    ):
        raise ValueError("primes must be a distinct tuple from the fixed observer bank")
    ledger = ResourceLedger(max_nodes=max_nodes, max_cache_entries=4 * max_nodes)
    workspace = SourceSafetyWorkspace(ledger, max_width=depth * max_event)
    grammar = ReachableFutureGrammar(workspace, max_event=max_event)
    partitions = PrimeBucketWorkspace(ledger)
    row_owner = ledger.register(
        f"joint-rows-{ledger.owner_count}", "bounded audit rows"
    )
    charged_entries = charged_nodes = 0
    frontier: tuple[tuple[SourceBlockID, BranchChoiceSuffix], ...] = ()
    rows: list[JointRow] = []
    records: list[dict[str, int]] = []
    mahler_parts: dict[int, tuple[int, ...]] = {}
    collatz_parts: dict[int, tuple[int, ...]] = {}
    truncated_domains = 0
    unbounded_domains = 0
    unexplored_rank_slots = 0
    report: dict[str, object]
    probe_offsets: tuple[int, ...] = (0,)
    try:
        setup_nodes = 4 * len(primes) + (
            16 + sum(p.bit_length() for p in primes) if high_fiber_probes else 0
        )
        ledger.reserve(row_owner, nodes=setup_nodes)
        charged_nodes += setup_nodes
        frontier = ((grammar.root, BranchChoiceSuffix()),)
        if high_fiber_probes:
            probe_offsets = tuple(dict.fromkeys((0, 1, 729, 729 * prod(primes))))
        mahler_parts = {p: partitions.partition("mahler", p) for p in primes}
        collatz_parts = {p: partitions.partition("collatz", p) for p in primes}
        for level in range(1, depth + 1):
            if not frontier:
                break
            following: list[tuple[SourceBlockID, BranchChoiceSuffix]] = []
            for parent, suffix in frontier:
                domain, menu = _legal_menu(workspace, parent, max_event)
                if domain.unbounded or (
                    domain.last is not None and domain.last > max_event
                ):
                    truncated_domains += 1
                if domain.unbounded:
                    unbounded_domains += 1
                if domain.first is not None:
                    unexplored_rank_slots += sum(
                        domain.contains(domain.first + rank)
                        and domain.first + rank > max_event
                        for rank in range(3)
                    )
                for exponent in menu:
                    assert domain.first is not None
                    edge = grammar.edge(parent, exponent)
                    next_suffix = suffix.append(exponent - domain.first + 1)
                    child_block = workspace.view(edge.child)
                    offsets = probe_offsets if child_block.width >= 6 else (0,)
                    base_source, base_fraction = grammar.witness(edge.child)
                    for probe in offsets:
                        source_nodes = (
                            base_source.bit_length()
                            + probe.bit_length()
                            + child_block.width
                            + 15
                        ) // 8
                        ledger.reserve(row_owner, nodes=source_nodes)
                        charged_nodes += source_nodes
                        source = base_source + (probe << child_block.width)
                        samples: tuple[tuple[str, Q], ...] = (
                            ("canonical", base_fraction),
                        )
                        if fractional_probes:
                            fraction_nodes = 64 + 8 * (
                                child_block.width + source.bit_length()
                            )
                            ledger.reserve(row_owner, nodes=fraction_nodes)
                            charged_nodes += fraction_nodes
                            samples = _fraction_witnesses(
                                grammar, edge.child, source, base_fraction
                            )
                        for fraction_label, fraction in samples:
                            # Charge row, key and grouped references before
                            # constructing each alternate exact witness.
                            nodes = (
                                96
                                + 24 * len(primes)
                                + 16 * level
                                + (probe.bit_length() + child_block.width + 7) // 8
                                + 8 * fraction.denominator.bit_length()
                            )
                            ledger.reserve(row_owner, entries=1, nodes=nodes)
                            charged_entries += 1
                            charged_nodes += nodes
                            ledger.bump(
                                "joint_high_fiber_integer_bits", source.bit_length()
                            )
                            row = _row(
                                grammar,
                                parent,
                                edge.child,
                                exponent,
                                menu,
                                domain,
                                suffix,
                                next_suffix,
                                level,
                                mahler_parts,
                                collatz_parts,
                                source_override=source,
                                high_fiber_probe=probe,
                                fraction_override=fraction,
                                fraction_probe=fraction_label,
                            )
                            rows.append(row)
                    following.append((edge.child, next_suffix))
            ledger.reserve(row_owner, entries=1, nodes=16)
            charged_entries += 1
            charged_nodes += 16
            frontier = tuple(following)
            records.append(
                {"depth": level, "families": len(frontier), "rows": len(rows)}
            )

        def summarize(
            view: str,
        ) -> tuple[
            int, int, int, dict[str, object] | None, int, dict[str, object] | None
        ]:
            grouped: dict[tuple[object, ...], list[JointRow]] = {}
            for row in rows:
                key = row.key
                if view == "deck":
                    key = (key[0],)
                elif view == "pre_edge":
                    key = row.pre_key
                elif view == "after_only":
                    key = row.after_only_key
                elif view == "fraction_exact_diagnostic":
                    # A source authority diagnostic, not a finite quotient.
                    key = (*key, row.fraction)
                elif view == "deck_suffix":
                    key = (key[0], key[-1])
                elif view == "chart_suffix":
                    key = (key[0], key[2], key[-1])
                elif view == "mahler_suffix":
                    key = (key[0], key[3], key[-1])
                elif view != "full":
                    raise ValueError("unknown finite quotient view")
                grouped.setdefault(key, []).append(row)
            repeats = conflicts = diagnostic_conflicts = 0
            first_conflict: dict[str, object] | None = None
            first_diagnostic_conflict: dict[str, object] | None = None
            for group in grouped.values():
                if len(group) < 2:
                    continue
                repeats += 1
                first = group[0]
                for other in group[1:]:
                    if other.diagnostics != first.diagnostics:
                        diagnostic_conflicts += 1
                        if first_diagnostic_conflict is None:
                            first_diagnostic_conflict = {
                                "first": _witness(first),
                                "second": _witness(other),
                                "first_diagnostics": first.diagnostics,
                                "second_diagnostics": other.diagnostics,
                            }
                    if other.output != first.output:
                        conflicts += 1
                        if first_conflict is None:
                            first_conflict = {
                                "first": _witness(first),
                                "second": _witness(other),
                                "first_output": first.output,
                                "second_output": other.output,
                            }
                        break
            ledger.bump("joint_refinement_rows_scanned", len(rows))
            return (
                len(grouped),
                repeats,
                conflicts,
                first_conflict,
                diagnostic_conflicts,
                first_diagnostic_conflict,
            )

        refinements: dict[str, dict[str, object]] = {}
        for view in (
            "deck",
            "deck_suffix",
            "pre_edge",
            "after_only",
            "fraction_exact_diagnostic",
            "chart_suffix",
            "mahler_suffix",
            "full",
        ):
            (
                classes,
                repeats,
                conflicts,
                witness,
                diagnostic_count,
                diagnostic_witness,
            ) = summarize(view)
            refinements[view] = {
                "classes": classes,
                "repeated_keys": repeats,
                "conflicts": conflicts,
                "first_conflict": witness,
                "diagnostic_conflicts": diagnostic_count,
                "first_diagnostic_conflict": diagnostic_witness,
            }
        by_depth: dict[int, dict[str, int]] = {}
        for level in range(1, depth + 1):
            level_rows = [row for row in rows if row.depth == level]
            level_groups: dict[tuple[object, ...], list[JointRow]] = {}
            for row in level_rows:
                level_groups.setdefault(row.key, []).append(row)
            by_depth[level] = {
                "rows": len(level_rows),
                "repeated_keys": sum(len(g) > 1 for g in level_groups.values()),
                "conflicts": sum(
                    len({row.output for row in g}) > 1 for g in level_groups.values()
                ),
            }
        full = refinements["full"]
        output_counts: dict[tuple[object, ...], int] = {}
        for row in rows:
            output_counts[row.output] = output_counts.get(row.output, 0) + 1
        report = {
            "status": "FINITE_CONFLICT"
            if full["conflicts"]
            else "FINITE_OBSERVATION_ONLY",
            "rows": len(rows),
            "distinct_keys": full["classes"],
            "repeated_keys": full["repeated_keys"],
            "conflicts": [full["first_conflict"]] if full["first_conflict"] else [],
            "refinements": refinements,
            "records": list(records),
            "by_depth": by_depth,
            "distinct_coarse_outputs": len(output_counts),
            "coarse_output_histogram": [
                {"output": output, "count": count}
                for output, count in output_counts.items()
            ],
        }
    except BlockContextBudgetExceeded:
        ledger.bump("joint_budget_refusals")
        partial_counts: dict[tuple[object, ...], int] = {}
        for row in rows:
            partial_counts[row.output] = partial_counts.get(row.output, 0) + 1
        report = {
            "status": "BUDGET_EXHAUSTED",
            "rows": len(rows),
            "records": list(records),
            "distinct_keys": None,
            "repeated_keys": None,
            "conflicts": [],
            "refinements": None,
            "by_depth": None,
            "distinct_coarse_outputs": len(partial_counts),
            "coarse_output_histogram": [
                {"output": output, "count": count}
                for output, count in partial_counts.items()
            ],
        }
    finally:
        mahler_parts.clear()
        collatz_parts.clear()
        partitions.close()
        grammar.close()
        workspace.close()
        ledger.release(row_owner, entries=charged_entries, nodes=charged_nodes)
        ledger.mark_disposed(row_owner)
        rows.clear()
        records.clear()
    report.update(
        {
            "prime_bank": primes,
            "output_schema": (
                "finite_ledger_failure",
                "conditional_next_fractional_event",
                "first_three_possible_rank_mask",
                "selected_rank_or_overflow",
            ),
            "event_bound": max_event,
            "larger_events": "UNEXPLORED",
            "truncated_legal_domains": truncated_domains,
            "unbounded_domains": unbounded_domains,
            "unexplored_first_three_rank_slots": unexplored_rank_slots,
            "source_occurrences_merged": False,
            "high_fiber_probes": high_fiber_probes,
            "fractional_probes": fractional_probes,
            "witness_scope": (
                "admitted initial fractional states in finite source cylinders; "
                "not the fixed blank-tape or source-7 trajectory"
            ),
            "fixed_key_conflict_scope": (
                "a finite observer key omits fractional safety binding; "
                "this is not a counterexample to the complete parameterized "
                "source cylinder or skew action"
            ),
            "all_time_safety_certified": False,
            "work": dict(ledger.counters),
            "peak_nodes": ledger.peak_nodes,
            "peak_entries": ledger.peak_entries,
            "retained_nodes": ledger.nodes,
            "retained_entries": ledger.entries,
        }
    )
    return report


def _witness(row: JointRow) -> dict[str, object]:
    return {
        "source": row.source,
        "high_fiber_probe": row.high_fiber_probe,
        "fraction": (row.fraction.numerator, row.fraction.denominator),
        "fraction_probe": row.fraction_probe,
        "middle": row.middle,
        "event_endpoint": row.event_endpoint,
        "next_source_low8": row.diagnostics[3],
        "width": row.width,
        "residue": row.residue,
        "mahler_q": row.mahler_exponent,
        "collatz_q": row.collatz_exponent,
        "explored_menu": row.legal_menu,
        "full_domain": (row.full_domain.first, row.full_domain.last),
        "suffix": row.suffix.choices(),
    }


def audit_collatz_sources(
    *,
    max_odd_source: int = 255,
    primes: tuple[int, ...] = PRIME_BANK,
    max_nodes: int = 100_000,
) -> dict[str, object]:
    """Separate bounded accelerated Collatz audit on exact odd sources.

    Its q is v2(3x+1), not the Mahler zero-run q.  Every retained table and
    sample has a ledger reservation; a budget refusal returns partial evidence.
    """
    if type(max_odd_source) is not int or not 1 <= max_odd_source <= 65535:
        raise ValueError("odd-source horizon must be 1..65535")
    if type(max_nodes) is not int or max_nodes < 1:
        raise ValueError("positive node budget required")
    if (
        type(primes) is not tuple
        or len(set(primes)) != len(primes)
        or any(type(p) is not int or p not in PRIME_BANK for p in primes)
    ):
        raise ValueError("primes must be a distinct tuple from the fixed observer bank")
    ledger = ResourceLedger(max_nodes=max_nodes, max_cache_entries=4 * max_nodes)
    partitions_workspace = PrimeBucketWorkspace(ledger)
    row_owner = ledger.register(
        f"joint-collatz-{ledger.owner_count}", "odd source rows"
    )
    charged_entries = charged_nodes = 0
    groups: dict[tuple[object, ...], tuple[tuple[int, int, int], int, bool]] = {}
    bucket_groups: dict[tuple[object, ...], tuple[tuple[int, int, int], int, bool]] = {}
    partitions: dict[int, tuple[int, ...]] = {}
    conflicts: list[dict[str, object]] = []
    conflict_count = repeated_count = rows = 0
    bucket_repeats = bucket_conflicts = 0
    first_bucket_conflict: dict[str, object] | None = None
    report: dict[str, object]
    try:
        ledger.reserve(row_owner, nodes=2 * len(primes))
        charged_nodes += 2 * len(primes)
        partitions = {p: partitions_workspace.partition("collatz", p) for p in primes}
        for source in range(1, max_odd_source + 1, 2):
            # The two dictionaries retain at most two short key tuples,
            # one lane tuple, and two first-witness records per source.  Each
            # lane receives twelve charged nodes, with a separate bit-size
            # allowance for the exact source and endpoint integers.
            nodes = 96 + 12 * len(primes) + 8 * source.bit_length()
            ledger.reserve(row_owner, entries=1, nodes=nodes)
            charged_entries += 1
            charged_nodes += nodes
            q = _collatz_gap(source)
            next_source = (3 * source + 1) >> q
            if next_source % 2 != 1:
                raise ArithmeticError("accelerated Collatz output is not odd")
            lane = tuple(
                (p, labels[(-3 * source - 1) % p], labels[(-3 * next_source - 1) % p])
                for p, labels in partitions.items()
            )
            key = (source % 64, source % 729, lane)
            bucket_key = (source % 64, lane)
            row = (source, q, next_source)
            prior = groups.get(key)
            if prior is None:
                groups[key] = (row, 1, False)
            else:
                first, count, had_conflict = prior
                if count == 1:
                    repeated_count += 1
                mismatch = (first[1], first[2] % 64) != (q, next_source % 64)
                if mismatch and not had_conflict:
                    conflict_count += 1
                    if len(conflicts) < 8:
                        conflicts.append({"first": first, "second": row})
                groups[key] = (first, count + 1, had_conflict or mismatch)
            bucket_prior = bucket_groups.get(bucket_key)
            if bucket_prior is None:
                bucket_groups[bucket_key] = (row, 1, False)
            else:
                first, count, had_conflict = bucket_prior
                if count == 1:
                    bucket_repeats += 1
                # Keep the collision output deliberately coarser than an
                # exact endpoint: q is saturated after three, and only the
                # next source's low three bits are retained.
                mismatch = (min(first[1], 4), first[2] % 8) != (
                    min(q, 4),
                    next_source % 8,
                )
                if mismatch and not had_conflict:
                    bucket_conflicts += 1
                    if first_bucket_conflict is None:
                        first_bucket_conflict = {"first": first, "second": row}
                bucket_groups[bucket_key] = (first, count + 1, had_conflict or mismatch)
            rows += 1
            ledger.bump("joint_collatz_source_rows")
        report = {
            "status": "FINITE_CONFLICT"
            if conflict_count
            else "FINITE_OBSERVATION_ONLY",
            "rows": rows,
            "distinct_keys": len(groups),
            "repeated_keys": repeated_count,
            "conflict_keys": conflict_count,
            "conflicts": conflicts,
            "deck_bucket_refinement": {
                "repeated_keys": bucket_repeats,
                "conflict_keys": bucket_conflicts,
                "first_conflict": first_bucket_conflict,
            },
        }
    except BlockContextBudgetExceeded:
        ledger.bump("joint_budget_refusals")
        report = {
            "status": "BUDGET_EXHAUSTED",
            "rows": rows,
            "distinct_keys": len(groups),
            "repeated_keys": repeated_count,
            "conflict_keys": conflict_count,
            "conflicts": conflicts,
            "deck_bucket_refinement": {
                "repeated_keys": bucket_repeats,
                "conflict_keys": bucket_conflicts,
                "first_conflict": first_bucket_conflict,
            },
        }
    finally:
        partitions.clear()
        partitions_workspace.close()
        ledger.release(row_owner, entries=charged_entries, nodes=charged_nodes)
        ledger.mark_disposed(row_owner)
        groups.clear()
        bucket_groups.clear()
    report.update(
        {
            "prime_bank": primes,
            "source_horizon": max_odd_source,
            "shared_mahler_q_claimed": False,
            "all_time_safety_certified": False,
            "work": dict(ledger.counters),
            "peak_nodes": ledger.peak_nodes,
            "peak_entries": ledger.peak_entries,
            "retained_nodes": ledger.nodes,
            "retained_entries": ledger.entries,
        }
    )
    return report


__all__ = ["JointRow", "audit_joint_future", "audit_collatz_sources"]
