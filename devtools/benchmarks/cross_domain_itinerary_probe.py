"""Cross-domain itinerary/residue/pair-field probe for v0.16."""

from __future__ import annotations

from devtools.verification.consumer_fixtures import carry_seed_rows
from devtools.paths import report_directory

import json
from collections import Counter
from math import comb, log2
from typing import Sequence, TypedDict

from devtools.paths import report_output, repository_root
from devtools.benchmarks.pair_encoding import pair_from_int
from number_compiler.arithmetic.carry.carry_itinerary import (
    LiveCarryItinerary,
    adaptive_cyclic_memory_horizon,
    adaptive_negacyclic_memory_horizon,
    adaptive_zplus1_memory_horizon,
    carry_threshold_itinerary,
    cyclic_growth_operator_rank,
    even_width_palindrome_has_z_plus_one_factor,
    growth_run_itinerary,
    live_event_suffix_length,
    negacyclic_transport_kernel,
    pair_field_preimage_count,
    polynomial_growth_operator_rank,
    reverse_add_base_pm_residues,
    threshold_reset_count,
)
from number_compiler.arithmetic.carry.event_memory import (
    carry_field,
    forcing_event,
    pair_step,
)
from number_compiler.sequences.collatz.pair import (
    accelerated_odd_target_mod3_from_valuation,
    collatz_slab_mod_odd,
    collatz_valuation_itinerary,
    mul3_carry_monoid,
    valuation_itinerary_slab,
)
from number_compiler.sequences.collatz.raw_field import CollatzRawDigitField

ROOT = repository_root()


def _summarize_horizons(values: Sequence[int | None]) -> dict[str, float]:
    assert all(value is not None for value in values)
    resolved = [value for value in values if value is not None]
    return {
        "average": sum(resolved) / len(resolved),
        "maximum": max(resolved),
        "minimum": min(resolved),
    }


def reverse_int(value: int, base: int = 10) -> int:
    ds = []
    n = int(value)
    while n:
        ds.append(n % base)
        n //= base
    ds = ds or [0]
    out = 0
    for d in ds:
        out = out * base + d
    return out


def reverse_trace(
    steps: int = 512,
) -> tuple[
    list[tuple[int, ...]],
    list[tuple[int, ...]],
    list[tuple[int, ...]],
    list[int],
    int,
    int,
    int,
]:
    pair = pair_from_int(196)
    pairs = [pair]
    carries = []
    growths = []
    events = []
    neutral = resets = positions = 0
    for _ in range(steps + 20):
        c = carry_field(pair, base=10)
        carries.append(c[1:])
        symbols = carry_threshold_itinerary(pair, base=10)
        neutral += sum(s == 0 for s in symbols)
        resets += threshold_reset_count(symbols)
        positions += len(pair)
        target, growth = pair_step(pair, 10)
        events.append(forcing_event(pair, target, growth))
        growths.append(growth)
        pair = target
        pairs.append(pair)
    return pairs, carries, events, growths, neutral, resets, positions


def vertical_itinerary_metrics(
    carries: list[tuple[int, ...]], horizon: int = 20, windows: int = 256
) -> dict[str, int]:
    words = set()
    active_words = set()
    cols = 0
    end = min(len(carries), horizon + windows)
    for t in range(horizon, end):
        rows = carries[t - horizon : t]
        width = len(rows[-1])
        for i in range(width):
            word = active = 0
            for j, row in enumerate(rows):
                if i < len(row):
                    active |= 1 << j
                    word |= row[i] << j
            words.add(word)
            active_words.add((active, word))
            cols += 1
    return {
        "windows": end - horizon,
        "columns": cols,
        "unique_carry_words": len(words),
        "unique_active_carry_words": len(active_words),
    }


class MacroSlot(TypedDict):
    count: int
    rows: set[tuple[int, ...]]
    alphabet: set[int]
    support: int
    positions: int


class MacroReport(TypedDict):
    epochs: int
    unique_macro_rows: int
    coefficient_alphabet_size: int
    coefficient_min: int
    coefficient_max: int
    support_fraction: float


def bucket_alphabet_probe(steps: int = 256) -> dict[str, object]:
    # Exact five-bucket regrouping of S = sum_q 2**q B_q (mod 32).  This is
    # deliberately measured and rejected if the bucket symbols retain full 5-bit
    # alphabets; it is not exported as another semantic state.
    pair = pair_from_int(196)
    buckets: tuple[tuple[int, ...], ...] = (pair,) + ((0,) * len(pair),) * 4
    alphabets: list[set[int]] = [set() for _ in range(5)]

    def growth_apply(row: tuple[int, ...]) -> tuple[int, ...]:
        out = [0] * (len(row) + 1)
        for i, x in enumerate(row):
            out[i] = (out[i] + x) & 31
            out[i + 1] = (out[i + 1] + x) & 31
        return tuple(out)

    for _ in range(steps):
        for q, row in enumerate(buckets):
            alphabets[q].update(row)
        target, growth = pair_step(pair, 10)
        event = forcing_event(pair, target, growth)
        if growth:
            next_b = [growth_apply(row) for row in buckets]
            next_b[0] = tuple((x + e) & 31 for x, e in zip(next_b[0], event))
        else:
            next_b = [tuple(e & 31 for e in event), *buckets[:-1]]
        reconstructed = tuple(
            sum((1 << q) * next_b[q][i] for q in range(5)) & 31
            for i in range(len(target))
        )
        assert reconstructed == target
        pair, buckets = target, tuple(next_b)
    return {
        "bucket_count": 5,
        "planes_per_bucket": 5,
        "total_bitplanes": 25,
        "alphabet_sizes": [len(s) for s in alphabets],
        "all_buckets_reach_full_mod32_alphabet": all(len(s) == 32 for s in alphabets),
        "accepted_as_canonical_state": False,
    }


def macro_event_probe(
    pairs: list[tuple[int, ...]], growths: list[int], steps: int = 512
) -> dict[str, MacroReport]:
    """Measure no-growth-terminated macro events without retaining them as state."""
    by_run: dict[int, MacroSlot] = {}
    start = 0
    t = 0
    while t < min(steps, len(growths)):
        r = 0
        while t < min(steps, len(growths)) and growths[t]:
            r += 1
            t += 1
        if t >= min(steps, len(growths)):
            break
        source = pairs[start]
        target = pairs[t + 1]
        linear = [0] * (len(source) + r)
        for i, value in enumerate(source):
            for j in range(r + 1):
                linear[i + j] += 2 * value * comb(r, j)
        linear += [0] * (len(target) - len(linear))
        macro = tuple(target[i] - linear[i] for i in range(len(target)))
        slot = by_run.setdefault(
            r,
            {
                "count": 0,
                "rows": set(),
                "alphabet": set(),
                "support": 0,
                "positions": 0,
            },
        )
        slot["count"] += 1
        slot["rows"].add(macro)
        slot["alphabet"].update(macro)
        slot["support"] += sum(v != 0 for v in macro)
        slot["positions"] += len(macro)
        t += 1
        start = t
    out: dict[str, MacroReport] = {}
    for r, slot in sorted(by_run.items()):
        out[str(r)] = {
            "epochs": slot["count"],
            "unique_macro_rows": len(slot["rows"]),
            "coefficient_alphabet_size": len(slot["alphabet"]),
            "coefficient_min": min(slot["alphabet"]),
            "coefficient_max": max(slot["alphabet"]),
            "support_fraction": slot["support"] / slot["positions"],
        }
    return out


def live_carry_probe(steps: int = 512) -> dict[str, float]:
    pair = pair_from_int(196)
    pair, fixed = carry_seed_rows(pair, 20)
    live = LiveCarryItinerary.seed(fixed, base=10)
    rows = []
    live_bits = []
    fixed_bits = []
    for __2 in range(steps):
        assert live.pair == pair
        rows.append(live.row_count)
        live_bits.append(live.charged_carry_bits)
        fixed_bits.append(sum(len(row) for row in fixed))
        nxt_carry = carry_field(pair, base=10)
        live = live.advance()
        fixed = fixed[1:] + [nxt_carry]
        pair, __2 = pair_step(pair, 10)
    return {
        "steps": steps,
        "row_count_average": sum(rows) / len(rows),
        "row_count_minimum": min(rows),
        "row_count_maximum": max(rows),
        "average_live_carry_bits": sum(live_bits) / len(live_bits),
        "average_fixed20_carry_bits": sum(fixed_bits) / len(fixed_bits),
        "charged_bit_ratio": sum(live_bits) / sum(fixed_bits),
        "discarded_rows_after_probe": live.dropped_rows,
    }


def mod99_trace(steps: int = 15) -> list[dict[str, int]]:
    n = 196
    rows = []
    for t in range(steps):
        width = len(str(n))
        minus, plus = reverse_add_base_pm_residues(n, width, base=10)
        rows.append(
            {
                "step": t,
                "value_mod99": n % 99,
                "mod9": minus,
                "mod11": plus,
                "width": width,
            }
        )
        n += reverse_int(n)
    return rows


def main() -> None:
    OUT = (
        report_directory("devtools.benchmarks.cross_domain_itinerary_probe")
        / "cross_domain_itinerary_metrics.json"
    )
    REPORT = report_output(
        "devtools.benchmarks.cross_domain_itinerary_probe",
        "CROSS_DOMAIN_ITINERARY_RESULTS.md",
    )
    pairs, carries, events, growths, neutral, resets, positions = reverse_trace(512)
    vertical = vertical_itinerary_metrics(carries)
    runs = growth_run_itinerary(growths[:512])
    run_counts = dict(sorted(Counter(runs).items()))
    completed_steps = sum(r + 1 for r in runs)
    live_suffixes = [
        live_event_suffix_length(events[t - 20 : t], base=10) for t in range(20, 513)
    ]
    live_carry = live_carry_probe(512)
    macro_events = macro_event_probe(pairs, growths, 512)
    preimage_bits = [
        log2(pair_field_preimage_count(pair, base=10)) for pair in pairs[:513]
    ]
    cyclic_memory = {}
    for classes in (1, 2, 4, 8, 16):
        hs = [
            adaptive_cyclic_memory_horizon(growths, endpoint, classes=classes, bits=5)
            for endpoint in range(20, 513)
        ]
        cyclic_memory[str(classes)] = _summarize_horizons(hs)

    negacyclic_memory = {}
    for classes in (1, 2, 4, 8):
        hs = [
            adaptive_negacyclic_memory_horizon(
                growths, endpoint, classes=classes, bits=5
            )
            for endpoint in range(20, 513)
        ]
        negacyclic_memory[str(classes)] = _summarize_horizons(hs)

    primary_memory = {}
    for degree in (1, 2, 4, 8, 16):
        hs = [
            adaptive_zplus1_memory_horizon(growths, endpoint, degree=degree, bits=5)
            for endpoint in range(20, 513)
        ]
        primary_memory[str(degree)] = _summarize_horizons(hs)

    polynomial_ranks: dict[str, dict[str, list[int]]] = {}
    for prime in (2, 3, 5, 7):
        polynomial_ranks[str(prime)] = {}
        for classes in (2, 4, 8):
            polynomial_ranks[str(prime)][str(classes)] = [
                cyclic_growth_operator_rank(classes, prime, power=p)
                for p in range(1, min(8, 2 * classes) + 1)
            ]

    prime_polynomial_audit = {
        "F2_z2_plus_z_plus_1": [
            polynomial_growth_operator_rank((1, 1, 1), 2, power=p) for p in range(1, 9)
        ],
        "F3_z2_plus_1": [
            polynomial_growth_operator_rank((1, 0, 1), 3, power=p) for p in range(1, 9)
        ],
        "F3_zplus1_squared": [
            polynomial_growth_operator_rank((1, 2, 1), 3, power=p) for p in range(1, 4)
        ],
    }

    # Verify the z+1 palindrome factor whenever the pair width is even.
    even_width_checks = sum(
        1
        for pair in pairs[:513]
        if len(pair) % 2 == 0 and even_width_palindrome_has_z_plus_one_factor(pair)
    )
    even_width_total = sum(1 for pair in pairs[:513] if len(pair) % 2 == 0)
    assert even_width_checks == even_width_total

    m99 = mod99_trace()
    mod99_cycle = [row["value_mod99"] for row in m99[3:9]]
    assert mod99_cycle == [11, 22, 44, 88, 77, 55]

    vals = collatz_valuation_itinerary(27)
    slab = valuation_itinerary_slab(vals)
    decimal_fields = []
    n = 27
    physical = 0
    odd_steps = 0
    while n != 1:
        if n & 1:
            field = CollatzRawDigitField.from_odd_value(n, base=10)
            decimal_fields.append(field)
            n = 3 * n + 1
            odd_steps += 1
        else:
            n //= 2
        physical += 1
    monoid = mul3_carry_monoid()

    collatz_residue = {}
    for modulus in (5, 7, 11, 13, 31, 99, 101):
        affine = collatz_slab_mod_odd(slab, modulus)
        collatz_residue[str(modulus)] = {
            "multiplier": affine.multiplier,
            "offset": affine.offset,
            "seed27_image": affine.apply(27),
        }

    bucket_report = bucket_alphabet_probe()
    metrics = {
        "reverse_add": {
            "fixed_event_horizon": 20,
            "trace_steps": 512,
            "final_pair_width": len(pairs[512]),
            "growth_fraction": sum(growths[:512]) / 512,
            "threshold_neutral_fraction": neutral / positions,
            "threshold_reset_fraction": resets / positions,
            "pair_field_preimage_log2": {
                "average": sum(preimage_bits) / len(preimage_bits),
                "maximum": max(preimage_bits),
                "final": preimage_bits[-1],
            },
            "vertical_itinerary": vertical,
            "growth_run_counts": run_counts,
            "max_growth_run": max(runs),
            "completed_no_growth_epochs": len(runs),
            "physical_steps_covered_by_completed_epochs": completed_steps,
            "physical_steps_per_epoch": completed_steps / len(runs),
            "fixed20_live_event_suffix": {
                "average": sum(live_suffixes) / len(live_suffixes),
                "minimum": min(live_suffixes),
                "maximum": max(live_suffixes),
            },
            "self_pruning_live_carry_itinerary": live_carry,
            "epoch_macro_event_probe": macro_events,
            "cyclic_memory_horizons_mod32": cyclic_memory,
            "negacyclic_memory_horizons_mod32": negacyclic_memory,
            "zplus1_primary_memory_horizons_mod32": primary_memory,
            "negacyclic_m2_two_growth_kernel_mod32": list(
                negacyclic_transport_kernel(2, 0, 2, modulus=32)
            ),
            "prime_field_growth_operator_ranks": polynomial_ranks,
            "prime_polynomial_growth_rank_audit": prime_polynomial_audit,
            "mod99_trace": m99,
            "mod99_eventual_cycle": mod99_cycle,
            "even_width_z_plus_one_factor_checks": even_width_checks,
            "event_bucket_alternative": bucket_report,
        },
        "collatz": {
            "seed": 27,
            "physical_steps": physical,
            "odd_steps": odd_steps,
            "normalized_parity_steps": sum(vals),
            "valuation_symbols": len(vals),
            "valuation_max": max(vals),
            "valuation_itinerary": list(vals),
            "valuation_run_length_compression": sum(vals) / len(vals),
            "valuation_target_mod3": [
                accelerated_odd_target_mod3_from_valuation(v) for v in vals
            ],
            "mul3_carry_monoid_size": len(monoid),
            "decimal_mul3_carry_functions": [list(fn.outputs) for fn in monoid],
            "decimal_max_raw_component": max(f.max_component for f in decimal_fields),
            "decimal_max_carry": max(
                max(f.normalization_carries()) for f in decimal_fields
            ),
            "decimal_growth_odd_steps": sum(f.digit_growth for f in decimal_fields),
            "whole_valuation_slab": {
                "width": slab.width,
                "ones": slab.ones,
                "description_bits": slab.description_bits,
                "image_of_27": slab.apply(27),
            },
            "odd_modulus_affine_projections": collatz_residue,
        },
        "conclusions": {
            "raw_vertical_carry_itinerary_small_alphabet": False,
            "threshold_last_event_coordinate_exact_but_sparse_enough": False,
            "adaptive_dead_event_prefix_exists": True,
            "epoch_macro_event_alphabet_small": False,
            "mod99_is_exact_eventual_small_cycle_for_196": True,
            "z2_growth_channel_rank_collapse": True,
            "negacyclic_two_growths_gain_factor_two": True,
            "zplus1_primary_growth_is_nilpotent_shift": True,
            "generic_irreducible_prime_polynomial_forgetting": False,
            "additive_hyperbolic_digit_fiber_already_quotiented": True,
            "collatz_decimal_five_element_carry_monoid": True,
            "collatz_valuation_is_tropical_nested_divisor_quotient": True,
            "five_bucket_event_state_kept": False,
            "full_reverse_add_behavioral_quotient_found": False,
        },
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(metrics, indent=2, sort_keys=True) + "\n")

    cm = cyclic_memory
    b = bucket_report
    lines: list[str] = []
    lines.append("# Cross-domain itinerary / residue / pair-field results\n")
    lines.append(
        "This probe applies the newer Collatz/prime quotient ideas back to reverse-and-add, "
        "and the reverse-and-add pair/carry machinery back to Collatz. Every compact result "
        "is charged separately from the work needed to derive it.\n"
    )
    lines.append("## Reverse-and-add: carry/event itinerary\n")
    lines.append(
        f"A raw transpose of the 20-row carry slab is **not** a finite-small alphabet on the "
        f"decimal-196 trace: across {vertical['columns']:,} sampled spacetime columns it realizes "
        f"**{vertical['unique_carry_words']:,}** distinct 20-bit carry histories "
        f"({vertical['unique_active_carry_words']:,} including active-domain history). This rejects "
        "the naive `20-bit vertical symbol -> finite automaton` idea.\n"
    )
    lines.append(
        f"The exact threshold itinerary `LOW / NEUTRAL / HIGH` is a last-event monoid, but neutral "
        f"`S_i=9` positions are only **{100 * neutral / positions:.2f}%** of the sampled pair field. "
        f"Encoding only non-neutral reset positions would therefore retain **{100 * resets / positions:.2f}%** "
        "of positions before even charging their indices, so it is rejected as the primary spatial carrier.\n"
    )
    lines.append("### No-growth epoch coordinate\n")
    lines.append(
        f"The branch itinerary has a useful bounded radix: completed growth runs have lengths "
        f"{run_counts}, with maximum **{max(runs)}**. A no-growth epoch is therefore one radix-4 "
        f"symbol `r in {{0,1,2,3}}` with physical duration `r+1`. Over the first 512 transitions "
        f"the completed epochs average **{completed_steps / len(runs):.3f} physical steps/symbol**. "
        "This is an exact weighted-time coordinate, but it only gives a constant-factor reduction "
        "until the macro-event generator itself is quotiented.\n"
    )
    lines.append("### Self-pruning live carry itinerary\n")
    lines.append(
        f"The fixed H=20 theorem contains a stronger source-specialized quotient. Once an old event has "
        f"five later no-growth doublings, its transported contribution is identically zero mod 32 and "
        f"that row can be discarded forever. Seeded once from an ordinary 20-row certificate, the "
        f"`LiveCarryItinerary` reconstructs the exact pair from only its surviving carry suffix, generates "
        f"the next carry, appends it, and prunes itself again. Over 512 advances it retains **"
        f"{live_carry['row_count_average']:.3f} rows on average** ("
        f"{live_carry['row_count_minimum']}..{live_carry['row_count_maximum']}) and charges **"
        f"{100 * live_carry['charged_bit_ratio']:.2f}%** as many carry bits as the fixed 20-row window. "
        "This is an exact temporal-history quotient, but it does not by itself quotient the repeated "
        "nonlinear action used by powering.\n"
    )
    lines.append("### Macro-event generator audit\n")
    lines.append(
        "Collapsing each radix-4 growth run into one no-growth-terminated macro event does **not** reveal "
        "a small event alphabet. The exact macro forcing row is `F_r=S_out-2(1+z)^r S_in`:\n\n"
        "| r | epochs | unique rows | coefficient alphabet | support fraction |\n"
        "|---:|---:|---:|---:|---:|"
    )
    for r, macro_row in macro_events.items():
        lines.append(
            f"| {r} | {macro_row['epochs']} | {macro_row['unique_macro_rows']} | "
            f"{macro_row['coefficient_alphabet_size']} | {macro_row['support_fraction']:.3f} |"
        )
    lines.append(
        "\nThe rows are nearly unique and become dense as `r` grows, so a direct four-symbol macro-event "
        "alphabet is rejected. The growth-run itinerary is useful control information, not a replacement "
        "for the nonlinear event generator.\n"
    )
    lines.append("### Additive hyperbolic fiber is already quotiented\n")
    lines.append(
        f"The prime factor surface `n=q*r` has an additive digit analogue `s=a+b`. But the canonical "
        f"pair field has already performed exactly that quotient: carry/event evolution depends on `s` "
        f"and never on the individual `(a,b)`. Across the sampled trajectory, one pair field represents "
        f"an average of about **2^{sum(preimage_bits) / len(preimage_bits):.2f}** fixed-width source digit "
        f"assignments (maximum **2^{max(preimage_bits):.2f}**). Reintroducing left/right digit lanes would "
        "therefore reverse a large existing canonicalization.\n"
    )
    lines.append("### Polynomial/cyclotomic event memory\n")
    lines.append(
        "For the cyclic quotient `z^m=1` modulo 32, the old-state transport is `2^q(1+z)^r`. "
        "The measured exact dependency horizons on the same trajectory are:\n\n"
        "| classes m | average horizon | maximum |\n|---:|---:|---:|"
    )
    for m_1 in (1, 2, 4, 8, 16):
        row = cm[str(m_1)]
        lines.append(f"| {m_1} | {row['average']:.3f} | {row['maximum']} |")
    lines.append(
        "\nThe `m=2` quotient is especially strong: `I+shift` has rank one over odd prime "
        "fields; over `F_2` its square is zero. Thus the alternating (`z=-1`) channel is reset "
        "by one growth step, while the full two-class old-state operator dies after at most six "
        "recent steps mod 32 on branch-count combinations sufficient for annihilation.\n"
    )
    lines.append(
        "### Prime-polynomial audit and the stronger `(z+1)`-primary coordinate\n"
    )
    lines.append(
        "Generic irreducible/prime polynomials do not give the desired forgetting. In `F_p[z]/(f)`, "
        "multiplication by `1+z` is a unit whenever irreducible `f != z+1`. The executable rank audit "
        f"keeps full rank for `z^2+z+1` over F2 (`{prime_polynomial_audit['F2_z2_plus_z_plus_1']}`) and "
        f"`z^2+1` over F3 (`{prime_polynomial_audit['F3_z2_plus_1']}`). Rank loss appears only in the "
        "`z+1` primary component.\n\n"
        "Writing `y=z+1` makes that useful component explicit: modulo `(y^k,32)`, a growth step is "
        "**literal multiplication by y**, while a no-growth step is multiplication by 2. Hence old state "
        "dies exactly when either five no-growths or `k` growths have occurred. Measured horizons are:\n\n"
        "| jet degree k | average horizon | maximum |\n|---:|---:|---:|"
    )
    for k in (1, 2, 4, 8, 16):
        row = primary_memory[str(k)]
        lines.append(f"| {k} | {row['average']:.3f} | {row['maximum']} |")
    lines.append(
        "\nThis is the cleanest polynomial itinerary coordinate found: it is a nilpotent shift conjugacy "
        "for the linear transport. It remains a theorem-interface projection because a small jet is not "
        "injective enough to reconstruct every local pair coefficient/carry.\n"
    )
    lines.append("### Negacyclic / `b^m+1` residues\n")
    lines.append(
        "The complementary quotient `z^m=-1` corresponds to radix residues of the `b^m+1` family. "
        "For `m=2`, `(1+z)^2=2z`, so **two growths buy one full 2-adic decay factor**. Modulo 32 the exact "
        f"kernel is `{negacyclic_transport_kernel(2, 0, 2, modulus=32)}`. The measured dependency horizons are:\n\n"
        "| m | average horizon | maximum |\n|---:|---:|---:|"
    )
    for m_2 in (1, 2, 4, 8):
        row = negacyclic_memory[str(m_2)]
        lines.append(f"| {m_2} | {row['average']:.3f} | {row['maximum']} |")
    lines.append(
        "\nThis explains why arbitrary modulus search is less useful than choosing a polynomial factor where "
        "the transport itself acquires 2-adic valuation.\n"
    )
    lines.append("### mod 99 / z+1 factor\n")
    lines.append(
        f"For decimal reversal, modulo 9 the transition is always doubling. Modulo 11, an even-width "
        f"source maps to zero because a palindromic pair polynomial of even width has the exact factor "
        f"`z+1`; zero is absorbing thereafter. Decimal 196 first enters that channel at step 3 and "
        f"from then on its mod-99 residue is the exact six-cycle\n\n`{mod99_cycle}`.\n\n"
        f"All **{even_width_checks} / {even_width_total}** sampled even-width pair fields satisfy the "
        "exact `z+1` factor identity. This is a useful theorem-interface/residue quotient, but it is "
        "not injective enough to replace the carry slab.\n"
    )
    lines.append("### Rejected five-bucket event regrouping\n")
    lines.append(
        f"Grouping event memory by the five powers of two would use **{b['total_bitplanes']} coefficient "
        f"bitplanes** instead of 20 binary carry rows, and every bucket reaches the full 32-value "
        f"alphabet (`{b['alphabet_sizes']}`). Once the existing prefix-domain metadata is charged "
        "correctly this is not a smaller canonical carrier, so it is **not retained as semantic state**.\n"
    )
    lines.append("## Collatz: reverse-and-add pair/carry machinery\n")
    lines.append(
        f"For an odd decimal step, the raw digit field is `R_i=3*d_i+[i=0]`, whose largest possible "
        f"component is **28**. After the LSD the carry alphabet is exactly `{{0,1,2}}`; the ordinary "
        f"decimal digits induce the closed five-element transfer monoid\n\n"
        f"`{[fn.outputs for fn in monoid]}`.\n\n"
        "So `3*n+1` has a native five-element spatial carry scan rather than a generic multiplication transducer.\n"
    )
    lines.append(
        f"The prime-style divisor quotient is even cleaner. The nested lanes `2^k | 3*n+1` canonicalize "
        f"by tropical **max** to the single value `v2(3*n+1)`. For seed 27, **{sum(vals)} normalized "
        f"parity steps** become **{len(vals)} valuation symbols** (max valuation {max(vals)}), a "
        f"**{sum(vals) / len(vals):.3f}x** run-length reduction. Their native affine slab is "
        f"`(width={slab.width}, ones={slab.ones})` and maps 27 directly to **{slab.apply(27)}**.\n"
    )
    lines.append(
        "This valuation symbol also completely determines the next accelerated odd state modulo 3: "
        "`target mod 3 = 2^(-v) mod 3 = (-1)^v`. The old odd-state residue disappears, so mod 3 is "
        "derived directly from the tropical itinerary rather than stored as another channel.\n"
    )
    lines.append(
        "Odd-modulus / prime-field projection of that entire slab is one affine map `x -> a*x+b`; "
        "this commutes with slab composition, so prime residues are theorem-interface projections and "
        f"do not require replaying the Collatz orbit. Mod 99, the whole seed-27 valuation slab is the "
        f"single affine map `x -> {collatz_residue['99']['multiplier']}*x+"
        f"{collatz_residue['99']['offset']}` and sends 27 to {collatz_residue['99']['seed27_image']}.\n"
    )
    lines.append("## Net result\n")
    lines.append(
        "The cross-domain transfer now separates the remaining problem more sharply. Reverse-and-add gains "
        "an exact self-pruning live carry itinerary and a `(z+1)`-primary nilpotent transport coordinate; "
        "Collatz gains the five-element decimal `3*n+1` carry monoid and tropical valuation itinerary. "
        "Generic prime-polynomial quotients, raw vertical histories, threshold-reset positions, and direct "
        "macro-event alphabets all fail the charged compression test.\n\n"
        "It still does **not** produce an injective finite/polylog quotient of the full powered reverse-and-add "
        "nonlinear action. The next target should combine the live-suffix certificate with primary-jet theorem "
        "interfaces so equivalent nonlinear slab actions can canonicalize **before** composition; merely "
        "packing the surviving rows or their macro events would only be another representation cleanup.\n"
    )
    REPORT.write_text("\n".join(lines))
    print(json.dumps(metrics, indent=2, sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
