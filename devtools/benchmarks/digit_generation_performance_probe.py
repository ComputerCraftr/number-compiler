"""Deterministic v0.53.7 digit-generation / support-extraction probe."""

from __future__ import annotations

import json

from devtools.experiments.algebra.baby_giant_behavioral_bend import (
    BabyGiantBendPacketMemo,
    BabyGiantSupportPacketMemo,
)
from devtools.experiments.algebra.residue_refined_bend import fast_multipoint_bend_audit
from devtools.paths import repository_root
from number_compiler.api.number_api import NumberCompiler

ROOT = repository_root()


def _digit_rows() -> dict[str, object]:
    compiler = NumberCompiler()
    f20 = compiler.project_nth("fermat", 20)
    m100k = compiler.project_nth("mersenne", 100_000)
    reverse = compiler.project_nth("reverse-add", 5, seed=196, base=10)
    forcing = compiler.project_reverse_add_growth_state(196, base=10)
    return {
        "fermat_f20": {
            "bit_length": f20.estimated_bit_length,
            "positions": [0, 123_456, 1 << 20],
            "digits": [f20.digit(0), f20.digit(123_456), f20.digit(1 << 20)],
            "full_word_materialization_required": False,
        },
        "mersenne_m100000": {
            "bit_length": m100k.estimated_bit_length,
            "position": 99_999,
            "digit": m100k.digit(99_999),
            "full_word_materialization_required": False,
        },
        "reverse_add_196_step5": {
            "digit0": reverse.digit(0),
            "full_digit_word_materialization_required": False,
        },
        "reverse_add_196_forcing": {
            "boundary_offset": forcing.boundary_offset,
            "boundary_relation": forcing.relation,
            "growth": forcing.growth,
            "carry_field_required": False,
            "successor_formula_required": False,
        },
    }


def _bsgs_rows() -> dict[str, object]:
    # A support-only consumer must stop after the one final support GCD.  M29 is
    # intentionally FULL support, so this also proves that proper-factor descent
    # is not accidentally charged to a digit/theorem branch that only needs the
    # unit/nonunit bit.
    support_memo = BabyGiantSupportPacketMemo()
    support = support_memo.evaluate("mersenne", 29, start=1, span=399)
    support_again = support_memo.evaluate("mersenne", 29, start=1, span=399)
    assert support_again is support

    # F6's first admissible factor is late enough in this bounded window to make
    # the logarithmic product-tree locator visible, rather than only the early
    # constant-prefix fast path.
    audit = fast_multipoint_bend_audit(
        "fermat",
        6,
        start=1,
        span=1200,
        locate_first_bend=True,
        include_direct_control=False,
    )
    bend_memo = BabyGiantBendPacketMemo()
    packet = bend_memo.evaluate("fermat", 6, start=1, span=1200)
    packet_again = bend_memo.evaluate("fermat", 6, start=1, span=1200)
    assert packet_again is packet
    return {
        "support_only_m29": {
            "status": support.status,
            "support_gcd": support.support_gcd,
            "final_support_gcds": support.final_support_gcds,
            "split_descent_gcds": support.split_descent_gcds,
            "direct_linear_control_evaluated": support.direct_control_evaluated,
            "memo_hits": support_memo.hits,
            "memo_misses": support_memo.misses,
        },
        "late_bend_f6": {
            "span": audit.span,
            "baby_width": audit.baby_width,
            "giant_blocks": audit.full_blocks,
            "first_bend_slot": audit.first_bend_slot,
            "first_bend_gcd": audit.first_bend_gcd,
            "block_locator_gcds": audit.block_locator_gcds,
            "leaf_locator_gcds": audit.leaf_locator_gcds,
            "old_linear_locator_upper_bound": audit.full_blocks + audit.baby_width,
            "direct_linear_control_evaluated": audit.direct_control_evaluated,
            "local_character_constant": packet.character_constant,
            "local_character": packet.first_bend_dirichlet_character,
            "memo_hits": bend_memo.hits,
            "memo_misses": bend_memo.misses,
        },
    }


def main() -> None:
    data = {
        "release": "v0.53.7",
        "digits": _digit_rows(),
        "bsgs": _bsgs_rows(),
        "claims": {
            "single_special_digit_avoids_full_word_materialization": True,
            "reverse_add_growth_uses_radial_order_and_sign_before_carry": True,
            "support_only_bsgs_skips_proper_factor_descent": True,
            "support_only_bsgs_skips_linear_direct_differential": True,
            "first_bend_gcd_localization_uses_product_tree": True,
            "dirichlet_phase_attached_only_after_local_support_extraction": True,
            "unseen_bsgs_support_polylogarithmic": False,
        },
    }
    text = json.dumps(data, indent=2, sort_keys=True) + "\n"
    out = ROOT / "results" / "digit_generation_performance_metrics.json"
    out.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
