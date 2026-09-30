"""Emit v0.53.0 metrics for constrained special-source theorem work."""

from __future__ import annotations

from devtools.paths import report_directory

import json
from typing import TYPE_CHECKING

from devtools.paths import repository_root
from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
from number_compiler.api.sequence_types import FermatSequenceSpec, MersenneSequenceSpec
from number_compiler.arithmetic.fields.symbolic_extent import extent_json_value
from number_compiler.projection.output_quotient import SpecialSourceShape

if TYPE_CHECKING:
    from number_compiler.api.sequence_types import (
        FermatCompiledTerm,
        MersenneCompiledTerm,
    )
    from number_compiler.sequences.power_numbers.theorem_query import (
        SpecialTheoremResolution,
    )


ROOT = repository_root()


def _term_metrics(
    term: FermatCompiledTerm | MersenneCompiledTerm,
) -> dict[str, object]:
    return {
        "parameter": int(getattr(term, "index", getattr(term, "exponent", -1))),
        "number_bits": extent_json_value(term.number_bits),
        "projection_method": term.projection_method,
        "primality_attached": term.primality is not None,
        "factor_witness_attached": term.factor_witness is not None,
        "source_guard_attached": term.source_guard is not None,
        "factored_projection_attached": term.radix_word.factored_projection is not None,
    }


def _resolution_metrics(
    row: SpecialTheoremResolution,
) -> dict[str, object]:
    cert = row.primality
    return {
        "method": row.projection_method,
        "failure_bit": row.source_guard.failure_bit,
        "factor_witness": row.factor_witness,
        "raw_squarings": None if cert is None else cert.specialization_raw_squarings,
        "gcd_witnesses": None if cert is None else cert.gcd_witnesses,
    }


def main() -> None:
    compiler = CanonicalSequenceCompiler()
    fcomp = compiler.compile(FermatSequenceSpec((2, 4, 5, 12), test_through=99))
    mcomp = compiler.compile(
        MersenneSequenceSpec((11, 13, 15, 31, 8191), test_through=99)
    )
    source_cache_after_compile = compiler.cache_size
    theorem_cache_after_compile = compiler.theorem_cache_size

    # test_through is theorem policy, not numeric source identity.
    f_alias = compiler.compile(FermatSequenceSpec((2, 4, 5, 12), test_through=0))
    m_alias = compiler.compile(
        MersenneSequenceSpec((11, 13, 15, 31, 8191), test_through=0)
    )

    # Coherent PASS-sheet source constraints are pulled back and persisted.
    cheap = {
        "f4_digit16": compiler.project_special_digit("fermat", 4, 16, 1, 0).value,
        "f4_parity": compiler.project_special_parity("fermat", 4, 17, 16).value,
        "f4_length": compiler.project_special_length("fermat", 4, 17, 16).value,
        "f4_carry": compiler.project_special_carry("fermat", 4, 2, 2, 9).value,
        "f4_boundary": compiler.project_special_boundary_sign("fermat", 4, -1, 1).value,
        "m13_digit7": compiler.project_special_digit("mersenne", 13, 7, 1, 0).value,
        "m13_length": compiler.project_special_length("mersenne", 13, 13, 12).value,
    }
    cache_after_cheap = compiler.theorem_cache_size
    f4_reused = compiler.project_special_branch_values("fermat", 4, 3, 7)
    f4_pulled = compiler.resolve_special_theorem("fermat", 4)

    # A candidate-derived powered defect accumulates as one support gcd.  The
    # proper support of F5 kills the PASS sheet without Pépin or a factor scan.
    support = CanonicalSequenceCompiler()
    f5_modulus = (1 << 32) + 1
    f5_state = support.pullback_special_defect(
        "fermat",
        5,
        f5_modulus,
        641,
        method="powered-target-defect",
    )
    f5_pulled = support.resolve_special_theorem("fermat", 5)
    f5_later = support.project_special_branch_values("fermat", 5, 3, 7)

    # With no evidence, a separating coordinate remains guarded.  Concrete
    # demand invokes the exact classical ceiling, not tropical enumeration.
    fresh = CanonicalSequenceCompiler()
    guarded = fresh.project_special_branch_values("mersenne", 13, 3, 7)
    forced = fresh.project_special_branch_values(
        "mersenne",
        13,
        3,
        7,
        require_concrete=True,
    )

    # Default theorem queries use no factor prepass and exactly B-2 nonlinear
    # recurrence steps after the logarithmic constraint/germ attempt.
    ceiling = CanonicalSequenceCompiler()
    f4 = ceiling.resolve_special_theorem("fermat", 4)
    f5 = ceiling.resolve_special_theorem("fermat", 5)
    m11 = ceiling.resolve_special_theorem("mersenne", 11)
    m13 = ceiling.resolve_special_theorem("mersenne", 13)
    m31 = ceiling.resolve_special_theorem("mersenne", 31)
    m15 = ceiling.resolve_special_theorem("mersenne", 15)

    # An unused factor_limit is normalized out of theorem cache identity.
    normalized = CanonicalSequenceCompiler()
    a = normalized.resolve_special_theorem(
        "fermat",
        4,
        factor_limit=17,
        use_terminal_certificate=False,
    )
    b = normalized.resolve_special_theorem(
        "fermat",
        4,
        factor_limit=99991,
        use_terminal_certificate=False,
    )

    fshape = SpecialSourceShape("fermat", 4)
    mshape = SpecialSourceShape("mersenne", 13)
    payload = {
        "version": "0.53.0",
        "raw_source": {
            "fermat": [_term_metrics(term) for term in fcomp.terms],
            "mersenne": [_term_metrics(term) for term in mcomp.terms],
            "source_cache_after_compile": source_cache_after_compile,
            "theorem_cache_after_compile": theorem_cache_after_compile,
            "legacy_test_through_aliases_source_cache": f_alias is fcomp
            and m_alias is mcomp,
        },
        "source_shapes": {
            "f4": {
                "bit_length": extent_json_value(fshape.bit_length),
                "boundary_sign": fshape.boundary_sign,
                "digits_0_1_16_17": [fshape.digit(i) for i in (0, 1, 16, 17)],
            },
            "m13": {
                "bit_length": extent_json_value(mshape.bit_length),
                "boundary_sign": mshape.boundary_sign,
                "digits_0_12_13": [mshape.digit(i) for i in (0, 12, 13)],
            },
        },
        "persistent_mask_pullback": {
            "cheap_outputs": cheap,
            "theorem_cache_after_cheap": cache_after_cheap,
            "constraint_cache_size": compiler.special_constraint_cache_size,
            "later_coordinate_mode": f4_reused.mode.value,
            "later_coordinate_value": f4_reused.value,
            "theorem_resolution_method": f4_pulled.projection_method,
            "theorem_cache_after_reuse": compiler.theorem_cache_size,
        },
        "support_gcd_pullback": {
            "support_gcd": f5_state.support_gcd,
            "support_modulus": f5_state.support_modulus,
            "resolution": _resolution_metrics(f5_pulled),
            "later_coordinate_mode": f5_later.mode.value,
            "later_coordinate_value": f5_later.value,
            "theorem_cache_size": support.theorem_cache_size,
        },
        "unresolved_then_classical": {
            "initial_mode": guarded.mode.value,
            "forced_mode": forced.mode.value,
            "forced_value": forced.value,
            "theorem_cache_size": fresh.theorem_cache_size,
        },
        "classical_ceiling": {
            "f4": _resolution_metrics(f4),
            "f5": _resolution_metrics(f5),
            "m11": _resolution_metrics(m11),
            "m13": _resolution_metrics(m13),
            "m31": _resolution_metrics(m31),
            "m15": _resolution_metrics(m15),
        },
        "factor_limit_cache_normalization": {
            "same_object": a is b,
            "cache_size": normalized.theorem_cache_size,
        },
    }
    out = (
        report_directory("devtools.benchmarks.special_constraint_pullback_probe")
        / "special_constraint_pullback_metrics.json"
    )
    text = json.dumps(payload, indent=2) + "\n"
    out.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
