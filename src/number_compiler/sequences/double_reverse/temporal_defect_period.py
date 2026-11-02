"""Production source-bound finite period samples of the combined carry defect.

One pointed *input* suffix yields both carry waves of the next two T-squared
updates.  A second pointed cone for either intermediate state is unnecessary.
This is a quotient-first output demand, not a finite-window claim of an
infinite seed period.
"""

from __future__ import annotations

from collections.abc import Sequence
from typing import TYPE_CHECKING

from .temporal_defect_quotient import (
    FourSymbolDefect,
)
from .temporal_four_observer import (
    CYCLIC_NEGACYCLIC_MODULI,
    FourObserverAffineClock,
    FourObserverEmission,
    projected_period_profiles,
)
from .temporal_hashlife import growth_ports
from .temporal_hashlife_types import UncertifiedPointedStencilError

if TYPE_CHECKING:
    from .source_bound_bank import PointedBankSource


def _tail_lags(
    values: Sequence[object], max_lag: int
) -> tuple[list[int], dict[str, int] | None]:
    count = len(values)
    complete = [
        p
        for p in range(1, min(max_lag, count - 1) + 1)
        if all(values[i] == values[i - p] for i in range(p, count))
    ]
    best: dict[str, int] | None = None
    # Find the last violating comparison for each lag. This gives the exact
    # earliest periodic suffix start in O(samples * max_lag) comparisons; no
    # quadratic rescan of every possible transient is necessary.
    for p in range(1, min(max_lag, count // 3) + 1):
        last_mismatch = max(
            (i for i in range(p, count) if values[i] != values[i - p]),
            default=-1,
        )
        start = max(0, last_mismatch - p + 1)
        if count - start >= 3 * p:
            candidate = {
                "observed_lag": p,
                "sample_start": start,
                "samples": count - start,
            }
            # Prefer the LONGEST supported suffix; within that same
            # transient, choose the primitive candidate. A spurious short
            # repetition in the last 3p samples must not overshadow a much
            # longer period that holds for the entire tested window.
            if best is None or (start, p) < (
                best["sample_start"],
                best["observed_lag"],
            ):
                best = candidate
    return complete, best


def source_bound_defect_period_packet(
    source: PointedBankSource,
    *,
    digits: int,
    samples: int,
    stride: int,
    max_lag: int,
) -> dict[str, object]:
    """Compile one exact carry-mask/defect suffix quotient per macro sample.

    The final sample is the macro immediately preceding the requested source
    endpoint; every output is inside the authenticated temporal horizon.
    No input occurrence is used as a semantic ID or assumed future driver.
    """
    source.validate(require_issued_cursor=True)
    if type(digits) is not int or not 1 <= digits <= 96:
        raise ValueError("combined defect width must be in 1..96")
    if type(samples) is not int or not 1 <= samples <= 128:
        raise ValueError("defect samples must be in 1..128")
    if type(stride) is not int or not 1 <= stride <= 4096:
        raise ValueError("defect stride is invalid")
    if type(max_lag) is not int or not 1 <= max_lag <= 128:
        raise ValueError("defect lag limit is invalid")
    if samples * (digits + 4) > 8192:
        raise ValueError("defect suffix sample budget exceeded")
    available = (source.f_steps // 2 - 1) // stride + 1 if source.f_steps >= 2 else 0
    count = min(samples, available)
    if count < 1:
        return {
            "status": "unavailable",
            "reason": "at least two source-authenticated T-squared updates are needed",
            "infinite_period_certified": False,
        }
    last_f = source.f_steps - 2
    start_f = last_f - 2 * stride * (count - 1)
    rows: list[dict[str, object]] = []
    emission_tape = source.engine.pointed_combined_defect_tape(
        source.root, start_f, source.phase, digits, count, stride
    )
    shared_halo = emission_tape.halo_segments == 1
    defects: list[FourSymbolDefect] = []
    emissions: list[FourObserverEmission] = []
    for i in range(count):
        f = start_f + 2 * stride * i
        try:
            candidate = emission_tape.emissions[i]
            if type(candidate) is not FourSymbolDefect:
                raise AssertionError("foreign combined carry defect")
            defect = candidate
            defect.verify()
        except ValueError as exc:
            return {
                "status": "unavailable",
                "reason": str(exc),
                "failed_sample_generation": source.physical_prefix + 2 * f,
                "infinite_period_certified": False,
            }
        defects.append(defect)
        current_phase = (source.phase + 2 * f) % 4
        source_width = source.width_in + sum(growth_ports(source.phase, f))
        emission = FourObserverEmission.from_source(
            defect, phase=current_phase, source_width=source_width
        )
        emissions.append(emission)
        rows.append(
            {
                "generation": source.physical_prefix + 2 * f,
                "macro_phase": (source.phase + 2 * f) % 4,
                "width": source_width,
                "growth_bits": [defect.first_growth, defect.second_growth],
                "carry_first": str(defect.first_carries).zfill(digits),
                "carry_second_aligned": str(defect.second_carries).zfill(digits),
                "defect_decimal": defect.emission_digits(),
                "defect_base5": defect.base5_digits(),
                "dual_directional_carries": {
                    "first_half_right": defect.first_directional.ordered_right_bits(),
                    "first_half_left": defect.first_directional.ordered_left_bits(),
                    "second_half_right": defect.second_directional.ordered_right_bits(),
                    "second_half_left": defect.second_directional.ordered_left_bits(),
                    "left_output_reference": "left-to-right characters are emitted from the right boundary",
                },
                "left_wave_defect_decimal": str(defect.left_defect_decimal()).zfill(
                    digits
                ),
                "left_wave_defect_base5": defect.left_base5_digits(),
                "left_wave_mirrored_decimal": str(
                    defect.left_mirrored_defect_decimal()
                ).zfill(digits),
                # The internal carry factors below describe only the bounded
                # retained suffix. The repunit overflow components have the
                # correct global border width phase.
                "four_observer_cyclotomic": {
                    str(mod): list(emission.cyclotomic_key(mod))
                    for mod in CYCLIC_NEGACYCLIC_MODULI
                },
                "four_observer_carry_difference": {
                    "aligned_local_signed": emission.difference,
                    "mod_10w": emission.difference % (10**digits),
                    "signed_99_local_difference": 99 * emission.difference,
                    "padic_units": emission.difference_signature(),
                    "global_reflection_inferred": False,
                    "same_suffix_coordinate": True,
                },
                "boundary_only_overflow_observers": {
                    "right_bits": list(emission.right_overflow),
                    "mirrored_left_bits": list(emission.mirrored_left_overflow),
                    "right_defect_mod_10w": list(
                        emission.right_overflow_defects(digits)
                    ),
                    "mirrored_left_defect_mod_10w": list(
                        emission.mirrored_left_overflow_defects(digits)
                    ),
                    "boundary_phases_source_certified": True,
                    "additive_physical_forcing": False,
                },
                "source_mod_2x10w": defect.input_modulus,
                "target_mod_2x10w": defect.output_modulus,
            }
        )

    # A single comparison of two carry words determines every smaller
    # decimal suffix precision: v_10(a-b) is the number of agreeing low
    # columns. Build right, left, signed-difference and four-output period
    # profiles together, without scanning each width independently.
    profiles = projected_period_profiles(emissions, max_lag)
    right_profile = profiles["right"]
    left_profile = profiles["left"]
    joint_profile = profiles["joint"]
    difference_profile = profiles["difference"]
    four_profile = profiles["four"]
    cyclotomic_profiles = {}
    for modulus in CYCLIC_NEGACYCLIC_MODULI:
        mod_lags, mod_tail = _tail_lags(
            [e.cyclotomic_key(modulus) for e in emissions], max_lag
        )
        cyclotomic_profiles[str(modulus)] = {
            "source_scope": "bounded-carry-suffix-plus-exact-global-overflow-phase",
            "finite_window_period_lags": mod_lags,
            "observed_tail_candidate": mod_tail,
            "unit_width_clock": True,
        }
    source_residue_lags, source_residue_tail = _tail_lags(
        [d.input_modulus for d in defects], max_lag
    )
    chain_checked = False
    joint_clock: FourObserverAffineClock | None = None
    if stride == 1:
        for before, after in zip(defects, defects[1:], strict=False):
            if before.output_modulus != after.input_modulus:
                raise AssertionError(
                    "successive normalized defect suffixes fail temporal seam"
                )
        chain_checked = True
        # One product in the four-output abelian affine action. The physical
        # signed clock is its RIGHT projection, not a separately composed
        # duplicate using the very same emissions and multiplier.
        joint_clock = FourObserverAffineClock.identity(digits)
        for emission in emissions:
            joint_clock = joint_clock.then(
                FourObserverAffineClock.from_emission(emission)
            )
        if (
            joint_clock.multiplier * defects[0].input_modulus
            + joint_clock.right_forcing
        ) % joint_clock.modulus != defects[-1].output_modulus:
            raise AssertionError("combined temporal signed cocycle failed source seam")

    result: dict[str, object] = {
        "status": "available",
        "representation": "four-symbol-reversed-carry-defect",
        "digits": digits,
        "physical_stride": 4 * stride,
        "samples": count,
        "rows": rows,
        "finite_window_period_lags": right_profile["finite_window_period_lags"],
        "observed_tail_candidate": right_profile["observed_tail_candidate"],
        "defect_suffix_period_hierarchy": right_profile["suffix_period_hierarchy"],
        "left_wave_finite_lags": left_profile["finite_window_period_lags"],
        "left_wave_observed_tail_candidate": left_profile["observed_tail_candidate"],
        "joint_directional_finite_lags": joint_profile["finite_window_period_lags"],
        "joint_directional_observed_tail_candidate": joint_profile[
            "observed_tail_candidate"
        ],
        "joint_directional_suffix_period_hierarchy": joint_profile[
            "suffix_period_hierarchy"
        ],
        "four_observer_finite_lags": four_profile["finite_window_period_lags"],
        "four_observer_observed_tail_candidate": four_profile[
            "observed_tail_candidate"
        ],
        "four_observer_suffix_period_hierarchy": four_profile[
            "suffix_period_hierarchy"
        ],
        "directional_difference_finite_lags": difference_profile[
            "finite_window_period_lags"
        ],
        "directional_difference_observed_tail_candidate": difference_profile[
            "observed_tail_candidate"
        ],
        "directional_difference_suffix_period_hierarchy": difference_profile[
            "suffix_period_hierarchy"
        ],
        "four_observer_boundary_carries_source": "certified-border-macro",
        "four_observer_cyclotomic_periods": cyclotomic_profiles,
        "period_analysis": "single-pass-valuative-mismatch-quotient",
        "overflow_observers_are_counterfactual_comparisons": True,
        "true_whole_word_mirrored_carry_defect_issued": False,
        "four_observer_future_right_congruence_proved": False,
        "four_observer_repeat_power_requires_external_certificate": True,
        "directional_reversal_conjugacy": True,
        "directional_inputs_independent": False,
        "normalized_residue_finite_lags": source_residue_lags,
        "normalized_residue_tail_candidate": source_residue_tail,
        "nilpotent_history_cutoff_macro_steps": digits,
        "suffix_period_equivalence_modulus": 2 * 10**digits,
        "signed_cocycle_temporal_seam_verified": chain_checked,
        "independent_intermediate_cones": 0,
        "shared_source_halo": shared_halo,
        "local_t_squared_steps": emission_tape.locally_advanced_f_steps,
        "source_halo_segments": emission_tape.halo_segments,
        "segmented_source_halo": emission_tape.halo_segments > 1,
        "infinite_period_certified": False,
        "scope": (
            "exact finite, source-authenticated four-symbol carry observations; "
            "no asserted future periodicity"
        ),
    }
    if joint_clock is not None:
        result["four_observer_composed_action"] = {
            "macro_steps": joint_clock.steps,
            "multiplier": joint_clock.multiplier,
            "right_physical_forcing": joint_clock.right_forcing,
            "left_formal_forcing": joint_clock.left_forcing,
            "directional_contrast": joint_clock.directional_contrast,
            "right_overflow_formal_forcing": joint_clock.right_overflow_forcing,
            "mirrored_left_overflow_formal_forcing": joint_clock.mirrored_left_overflow_forcing,
            "physical_forcing_channel": "right_physical_forcing",
            "source_bound": True,
        }
    if joint_clock is not None:
        result["composed_signed_action"] = {
            "macro_steps": joint_clock.steps,
            "multiplier": joint_clock.multiplier,
            "forcing": joint_clock.right_forcing,
            "source_residue": defects[0].input_modulus,
            "target_residue": defects[-1].output_modulus,
        }
    return result


def defect_clock_cli_packet(
    term: object,
    *,
    digits: int = 8,
    samples: int = 24,
    stride: int = 1,
    max_lag: int = 16,
    prefix_horizon: int = 128,
) -> dict[str, object]:
    """Defect-only CLI path: avoid the all-word endpoint and center scan."""
    from .power import DoubleReverseTerm

    if not isinstance(term, DoubleReverseTerm):
        raise TypeError("defect-clock request requires an exact 2rev10 term")
    term.check_open()
    if type(prefix_horizon) is not int or not 1 <= prefix_horizon <= 512:
        raise ValueError("invalid defect source prefix")
    if term.generation < 4 or term.seed == 0:
        return {
            "status": "unavailable",
            "reason": "a nonzero source and at least two complete T-squared steps are required",
            "infinite_period_certified": False,
        }
    try:
        term.temporal_engine.admit_extended_prefix(
            min(prefix_horizon, term.generation - 2)
        )
        _entry, source = term.prepare_bank_source(
            max_prefix=min(prefix_horizon, term.generation - 2)
        )
    except UncertifiedPointedStencilError as exc:
        return {
            "status": "unavailable",
            "reason": str(exc),
            "infinite_period_certified": False,
        }
    packet = source_bound_defect_period_packet(
        source,
        digits=digits,
        samples=samples,
        stride=stride,
        max_lag=max_lag,
    )
    return {
        "seed": term.seed,
        "target_generation": term.generation,
        "source_prefix_generation": source.physical_prefix,
        **packet,
    }
