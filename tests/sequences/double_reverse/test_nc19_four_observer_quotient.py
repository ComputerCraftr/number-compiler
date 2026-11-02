"""Independent checks of the four-output carry quotient and its periods."""

from __future__ import annotations

from collections.abc import Sequence
from random import Random

from number_compiler.sequences.double_reverse.temporal_defect_quotient import (
    DefectAffineClock,
    defect_and_successor_from_normalized_suffix,
    defect_from_normalized_suffix,
)
from number_compiler.sequences.double_reverse.temporal_four_observer import (
    FourObserverAffineClock,
    FourObserverEmission,
    projected_period_profiles,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import edge_phase
from tests.sequences.double_reverse.packet_helpers import object_list, object_mapping


def _reverse_double(x: int) -> int:
    return 2 * int(str(x)[::-1])


def _mirrored_half_step(x: int) -> int:
    return int(str(_reverse_double(x))[::-1])


def _even_orbit(seed: int, start: int, count: int) -> list[int]:
    x = seed
    for _ in range(start):
        x = _reverse_double(x)
    result: list[int] = []
    for _ in range(count):
        result.append(x)
        for _ in range(4):
            x = _reverse_double(x)
    return result


def _naive_tail_lags(
    values: Sequence[object], max_lag: int
) -> tuple[list[int], dict[str, int] | None]:
    """Small independent exhaustive oracle for the optimized suffix scan."""
    count = len(values)
    complete = [
        lag
        for lag in range(1, min(max_lag, count - 1) + 1)
        if all(values[index] == values[index - lag] for index in range(lag, count))
    ]
    candidates: list[dict[str, int]] = []
    for lag in range(1, min(max_lag, count // 3) + 1):
        for start in range(count):
            if count - start < 3 * lag:
                continue
            if all(
                values[index] == values[index - lag]
                for index in range(start + lag, count)
            ):
                candidates.append(
                    {
                        "observed_lag": lag,
                        "sample_start": start,
                        "samples": count - start,
                    }
                )
                break
    best = min(
        candidates,
        key=lambda item: (item["sample_start"], item["observed_lag"]),
        default=None,
    )
    return complete, best


def _period_candidate(value: object) -> dict[str, int] | None:
    try:
        record = object_mapping(value)
    except AssertionError:
        return None
    observed_lag = record.get("observed_lag")
    sample_start = record.get("sample_start")
    samples = record.get("samples")
    if (
        type(observed_lag) is not int
        or type(sample_start) is not int
        or type(samples) is not int
    ):
        return None
    return {
        "observed_lag": observed_lag,
        "sample_start": sample_start,
        "samples": samples,
    }


def _source_observation(x: int, width: int) -> FourObserverEmission:
    digits = str(x)
    phase = edge_phase(
        (int(digits[0]), int(digits[1])),
        (int(digits[-2]), int(digits[-1])),
    )
    assert phase in (0, 2)
    source = (0,) * (width + 4) + tuple(map(int, digits))
    defect = defect_from_normalized_suffix(source, width)
    return FourObserverEmission.from_source(
        defect, phase=phase, source_width=len(digits)
    )


def test_four_observer_boundary_sources_are_actual_half_step_overflows() -> None:
    for seed in (1, 168, 196):
        for x in _even_orbit(seed, 64, 25):
            observation = _source_observation(x, 12)
            x1 = _reverse_double(_reverse_double(x))
            y0 = _mirrored_half_step(x)  # H(x), even-frame notation
            y1 = _mirrored_half_step(x1)
            expected_right = (int(x % 10 >= 5), int(x1 % 10 >= 5))
            expected_left = (int(int(str(y0)[0]) >= 5), int(int(str(y1)[0]) >= 5))
            assert observation.right_overflow == expected_right
            assert observation.mirrored_left_overflow == expected_left
            assert observation.semantic_key(12) == (
                observation.phase,
                observation.right % 10**12,
                observation.left % 10**12,
                None,
            )
            for w in (1, 3, 8, 12):
                modulus = 2 * 10**w
                # Width is larger than the observer precision, hence the
                # exact repunit reference is -overflow in both orientations.
                o_r = observation.right_overflow_defects(w, factor=2)
                o_l = observation.mirrored_left_overflow_defects(w, factor=2)
                assert o_r == tuple(
                    (b * (10 ** (len(str(z)) + 1) - 1)) % modulus
                    for b, z in zip(expected_right, (x, x1), strict=True)
                )
                assert o_l == tuple(
                    (b * (10 ** (len(str(z)) + 1) - 1)) % modulus
                    for b, z in zip(expected_left, (y0, y1), strict=True)
                )


def test_joint_signed_clock_composes_and_powers_without_misadding_forcing() -> None:
    observations = [_source_observation(x, 16) for x in _even_orbit(168, 64, 40)]
    actual = FourObserverAffineClock.identity(16)
    single = DefectAffineClock.identity(16)
    for observer in observations:
        actual = actual.then(FourObserverAffineClock.from_emission(observer))
        single = single.then(DefectAffineClock.from_defect(observer.defect))
        assert (actual.multiplier, actual.right_forcing) == (
            single.multiplier,
            single.forcing,
        )
    one = FourObserverAffineClock.from_emission(observations[0])
    assert one.power(0) == FourObserverAffineClock.identity(16)
    assert one.power(2) == one.then(one)
    assert one.power(101) == one.power(50).then(one.power(51))
    assert one.power(10**14).steps == 10**14
    assert (
        actual.directional_contrast
        == (actual.right_forcing - actual.left_forcing) % actual.modulus
    )


def test_valuation_period_kernel_agrees_with_independent_naive_lag_scan() -> None:
    for seed in (1, 168, 196):
        observations = [_source_observation(x, 25) for x in _even_orbit(seed, 100, 70)]
        raw_profile: object = projected_period_profiles(observations, 30)
        profile = object_mapping(raw_profile)
        for kind in ("right", "left", "difference", "joint", "four"):
            kind_profile = object_mapping(profile[kind])
            raw_hierarchy = object_list(kind_profile["suffix_period_hierarchy"])
            for w in range(1, 26):
                active: dict[str, int] | None = None
                for row in reversed(raw_hierarchy):
                    row_mapping = object_mapping(row)
                    suffix_digits = row_mapping.get("suffix_digits")
                    if type(suffix_digits) is not int or suffix_digits > w:
                        continue
                    active = _period_candidate(
                        row_mapping.get("observed_tail_candidate")
                    )
                    break
                modulus = 10**w
                if kind == "right":
                    projected = [r.right % modulus for r in observations]
                elif kind == "left":
                    projected = [r.left % modulus for r in observations]
                elif kind == "difference":
                    projected = [r.difference % modulus for r in observations]
                elif kind == "joint":
                    projected = [
                        (r.right % modulus, r.left % modulus) for r in observations
                    ]
                else:
                    projected = [r.output_at_width(w) for r in observations]
                full, candidate = _naive_tail_lags(projected, 30)
                assert active == candidate, (seed, kind, w, active, candidate)
                if w == 25:
                    assert kind_profile["finite_window_period_lags"] == full


def test_full_successor_is_reused_without_changing_carry_columns() -> None:
    rng = Random(0x4A9)
    checked = 0
    for _ in range(1000):
        width = rng.randrange(1, 25)
        source = tuple(
            rng.randrange(0, 10) for _ in range(width + rng.randrange(4, 55))
        )
        if not source[-1]:
            continue
        try:
            defect, successor = defect_and_successor_from_normalized_suffix(
                source, width
            )
            old = defect_from_normalized_suffix(source, width)
        except ValueError:
            continue
        assert defect.combined_decimal == old.combined_decimal
        assert defect.left_defect_decimal() == old.left_defect_decimal()
        assert defect.input_modulus == old.input_modulus
        assert defect.output_modulus == old.output_modulus
        assert (
            int("".join(map(str, successor))) % (2 * 10**width) == defect.output_modulus
        )
        checked += 1
    assert checked > 300


def test_cyclic_boundary_overflow_factors_use_full_width_without_full_words() -> None:
    from number_compiler.sequences.double_reverse.temporal_four_observer import (
        CYCLIC_NEGACYCLIC_MODULI,
    )

    for seed in (1, 168, 196):
        for x in _even_orbit(seed, 72, 35):
            obs = _source_observation(x, 15)
            x1 = _reverse_double(_reverse_double(x))
            y0 = _mirrored_half_step(x)
            y1 = _mirrored_half_step(x1)
            for m in CYCLIC_NEGACYCLIC_MODULI:
                assert pow(10, 12, m) == 1
                key = obs.cyclotomic_key(m)
                r = tuple(
                    b * (10 ** (len(str(z)) + 1) - 1) % m
                    for b, z in zip(obs.right_overflow, (x, x1), strict=True)
                )
                left_residues = tuple(
                    b * (10 ** (len(str(z)) + 1) - 1) % m
                    for b, z in zip(obs.mirrored_left_overflow, (y0, y1), strict=True)
                )
                assert key == (
                    obs.phase,
                    obs.right % m,
                    obs.left % m,
                    *r,
                    *left_residues,
                )


def test_narrow_boundary_precision_is_not_silently_saturated() -> None:
    src = (0,) * 12 + (1, 6, 8)
    defect = defect_from_normalized_suffix(src, 8)
    obs = FourObserverEmission.from_source(defect, phase=0, source_width=3)
    assert obs.narrow_source_width == 3
    assert obs.semantic_key(8)[-1] == 3
    for width in (3, 4, 8):
        modulus = 2 * 10**width
        assert obs.right_overflow_defects(width, factor=2) == ((10**4 - 1) % modulus, 0)
        assert obs.mirrored_left_overflow_defects(width, factor=2) == (
            0,
            (10**5 - 1) % modulus,
        )
    # Different admitted real widths have different boundary-only residues,
    # even when the *local suffix* and border phase are otherwise equal.
    with __import__("pytest").raises(ValueError):
        FourObserverEmission.from_source(defect, phase=2, source_width=3)
