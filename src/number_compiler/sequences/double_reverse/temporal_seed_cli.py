"""CLI-owned, seed-agnostic exact powered 2rev10 endpoint and finite period scan.

The certified full-digit SLP word is the authority, not a mod-99 residue or
an assumed future center driver.  Four-generation center windows are demanded
from the *same pointed source* by exact guarded spacetime cones.  A matching
finite sample never authorizes an infinite-period or repeated-source shortcut.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, NotRequired, TypedDict

from .temporal_center_cyclotomic import certified_cyclotomic_center_driver
from .temporal_depth_transfer_matrix import (
    SourceConditionedDepthWindowUnavailable,
    source_conditioned_depth_window_packet,
)
from .temporal_hashlife import growth_ports
from .temporal_hashlife_types import UncertifiedPointedStencilError
from .temporal_residue_quotient import (
    certified_residue_action,
    decimal_residues_from_slp,
)
from .temporal_seed_morphism import (
    certified_seed_orbit_morphism,
    word_fiber_from_root,
)

if TYPE_CHECKING:
    from .power import DoubleReverseTerm
    from .source_bound_bank import PointedBankSource
    from .temporal_seed_morphism import CertifiedSeedOrbitMorphism


class _CenterTraceRow(TypedDict):
    generation: int
    phase: int
    width: int
    residue99: int
    residue198: int
    center: str


class _FiniteCenterScan(TypedDict):
    status: str
    physical_stride: int
    requested_samples: int
    actual_samples: int
    max_depth: int
    trace: list[_CenterTraceRow]
    layers: list[dict[str, object]]
    scope: str
    drivers: NotRequired[dict[str, object]]


def _finite_center_scan(
    source: PointedBankSource,
    *,
    samples: int,
    stride: int,
    depth: int,
    max_lag: int,
    include_drivers: bool,
) -> _FiniteCenterScan:
    """Demand exact center windows, never whole intermediate integer words.

    Samples are a fixed four-physical-tick clock, ending at the requested
    generation.  Each depth is the full width-(2d+2) even-center or width-
    (2d+1) odd-center window. The finite lag tests do not assume stationarity.
    """
    source.validate(require_issued_cursor=True)
    count = min(samples, 1 + source.f_steps // (2 * stride))
    start_f = source.f_steps - 2 * stride * (count - 1)
    indexes = tuple(start_f + 2 * stride * j for j in range(count))
    source_mod99, source_mod198 = decimal_residues_from_slp(
        source.arena,
        source.root,
        ledger=source.ledger,
        scratch_owner=source.scratch_owner,
    )
    trace: list[_CenterTraceRow] = []
    columns: list[list[str]] = [[] for _ in range(depth + 1)]
    for f in indexes:
        width = source.width_in + sum(growth_ports(source.phase, f))
        center_width = 2 if width % 2 == 0 else 1
        position = (width - center_width) // 2
        phase = (source.phase + 2 * f) % 4
        residues = certified_residue_action(
            phase=source.phase,
            width=source.width_in,
            duration=2 * f,
            source_mod99=source_mod99,
            source_mod198=source_mod198,
        )
        if residues.width_out != width:
            raise AssertionError("center sample width disagrees with cyclotomic clock")
        # Every requested layer is nested around the same center. One bounded
        # row shares its exact source halo across the complete sample.
        valid = min(depth, position, width - position - center_width)
        start = position - valid
        count_digits = center_width + 2 * valid
        sampled = source.engine.pointed_window(
            source.root, f, source.phase, start, count_digits
        )
        for d in range(depth + 1):
            if d > valid:
                columns[d].append("")  # missing window is NOT a return match
            else:
                begin = valid - d
                end = valid + center_width + d
                columns[d].append("".join(map(str, sampled[begin:end])))
        trace.append(
            {
                "generation": source.physical_prefix + 2 * f,
                "phase": phase,
                "width": width,
                "residue99": residues.target_mod99,
                "residue198": residues.target_mod198,
                "center": columns[0][-1],
            }
        )

    layers: list[dict[str, object]] = []
    for d, values in enumerate(columns):
        possible_lags = range(1, min(max_lag, count - 1) + 1)
        # A finite sampled-window period is exact only on the displayed
        # window; it says NOTHING about either future letters or the orbit.
        window_lags = [
            lag
            for lag in possible_lags
            if all(
                values[j] and values[j - lag] and values[j] == values[j - lag]
                for j in range(lag, count)
            )
        ]
        final_lags = [
            lag
            for lag in possible_lags
            if values[-1] and values[-1] == values[-lag - 1]
        ]
        last_seen: dict[str, int] = {}
        repeats: list[dict[str, int]] = []
        for j, word in enumerate(values):
            if not word:
                continue
            if word in last_seen:
                earlier = last_seen[word]
                repeats.append(
                    {
                        "generation": int(trace[j]["generation"]),
                        "previous_generation": int(trace[earlier]["generation"]),
                        "physical_gap": int(trace[j]["generation"])
                        - int(trace[earlier]["generation"]),
                        "sample_gap": j - earlier,
                    }
                )
            last_seen[word] = j
        layers.append(
            {
                "depth": d,
                "observed_digits": values,
                "finite_window_period_lags": window_lags,
                "final_sample_matching_lags": final_lags,
                "consecutive_observed_return_gaps": repeats,
                "complete_windows": sum(bool(v) for v in values),
            }
        )

    packet: _FiniteCenterScan = {
        "status": "available",
        "physical_stride": 4 * stride,
        "requested_samples": samples,
        "actual_samples": count,
        "max_depth": depth,
        "trace": trace,
        "layers": layers,
        "scope": "exact finite source-cone observations; no all-depth period claim",
    }
    if include_drivers:
        if (
            stride != 1
            or count < 2
            or trace[0]["phase"] != 0
            or int(trace[0]["width"]) % 2
        ):
            packet["drivers"] = {
                "status": "unavailable",
                "reason": "four-tick center driver needs consecutive phase-0 even-width blocks",
            }
        else:
            letters: list[dict[str, object]] = []
            for i in range(count - 1):
                witness = certified_cyclotomic_center_driver(
                    source, start_f_steps=indexes[i]
                )
                witness.validate_source_authority()
                if (
                    "".join(map(str, witness.initial_pair)) != columns[0][i]
                    or "".join(map(str, witness.next_pair)) != columns[0][i + 1]
                ):
                    raise AssertionError(
                        "source center driver diverged from period scan"
                    )
                letters.append(
                    {
                        "generation": int(trace[i]["generation"]),
                        "incoming_carries": [
                            witness.driver.left_1,
                            witness.driver.left_2,
                            witness.driver.left_3,
                        ],
                        "right_f5": witness.driver.right_f5,
                        "odd_center_digits": list(witness.odd_centers),
                        "from_center": columns[0][i],
                        "to_center": columns[0][i + 1],
                    }
                )
            packet["drivers"] = {"status": "available", "letters": letters}
    return packet


def seed_morphism_cli_packet(
    term: DoubleReverseTerm,
    *,
    period_samples: int = 0,
    period_stride: int = 1,
    period_depth: int = 2,
    period_max_lag: int = 16,
    period_drivers: bool = False,
    depth_matrix: bool = False,
    prefix_horizon: int = 128,
) -> dict[str, object]:
    """Run source-verified full-word powering on any CLI seed when admitted.

    For unrecognized seed cylinders, existing exact chronological semantics
    are preserved, explicitly labeled as a non-powered fallback.  Seed zero
    has a separate exact fixed-point shortcut. No missing certification is
    silently replaced by an empirical width/driver motif.
    """
    term._check_open()
    if type(prefix_horizon) is not int or not 1 <= prefix_horizon <= 512:
        raise ValueError("temporal prefix horizon outside the allowed range")
    if type(period_samples) is not int or not 0 <= period_samples <= 128:
        raise ValueError("period samples outside the allowed range")
    if type(period_stride) is not int or not 1 <= period_stride <= 4096:
        raise ValueError("period stride outside the allowed range")
    if type(period_depth) is not int or not 0 <= period_depth <= 8:
        raise ValueError("period depth outside the allowed range")
    if type(period_max_lag) is not int or not 1 <= period_max_lag <= 128:
        raise ValueError("period maximum lag outside the allowed range")
    if type(period_drivers) is not bool:
        raise TypeError("period driver demand must be Boolean")
    if type(depth_matrix) is not bool:
        raise TypeError("depth matrix demand must be Boolean")
    if depth_matrix and period_depth < 1:
        raise ValueError("a depth matrix needs period depth of at least one pair")
    if period_samples * (2 * period_depth + 1) > 2048:
        raise ValueError("temporal period sampling exceeds its work budget")
    if period_drivers and period_samples > 32:
        raise ValueError("source-authenticated driver word exceeds 32 blocks")

    source: PointedBankSource | None = None
    morphism: CertifiedSeedOrbitMorphism | None = None
    reason: str | None = None
    if term.seed == 0:
        root = term._source.root
        mode = "exact_fixed_zero"
    elif term.generation >= 2:
        try:
            term._adapter.temporal_hashlife.admit_extended_prefix(
                min(prefix_horizon, term.generation - 2)
            )
            _entry, source = term._prepare_bank_source(
                max_prefix=min(prefix_horizon, term.generation - 2)
            )
        except UncertifiedPointedStencilError as exc:
            reason = str(exc)
            root = term._root()
            mode = "exact_scheduler_fallback"
        else:
            morphism = certified_seed_orbit_morphism(source, steps=source.f_steps)
            morphism.validate_source_authority()
            root = morphism.last.root
            mode = "source_certified_hashlife_dyadic"
    else:
        root = term._root()
        mode = "exact_short_prefix"

    if source is None:
        last = word_fiber_from_root(
            term._arena, term.resource_ledger, term._scratch_owner, root
        )
        power: dict[str, object] = {
            "mode": mode,
            "source_prefix_generation": term.generation,
            "physical_powered_generations": 0,
            "dyadic_t_squared_chunks": [],
            "border_phase": None,
            "reason": reason,
            "scheduler_hashlife_powered_t_squared_steps": term.metrics().get(
                "double_reverse_hashlife_powered_t2_steps", 0
            ),
        }
    else:
        if morphism is None:
            raise AssertionError("certified source is missing its orbit morphism")
        last = morphism.last
        power = {
            "mode": mode,
            "source_prefix_generation": source.physical_prefix,
            "physical_powered_generations": 2 * source.f_steps,
            "dyadic_t_squared_chunks": [
                1 << bit
                for bit in range(source.f_steps.bit_length() - 1, -1, -1)
                if source.f_steps & (1 << bit)
            ],
            "border_phase": source.phase,
            "reason": None,
        }
    packet: dict[str, object] = {
        "seed": term.seed,
        "target_generation": term.generation,
        "power": power,
        "endpoint": {
            "width": last.width,
            "center": "".join(map(str, last.center)),
            "center_band_moore": last.center_band_moore,
            "mod99": last.residue99,
            "mod198": last.residue198,
            "punctured_exterior_mod99": last.exterior99,
            "punctured_exterior_mod198": last.exterior198,
            "full_digit_slp": True,
        },
        "all_depth_period_claim": False,
    }
    if source is not None:
        if morphism is None:
            raise AssertionError("certified source is missing its orbit morphism")
        if last.residue99 != morphism.residue_action.target_mod99 or (
            last.residue198 != morphism.residue_action.target_mod198
        ):
            raise AssertionError("CLI global ring disagrees with exact word endpoint")
        packet["global_four_block_order"] = morphism.global_four_block_order
        if period_samples:
            scan = _finite_center_scan(
                source,
                samples=period_samples,
                stride=period_stride,
                depth=period_depth,
                max_lag=period_max_lag,
                include_drivers=period_drivers,
            )
            if int(scan["trace"][-1]["generation"]) != term.generation:
                raise AssertionError(
                    "finite period scan did not reach target generation"
                )
            if (
                scan["trace"][-1]["center"] != "".join(map(str, last.center))
                or scan["trace"][-1]["residue99"] != last.residue99
                or scan["trace"][-1]["residue198"] != last.residue198
            ):
                raise AssertionError(
                    "independent temporal cones disagree with all-word power"
                )
            packet["period_observations"] = scan
    elif period_samples:
        packet["period_observations"] = {
            "status": "unavailable",
            "reason": (
                "the actual seed has no certified four-phase source cylinder "
                "within the admitted prefix; no future period is inferred"
            ),
        }
    if depth_matrix:
        if source is None or source.f_steps < 1:
            packet["conditional_depth_matrix"] = {
                "status": "unavailable",
                "reason": reason or "no prepared T-squared source horizon is available",
                "infinite_period_certified": False,
            }
        else:
            matrix_steps = min(4, source.f_steps)
            matrix_start = source.f_steps - matrix_steps
            try:
                matrix_packet = source_conditioned_depth_window_packet(
                    source,
                    outer_pairs=period_depth,
                    start_f_steps=matrix_start,
                    f_steps=matrix_steps,
                )
            except UncertifiedPointedStencilError as exc:
                packet["conditional_depth_matrix"] = {
                    "status": "unavailable",
                    "reason": str(exc),
                    "infinite_period_certified": False,
                }
            except SourceConditionedDepthWindowUnavailable as exc:
                packet["conditional_depth_matrix"] = {
                    "status": "unavailable",
                    "reason": str(exc),
                    "infinite_period_certified": False,
                }
            else:
                packet["conditional_depth_matrix"] = matrix_packet
    return packet


__all__ = ["seed_morphism_cli_packet"]
