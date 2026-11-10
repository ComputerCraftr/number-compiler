"""CLI-owned, seed-agnostic exact powered 2rev10 endpoint and finite period scan.

The certified full-digit SLP word is the authority, not a mod-99 residue or
an assumed future center driver.  Four-generation center windows are demanded
from the *same pointed source* by exact guarded spacetime cones.  A matching
finite sample never authorizes an infinite-period or repeated-source shortcut.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, NotRequired, TypedDict

from number_compiler.api.json_output import (
    is_object_sequence,
    is_string_object_mapping,
)

from .temporal_center_power import (
    CenterForcingPower,
    centered_half_combination_mod11,
)
from .temporal_center_selector import CenterDriver, CenterReturn, center_return
from .temporal_depth_transfer_matrix import (
    SourceConditionedDepthWindowUnavailable,
    source_conditioned_depth_window_packet,
)
from .temporal_hashlife import growth_ports
from .temporal_hashlife_types import UncertifiedPointedStencilError
from .temporal_residue_quotient import (
    certified_residue_action,
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
    centered_half_mode: str
    centered_half_mod11: int


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
    spatial_pascal_moments: NotRequired[dict[str, object]]
    spatial_mod70_cyclotomic: NotRequired[dict[str, object]]


def _finite_center_scan(
    source: PointedBankSource,
    *,
    samples: int,
    stride: int,
    depth: int,
    max_lag: int,
    include_drivers: bool,
    source_mod99: int,
    source_mod198: int,
) -> _FiniteCenterScan:
    """Reserve the finite observer's complete scratch shape before reading it."""
    source.validate(require_issued_cursor=True)
    count = min(samples, 1 + source.f_steps // (2 * stride))
    if count < 1 or depth < 0:
        raise ValueError("finite center scan needs samples and a nonnegative depth")
    word_digits = (depth + 1) * (depth + 2)
    driver_blocks = count - 1 if include_drivers and stride == 1 and count > 1 else 0
    scratch_entries = (
        count * (2 * (depth + 1) + 5) + 4 * driver_blocks + 3 * (depth + 1)
    )
    scratch_nodes = count * (word_digits + 8 * (depth + 1) + 40) + 32 * driver_blocks
    with source.ledger.reservation(
        source.scratch_owner, entries=scratch_entries, nodes=scratch_nodes
    ):
        return _finite_center_scan_reserved(
            source,
            samples=samples,
            stride=stride,
            depth=depth,
            max_lag=max_lag,
            include_drivers=include_drivers,
            source_mod99=source_mod99,
            source_mod198=source_mod198,
            count=count,
        )


def _finite_center_driver_from_halos(
    before_width: int,
    before_halo: tuple[int, int, int, int],
    middle_halo: tuple[int, int, int, int],
    before_pair: tuple[int, int],
    after_pair: tuple[int, int],
) -> CenterReturn:
    """Reconstruct one exact four-tick center action from two source halos.

    The first and final even frames are requested period samples. The one
    intervening odd-width frame supplies the middle center and adjacent carry
    ports. The other two odd frames follow directly from the reflected-double
    digit rule, so no second center-driver publisher or residue fold is needed.
    """
    if before_width < 4 or before_width % 2:
        raise ValueError("mirrored center seam needs an even source width >= 4")
    center = before_width // 2

    def odd_at(
        halo: tuple[int, int, int, int], width: int, growth: int, at: int
    ) -> int:
        if growth and at == 0:
            return 1
        source_index = width - 1 - (at - growth)
        offset = source_index - (center - 2)
        if not 0 <= offset < len(halo):
            raise AssertionError("mirrored center halo omitted an input port")
        carry = int(source_index > 0 and halo[offset - 1] >= 5)
        return (2 * halo[offset] + carry) % 10

    first_left = odd_at(before_halo, before_width, 1, center - 1)
    first_center = odd_at(before_halo, before_width, 1, center)
    middle_center = middle_halo[2]
    third_left = odd_at(middle_halo, before_width + 1, 0, center - 1)
    third_center = odd_at(middle_halo, before_width + 1, 0, center)
    third_right = odd_at(middle_halo, before_width + 1, 0, center + 1)
    driver = CenterDriver(
        int(first_left >= 5),
        int(middle_halo[1] >= 5),
        int(third_left >= 5),
        third_right % 5,
    )
    returned = center_return(before_pair, driver)
    if returned.odd != (first_center, middle_center, third_center):
        raise AssertionError("single-pass center carries disagree with odd centers")
    if returned.next_pair != after_pair:
        raise AssertionError("single-pass center carries disagree with next pair")
    return returned


def _finite_center_scan_reserved(
    source: PointedBankSource,
    *,
    samples: int,
    stride: int,
    depth: int,
    max_lag: int,
    include_drivers: bool,
    source_mod99: int,
    source_mod198: int,
    count: int,
) -> _FiniteCenterScan:
    """Demand exact center windows, never whole intermediate integer words.

    Samples are a fixed four-physical-tick clock, ending at the requested
    generation.  Each depth is the full width-(2d+2) even-center or width-
    (2d+1) odd-center window. The finite lag tests do not assume stationarity.
    """
    start_f = source.f_steps - 2 * stride * (count - 1)
    indexes = tuple(start_f + 2 * stride * j for j in range(count))
    trace: list[_CenterTraceRow] = []
    columns: list[list[str]] = [[] for _ in range(depth + 1)]
    first_width = source.width_in + sum(growth_ports(source.phase, start_f))
    driver_available = (
        include_drivers
        and stride == 1
        and count >= 2
        and (source.phase + 2 * start_f) % 4 == 0
        and first_width >= 4
        and first_width % 2 == 0
    )
    published_letters: list[dict[str, object]] = []
    composed_power: CenterForcingPower | None = None
    prior_halo: tuple[int, int, int, int] | None = None
    prior_pair: tuple[int, int] | None = None
    prior_width: int | None = None
    for sample_index, f in enumerate(indexes):
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
        read_depth = max(valid, int(driver_available))
        start = position - read_depth
        count_digits = center_width + 2 * read_depth
        sampled = source.engine.pointed_window(
            source.root, f, source.phase, start, count_digits
        )
        for d in range(depth + 1):
            if d > valid:
                columns[d].append("")  # missing window is NOT a return match
            else:
                begin = read_depth - d
                end = read_depth + center_width + d
                columns[d].append("".join(map(str, sampled[begin:end])))
        half_mode, half_residue = centered_half_combination_mod11(
            width,
            tuple(map(int, columns[0][-1])),
            residues.target_mod99,
        )
        trace.append(
            {
                "generation": source.physical_prefix + 2 * f,
                "phase": phase,
                "width": width,
                "residue99": residues.target_mod99,
                "residue198": residues.target_mod198,
                "center": columns[0][-1],
                "centered_half_mode": half_mode,
                "centered_half_mod11": half_residue,
            }
        )
        if driver_available:
            if read_depth < 1 or center_width != 2:
                raise AssertionError("center scan omitted its exact four-digit halo")
            halo = (
                sampled[read_depth - 1],
                sampled[read_depth],
                sampled[read_depth + 1],
                sampled[read_depth + 2],
            )
            pair_digits = tuple(map(int, columns[0][-1]))
            if len(pair_digits) != 2:
                raise AssertionError(
                    "even center sample did not produce an ordered pair"
                )
            pair = (pair_digits[0], pair_digits[1])
            if sample_index:
                if prior_halo is None or prior_pair is None or prior_width is None:
                    raise AssertionError("center scan lost its previous source halo")
                old_center = prior_width // 2
                middle_values = source.engine.pointed_window(
                    source.root,
                    f - 1,
                    source.phase,
                    old_center - 2,
                    4,
                )
                middle_halo = (
                    middle_values[0],
                    middle_values[1],
                    middle_values[2],
                    middle_values[3],
                )
                returned = _finite_center_driver_from_halos(
                    prior_width, prior_halo, middle_halo, prior_pair, pair
                )
                block_power = CenterForcingPower.from_return(returned)
                composed_power = (
                    block_power
                    if composed_power is None
                    else composed_power.then(block_power)
                )
                published_letters.append(
                    {
                        "generation": int(trace[-2]["generation"]),
                        "incoming_carries": [
                            returned.driver.left_1,
                            returned.driver.left_2,
                            returned.driver.left_3,
                        ],
                        "right_f5": returned.driver.right_f5,
                        "right_center_forcing": block_power.weighted_mod10,
                        "odd_center_digits": list(returned.odd),
                        "from_center": trace[-2]["center"],
                        "to_center": trace[-1]["center"],
                    }
                )
            prior_halo = halo
            prior_pair = pair
            prior_width = width

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
        if not driver_available:
            packet["drivers"] = {
                "status": "unavailable",
                "reason": (
                    "four-tick center driver needs consecutive phase-0 even-width "
                    "blocks of width at least four"
                ),
            }
        else:
            if composed_power is None or len(published_letters) != count - 1:
                raise AssertionError("finite center driver composition is incomplete")
            powered = CenterForcingPower.from_endpoints(
                int(columns[0][0][-1]),
                int(columns[0][-1][-1]),
                count - 1,
            )
            if composed_power != powered:
                raise AssertionError(
                    "source driver forcing disagrees with powered center"
                )
            half_multiplier = pow(16, powered.blocks, 11)
            half_innovation = (
                int(trace[-1]["centered_half_mod11"])
                - half_multiplier * int(trace[0]["centered_half_mod11"])
            ) % 11
            if (
                trace[0]["centered_half_mode"] != trace[-1]["centered_half_mode"]
                or trace[0]["centered_half_mode"] == "difference"
                and half_innovation
            ):
                raise AssertionError(
                    "centered half clock disagrees with global 99/198 power"
                )
            packet["drivers"] = {
                "status": "available",
                "letters": published_letters,
                "center_forcing_power": {
                    "scope": "finite source-authenticated endpoint action",
                    "blocks": powered.blocks,
                    "weighted_mod10": powered.weighted_mod10,
                    "forcing_sum_mod5": powered.sum_mod5,
                    "last_forcing_parity": powered.last_forcing_parity,
                    "right_center_return": powered.harmonic_return,
                    "complete_center_pair_return": columns[0][0] == columns[0][-1],
                    "centered_half_mod11": {
                        "mode": trace[0]["centered_half_mode"],
                        "source": trace[0]["centered_half_mod11"],
                        "target": trace[-1]["centered_half_mod11"],
                        "multiplier": half_multiplier,
                        "center_forcing": half_innovation,
                    },
                },
            }
    return packet


def _pascal_moments_packet(
    morphism: CertifiedSeedOrbitMorphism,
    source: PointedBankSource,
) -> dict[str, object] | None:
    """Serialize demanded exact spatial bands under the source morphism."""
    morphism.validate_source_authority()
    first = morphism.first
    last = morphism.last
    if not first.pascal_levels:
        if last.pascal_levels:
            raise AssertionError("target Pascal demand lacks a source demand")
        return None
    if (
        first.pascal_levels != last.pascal_levels
        or first.pascal_order != last.pascal_order
        or len(first.pascal_bands) != len(last.pascal_bands)
    ):
        raise AssertionError("source/target Pascal summaries have different demands")
    bands: list[dict[str, object]] = []
    for (source_level, source_moments), (target_level, target_moments) in zip(
        first.pascal_bands, last.pascal_bands, strict=True
    ):
        if source_level != target_level:
            raise AssertionError("source/target Pascal band levels differ")
        bands.append(
            {
                "level": source_level,
                "source_length": source_moments.length,
                "target_length": target_moments.length,
                "source_digit_moments": list(source_moments.digit_moments),
                "target_digit_moments": list(target_moments.digit_moments),
                "source_high_marker_moments": list(source_moments.marker_moments),
                "target_high_marker_moments": list(target_moments.marker_moments),
                "source_endpoint_markers": [
                    source_moments.first_marker,
                    source_moments.last_marker,
                ],
                "target_endpoint_markers": [
                    target_moments.first_marker,
                    target_moments.last_marker,
                ],
            }
        )
    return {
        "status": "available",
        "source_generation": source.physical_prefix + 2 * morphism.start_f_steps,
        "target_generation": source.physical_prefix
        + 2 * (morphism.start_f_steps + morphism.steps),
        "orientation": "most-significant-digit-first",
        "modulus": 11,
        "order": first.pascal_order,
        "marker": "digit-at-least-five",
        "bands": bands,
        "scope": (
            "finite exact source-issued SLP bands; no temporal repetition authority"
        ),
    }


def _spatial_mod70_packet(
    morphism: CertifiedSeedOrbitMorphism,
    source: PointedBankSource,
) -> dict[str, object]:
    """Serialize demanded source/target spatial factors from their shared fold."""
    authority = morphism.validate_source_authority()
    source.validate(require_issued_cursor=source.f_steps > 0)
    if (
        authority.arena is not source.arena
        or authority.root != source.root
        or authority.source_generation != source.physical_prefix
        or morphism.source_root != source.root
        or morphism.start_f_steps != 0
        or morphism.first.root != source.root
        or morphism.first.mod70 is None
        or morphism.last.mod70 is None
    ):
        raise ValueError("mod-70 projection lacks the demanded issued source fold")
    source_summary = morphism.first.mod70
    target_summary = morphism.last.mod70
    if len(morphism.first.mod70_bands) != len(morphism.last.mod70_bands):
        raise AssertionError("source and target mod-70 bands have different demands")
    bands: list[dict[str, object]] = []
    for (source_level, source_band), (target_level, target_band) in zip(
        morphism.first.mod70_bands,
        morphism.last.mod70_bands,
        strict=True,
    ):
        if source_level != target_level:
            raise AssertionError("source and target mod-70 band levels differ")
        bands.append(
            {
                "level": source_level,
                "source": source_band.packet(),
                "target": target_band.packet(),
                "scope": "finite spatial interval; no exterior halo authority",
            }
        )
    result: dict[str, object] = {
        "source_generation": source.physical_prefix,
        "target_generation": source.physical_prefix + 2 * morphism.steps,
        "orientation": "most-significant-decimal-digit-first",
        "source": source_summary.packet(),
        "target": target_summary.packet(),
        "bands": bands,
        "scope": (
            "finite source-issued word projections; spatial factors do not "
            "establish a temporal period"
        ),
    }
    if source_summary.suffix_digits[-1] == 0:
        result["source_t_squared_affine_mod70"] = {
            "status": "unavailable",
            "reason": "source ends in zero; exact width-normalizing fallback is required",
        }
        return result
    affine = morphism.source_t_squared_mod70_affine()
    projected_t2 = affine.apply(
        source_summary.word_mod70,
        multiply=lambda left, right: left * right % 70,
        add=lambda left, right: (left + right) % 70,
    )
    if morphism.steps == 1 and projected_t2 != target_summary.word_mod70:
        raise AssertionError("mod-70 affine projection disagrees with exact T² root")
    result["source_t_squared_affine_mod70"] = {
        "status": "available",
        "physical_ticks": 2,
        "source_generation": source.physical_prefix,
        "target_generation": source.physical_prefix + 2,
        "multiplier": affine.multiplier,
        "addend": affine.addend,
        "source_mod70": source_summary.word_mod70,
        "projected_t_squared_mod70": projected_t2,
        "compared_with_exact_endpoint": morphism.steps == 1,
        "scope": "one authenticated canonical whole-word source only",
    }
    return result


def seed_morphism_cli_packet(
    term: DoubleReverseTerm,
    *,
    period_samples: int = 0,
    defect_digits: int = 0,
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
    term.check_open()
    if type(prefix_horizon) is not int or not 1 <= prefix_horizon <= 512:
        raise ValueError("temporal prefix horizon outside the allowed range")
    if type(period_samples) is not int or not 0 <= period_samples <= 128:
        raise ValueError("period samples outside the allowed range")
    if type(defect_digits) is not int or not 0 <= defect_digits <= 96:
        raise ValueError("defect suffix width outside the allowed range")
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
    if period_drivers and defect_digits:
        raise ValueError(
            "explicit center drivers and defect-only period view are separate queries"
        )

    source: PointedBankSource | None = None
    morphism: CertifiedSeedOrbitMorphism | None = None
    reason: str | None = None
    if term.seed == 0:
        root = term.source_root
        mode = "exact_fixed_zero"
    elif term.generation >= 2:
        # A caller may already have issued the exact prefix cursor and its
        # powered temporal suffix. Preserve that source-owned route: asking
        # the general endpoint scheduler to rebuild the same suffix would
        # re-enter the scalar source adapter and discard authenticated work.
        # A fresh cold observer still publishes the complete scheduler image
        # once, which is the fast path used by the installed CLI.
        prior_prefix = term.temporal_engine.source_prefix()
        try:
            term.temporal_engine.admit_extended_prefix(
                min(prefix_horizon, term.generation - 2)
            )
            _entry, source = term.prepare_bank_source(
                max_prefix=min(prefix_horizon, term.generation - 2)
            )
        except UncertifiedPointedStencilError as exc:
            reason = str(exc)
            root = term.endpoint_root()
            mode = "exact_scheduler_fallback"
        else:
            completed_term = term if term.published_image is not None else None
            if completed_term is None and prior_prefix is None:
                term.prepare_endpoint()
                completed_term = term
            pascal_levels = (
                tuple(range(1, period_depth + 1))
                if period_samples and period_drivers
                else ()
            )
            mod70_projection = period_samples > 0 and period_drivers
            morphism = certified_seed_orbit_morphism(
                source,
                steps=source.f_steps,
                completed_term=completed_term,
                pascal_levels=pascal_levels,
                pascal_order=1,
                mod70_projection=mod70_projection,
            )
            morphism.validate_source_authority()
            root = morphism.last.root
            mode = "source_certified_hashlife_dyadic"
    else:
        root = term.endpoint_root()
        mode = "exact_short_prefix"

    if source is None:
        last = word_fiber_from_root(
            term.source_arena, term.resource_ledger, term.scratch_owner, root
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
        # The complete-word source morphism already owns the residue action.
        # Project the same action into the two Laurent accumulation channels;
        # no second source fold or chronology beyond the finite entry prefix.
        from .temporal_laurent_return import source_laurent_accumulator_packet

        packet["normalized_laurent_accumulator"] = source_laurent_accumulator_packet(
            term,
            source.physical_prefix,
            morphism.residue_action,
            authenticated_morphism=morphism,
        )
        if period_samples:
            if defect_digits:
                # The same source-issued alternating-frame transducer powers
                # the defect observer AND the source-morphism period view.
                # Compare the final macro's output with the independently
                # completed all-word Hashlife endpoint, without a new cone.
                from number_compiler.arithmetic.automata.slp_walks import symbol_at

                from .temporal_defect_period import source_bound_defect_period_packet
                from .temporal_defect_quotient import defect_modulus

                scan_defect = source_bound_defect_period_packet(
                    source,
                    digits=defect_digits,
                    samples=period_samples,
                    stride=period_stride,
                    max_lag=period_max_lag,
                )
                if scan_defect["status"] == "available":
                    rows = scan_defect["rows"]
                    if not is_object_sequence(rows) or not rows:
                        raise AssertionError(
                            "source-period defect lost its temporal rows"
                        )
                    final_row = rows[-1]
                    if not is_string_object_mapping(final_row):
                        raise AssertionError("invalid defect terminal row")
                    generation = final_row.get("generation")
                    target_modulus_residue = final_row.get("target_mod_2x10w")
                    if (
                        type(generation) is not int
                        or type(target_modulus_residue) is not int
                    ):
                        raise AssertionError("invalid exact defect terminal integers")
                    final_generation = generation + 4
                    if final_generation != term.generation:
                        raise AssertionError(
                            "defect period sample misses the requested endpoint"
                        )
                    take = min(last.width, defect_digits + 1)
                    residue = 0
                    for pos in range(last.width - take, last.width):
                        residue = 10 * residue + symbol_at(source.arena, last.root, pos)
                    if (
                        residue % defect_modulus(defect_digits)
                        != target_modulus_residue
                    ):
                        raise AssertionError(
                            "source-certified defect disagrees with full-word endpoint"
                        )
                    scan_defect["full_endpoint_suffix_verified"] = True
                packet["period_observations"] = scan_defect
            else:
                scan = _finite_center_scan(
                    source,
                    samples=period_samples,
                    stride=period_stride,
                    depth=period_depth,
                    max_lag=period_max_lag,
                    include_drivers=period_drivers,
                    source_mod99=morphism.first.residue99,
                    source_mod198=morphism.first.residue198,
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
                spatial_pascal = _pascal_moments_packet(morphism, source)
                if spatial_pascal is not None:
                    scan["spatial_pascal_moments"] = spatial_pascal
                if period_drivers and morphism.first.mod70 is not None:
                    scan["spatial_mod70_cyclotomic"] = _spatial_mod70_packet(
                        morphism, source
                    )
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
