"""Deterministic profile of the bounded special-number binary quotient jump."""

from __future__ import annotations

from dataclasses import asdict, dataclass

from devtools.verification.oracles.special_binary_jump import (
    build_fermat_binary_jump,
    build_mersenne_binary_jump,
)


@dataclass(frozen=True, slots=True)
class SpecialBinaryJumpProfile:
    family: str
    parameter: int
    raw_source_states: int
    carrier_classes: int
    quotient_classes: int
    quotient_state_bits: int
    retained_transition_bits: int
    observer_offset: int
    target_horizon: int
    quotient_steps: int
    binary_compositions: int
    specialization_raw_squarings: int
    construction_raw_squarings: int
    construction_radix_shifts: int
    proof_states_examined: int
    target: bool
    construction_is_exhaustive: bool
    scalable_construction: bool


def special_binary_jump_profiles() -> tuple[SpecialBinaryJumpProfile, ...]:
    rows: list[SpecialBinaryJumpProfile] = []
    for n in (2, 3, 4):
        program = build_fermat_binary_jump(n)
        horizon = (1 << n) - 1
        application = program.apply(horizon)
        rows.append(
            SpecialBinaryJumpProfile(
                "fermat",
                n,
                program.raw_source_states,
                program.carrier_classes,
                program.quotient_classes,
                program.quotient_state_bits,
                program.retained_transition_bits,
                program.offset,
                horizon,
                application.quotient_steps,
                application.construction_compositions,
                application.specialization_raw_squarings,
                program.construction_raw_squarings,
                program.construction_radix_shifts,
                program.proof_states_examined,
                application.target,
                program.construction_is_exhaustive,
                program.scalable_construction,
            )
        )
    for p in (5, 7, 11, 13):
        program = build_mersenne_binary_jump(p)
        horizon = p - 2
        application = program.apply(horizon)
        rows.append(
            SpecialBinaryJumpProfile(
                "mersenne",
                p,
                program.raw_source_states,
                program.carrier_classes,
                program.quotient_classes,
                program.quotient_state_bits,
                program.retained_transition_bits,
                program.offset,
                horizon,
                application.quotient_steps,
                application.construction_compositions,
                application.specialization_raw_squarings,
                program.construction_raw_squarings,
                program.construction_radix_shifts,
                program.proof_states_examined,
                application.target,
                program.construction_is_exhaustive,
                program.scalable_construction,
            )
        )
    return tuple(rows)


def metrics_dict() -> dict[str, object]:
    return {"profiles": [asdict(row) for row in special_binary_jump_profiles()]}


def markdown() -> str:
    rows = special_binary_jump_profiles()
    lines = [
        "# Special-number finite quotient binary jump — v0.43.0",
        "",
        "This probe uses the same architectural rule as the reverse-add/Collatz powered stacks: first prove a finite semantic quotient, then binary-compose the quotient transition by extensional behavior. No source orbit/itinerary is retained, and specialization at the requested horizon performs no raw Pepin/Lucas--Lehmer squarings.",
        "",
        "v0.41 leaves the composite-safe jump semantics unchanged while deleting the obsolete parallel order-character compiler state. The prime-conditional group-depth theorem is now the sole special depth semantics: image ranks, Moore=image-depth, and target distance are derived algebraically, while carry histories remain downstream research witnesses only. The public composite-safe builders still prove their quotient machines by complete bounded-domain construction, so `scalable_construction` remains false. The group-depth theorem is not promoted into the builder until purity can be established without the long order test or hidden factorization.",
        "",
        "## Exact powered quotients",
        "",
        "| family | parameter | raw states | carrier classes | minimized classes | state bits | retained transition bits | observer offset | target N | quotient steps | binary compositions | specialization raw squarings |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row_1 in rows:
        lines.append(
            f"| {row_1.family} | {row_1.parameter} | {row_1.raw_source_states:,} | {row_1.carrier_classes:,} | "
            f"{row_1.quotient_classes:,} | {row_1.quotient_state_bits} | {row_1.retained_transition_bits} | "
            f"{row_1.observer_offset} | {row_1.target_horizon} | {row_1.quotient_steps} | "
            f"{row_1.binary_compositions} | {row_1.specialization_raw_squarings} |"
        )
    lines += [
        "",
        "### Mersenne carrier",
        "",
        "The carrier is the existing whole `Phi_p mod 2` digit component. It is theorem-equivalent to the exact sign quotient `x ~ -x`, because `Phi_p(2)=2^p-1` and Lucas--Lehmer satisfies `T(-x)=T(x)`. The carrier is therefore directly injectable by canonical sign representative, successor-closed, and target-separating. Exact Moore minimization gives 5/7/13 classes for prime M5/M7/M13, matching the prime-domain group-depth theorem; composite M11 instead collapses to 3 exact ring-safe classes. Binary powering acts only on this minimized transition table.",
        "",
        "### Fermat carrier",
        "",
        "The carrier is a new exact radix/cyclotomic orbit quotient. Since `2^(2^n) == -1 mod F_n`, the radix-root element 2 has exact order `2^(n+1)` modulo every `F_n`, prime or composite. Multiplication by its powers is a negacyclic digit rotation/sign action, and squaring maps every actual residue orbit to a residue orbit. The bounded builder enumerates those actual orbits rather than assuming every residue has the full group-orbit size. The current target `-1` is not separated on that carrier, so the observer is delayed by `n+1` squarings; at that point every radix phase is annihilated. Moore minimization of the delayed machine gives 2/5/12 states for F2/F3/F4.",
        "",
        "## Construction charge / remaining blocker",
        "",
        "| family | parameter | proof states examined | construction raw squarings | radix shifts | exhaustive | scalable |",
        "|---|---:|---:|---:|---:|---|---|",
    ]
    for row_2 in rows:
        lines.append(
            f"| {row_2.family} | {row_2.parameter} | {row_2.proof_states_examined:,} | "
            f"{row_2.construction_raw_squarings:,} | {row_2.construction_radix_shifts:,} | "
            f"{row_2.construction_is_exhaustive} | {row_2.scalable_construction} |"
        )
    lines += [
        "",
        "The binary jump is therefore **real after quotient construction**: target specialization performs zero recurrence squarings and `O(log N)` extensional map compositions. But quotient construction is still exhaustive in the bounded implementation. The remaining special-number theorem is now sharper: construct/inject the same small quotient from symbolic radix/cyclotomic data without enumerating the ambient carrier/raw state space.",
        "",
        "No full Hensel/CRT reconstruction, caller certificate, saved itinerary, or deferred exponent token is credited as a solution.",
        "",
    ]
    return "\n".join(lines)


__all__ = [
    "SpecialBinaryJumpProfile",
    "markdown",
    "metrics_dict",
    "special_binary_jump_profiles",
]
