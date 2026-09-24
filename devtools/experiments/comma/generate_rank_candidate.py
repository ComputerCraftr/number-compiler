"""Generate an *untrusted* Isabelle rank candidate for the comma quotient.

The output is data only.  Isabelle must independently evaluate its own
finite transition, prove every boundary macro is complete, and check the
candidate against every actual quotient child.  This script is deliberately
absent from the installed package and is never an admission oracle.
"""

from __future__ import annotations

import argparse
from math import gcd
from pathlib import Path
from tempfile import gettempdir

PERIOD = 924
STATE_COUNT = 16 * PERIOD
PADDED_COUNT = 16_384
MAX_MOVES = 4_096
DEFAULT_OUTPUT = Path(gettempdir()) / "number-compiler-comma-rank-data.thy"


def _period(leading: int, digit: int) -> int:
    divisor = gcd(leading, 10)
    length = 10 // divisor
    phase = digit % divisor
    return (
        10 * (length * phase + divisor * length * (length - 1) // 2) + length * leading
    )


def _macro_children(index: int) -> tuple[int, ...]:
    side, remainder = divmod(index, 8 * PERIOD)
    ordinal, source_residue = divmod(remainder, PERIOD)
    leading = ordinal + 2
    delta = 0
    offset = leading + 89 if side == 0 else 0
    remaining = MAX_MOVES
    while remaining:
        remaining -= 1  # The Entry -> Near transition consumes one HOL fuel unit.
        exponent_residue = (source_residue + delta) % PERIOD
        representative = (
            exponent_residue if exponent_residue >= 5 else exponent_residue + PERIOD
        )
        displacement = _period(leading, offset % 10)
        extra = int(leading < 9)
        headroom = (
            1
            + extra
            + (
                (pow(10, representative, displacement) - offset - 1 - extra)
                % displacement
            )
        )
        while remaining:
            remaining -= 1  # Every Near transition consumes the same fuel budget.
            digit = (-headroom) % 10
            if leading < 9:
                low = 10 * digit + leading
                if headroom > low + 1:
                    headroom -= low
                    continue
                if headroom == low + 1:
                    child_residue = (source_residue + delta) % PERIOD
                    near = (leading - 1) * PERIOD + child_residue
                    return near, near + 8 * PERIOD
                offset = low + 1 - headroom
                leading += 1
                break
            same = 10 * digit + 9
            cross = 10 * digit + 1
            if headroom > same:
                headroom -= same
                continue
            if headroom <= cross:
                offset = cross - headroom
                leading = 1
                delta += 1
                break
            return ()
    raise ValueError(f"macro move limit at state {index}")


def _candidate_ranks() -> list[int]:
    graph = [_macro_children(index) for index in range(STATE_COUNT)]
    rank = {index: 0 for index, children in enumerate(graph) if not children}
    while True:
        found = {
            index: 1 + max(rank[child] for child in children)
            for index, children in enumerate(graph)
            if index not in rank
            and children
            and all(child in rank for child in children)
        }
        if not found:
            break
        rank.update(found)
    codes = [rank[index] + 1 if index in rank else 0 for index in range(STATE_COUNT)]
    codes.extend([0] * (PADDED_COUNT - STATE_COUNT))
    return codes


def _render(codes: list[int]) -> str:
    if len(codes) != PADDED_COUNT:
        raise ValueError("invalid candidate length")
    parts = [
        "theory Comma_Rank_Data\n  imports Comma_Macro_Constructor\nbegin\n\n",
        "text \\<open>These numbers are a candidate rank witness generated from the\n",
        "finite boundary audit. They confer no branch authority. The checked\n",
        "instance must compare every entry with the executable HOL transition\n",
        "and prove complete macro construction before using the witness.\\<close>\n\n",
        'definition comma_rank_codes :: "nat list list list list" where\n',
        '  "comma_rank_codes = [\n',
    ]
    for top in range(4):
        parts.append("    [\n")
        for second in range(16):
            parts.append("      [\n")
            for third in range(16):
                start = ((top * 16 + second) * 16 + third) * 16
                leaf = codes[start : start + 16]
                parts.append(
                    "        ["
                    + ", ".join(map(str, leaf))
                    + "]"
                    + ("," if third < 15 else "")
                    + "\n"
                )
            parts.append("      ]" + ("," if second < 15 else "") + "\n")
        parts.append("    ]" + ("," if top < 3 else "") + "\n")
    parts.extend(
        [
            '  ]"\n\n',
            'definition comma_rank_code_at :: "nat \\<Rightarrow> nat" where\n',
            '  "comma_rank_code_at i = comma_rank_codes ! (i div 4096) !\n',
            '    ((i div 256) mod 16) ! ((i div 16) mod 16) ! (i mod 16)"\n\n',
            'definition comma_rank_candidate :: "comma_boundary_state \\<Rightarrow> nat option" where\n',
            '  "comma_rank_candidate q =\n',
            "    (case q of (kind,a,r) \\<Rightarrow>\n",
            "      let index = (if kind = Comma_Z then 8 * 924 else 0) +\n",
            "        (a - 2) * 924 + r; code = comma_rank_code_at index\n",
            '      in if code = 0 then None else Some (code - 1))"\n\n',
            "end\n",
        ]
    )
    return "".join(parts)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = _render(_candidate_ranks())
    if args.check:
        if args.output.read_text() != content:
            raise SystemExit("comma rank candidate differs from regenerated data")
        print("comma rank candidate matches deterministic generator")
    else:
        args.output.write_text(content)
        print(args.output)


if __name__ == "__main__":
    main()
