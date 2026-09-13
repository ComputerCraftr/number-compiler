"""Independent finite reverse-add safety-tube audit; no all-future inference."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path


def audit(steps: int = 20_000) -> dict[str, object]:
    if type(steps) is not int or steps < 0:
        raise ValueError("steps must be a nonnegative integer")
    digits = [6, 9, 1]
    counts: Counter[str] = Counter()
    failures: Counter[str] = Counter()
    deep: Counter[str] = Counter()
    for _ in range(steps):
        pair = [x + y for x, y in zip(digits, reversed(digits))]
        reset = next((x for x in pair if x != 9), None)
        counts["ID" if reset is None else "CONST1" if reset > 9 else "CONST0"] += 1
        carry = 0
        any_carry = False
        target = []
        for s in pair:
            value = s + carry
            carry = int(value >= 10)
            any_carry |= bool(carry)
            target.append(value - 10 * carry)
        if carry:
            target.append(1)
            mismatch = next(
                (i for i in range(len(target) // 2) if target[i] != target[-1 - i]),
                None,
            )
            failures[str(mismatch)] += 1
            if mismatch == 2:
                deep[str(tuple(pair[:3]))] += 1
        else:
            counts[
                "no_growth_with_carry" if any_carry else "no_growth_without_carry"
            ] += 1
        counts["palindromes"] += int(target == target[::-1])
        digits = target
    return {
        "transitions": steps,
        "seed": 196,
        "counts": dict(counts),
        "first_growth_mismatch": dict(failures),
        "deep_pair_shells": dict(deep),
        "final_width": len(digits),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--steps", type=int, default=20_000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(audit(args.steps), indent=2) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(result)
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
