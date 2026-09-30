from __future__ import annotations

from devtools.paths import report_output

import json
from dataclasses import asdict

from devtools.experiments.algebra.baby_giant_behavioral_bend import (
    BabyGiantBendPacketMemo,
    behavioral_bend_frontier,
    behavioral_bend_quotient_audit,
)


def main() -> None:
    controls = [
        behavioral_bend_quotient_audit("fermat", 5),
        behavioral_bend_quotient_audit("mersenne", 11),
        behavioral_bend_quotient_audit("mersenne", 29),
    ]
    memo = BabyGiantBendPacketMemo()
    packets = [
        memo.evaluate("fermat", 4, start=1, span=3),
        memo.evaluate("fermat", 5, start=1, span=511),
        memo.evaluate("mersenne", 13, start=1, span=3),
        memo.evaluate("mersenne", 29, start=1, span=399),
    ]
    # Prove the identical fixed window is reused rather than reevaluated.
    f5_again = memo.evaluate("fermat", 5, start=1, span=511)
    assert f5_again is packets[1]
    data = {
        "controls": [asdict(row) for row in controls],
        "fixed_window_packets": [asdict(packet) for packet in packets],
        "memo": {"size": memo.size, "hits": memo.hits, "misses": memo.misses},
        "frontier": asdict(behavioral_bend_frontier()),
    }
    text = json.dumps(data, indent=2, sort_keys=True) + "\n"
    out = report_output(
        "devtools.benchmarks.baby_giant_behavioral_bend_probe",
        "baby_giant_behavioral_bend_metrics.json",
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
