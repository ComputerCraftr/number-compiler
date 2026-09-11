from devtools.benchmarks.successor_congruence_probe import run_probe
import pytest


@pytest.mark.validation  # Full reverse N=256 / accelerated Collatz proof probe.
def test_successor_congruence_release_probe_is_fail_closed() -> None:
    result = run_probe()
    assert result["status"] == "PASS"
    assert result["version"] == "0.59.9"
    assert result["exact_target_cache_requires_successor_congruence"] is True
    assert result["reverse"]["successor_conflicts"] >= 1
    assert result["collatz"]["successor_conflicts"] >= 1
    assert result["reference_oracle_counts"]["reverse_196_256"]["operator_classes"] == 2
    # The diagnostic independently observes the requested source and endpoint.
    assert result["reference_oracle_counts"]["collatz_27_64"]["operator_classes"] == 2
    assert (
        result["reference_oracle_counts"]["collatz_27_64"][
            "primitive_exact_transitions"
        ]
        == 0
    )
