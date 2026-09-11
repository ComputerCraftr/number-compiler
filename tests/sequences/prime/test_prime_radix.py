from number_compiler.sequences.prime.radix import project_odd_prime_block_radix
from number_compiler.sequences.prime.set import project_odd_prime_block


def test_direct_prime_radix_dag_matches_bitmap_summary_without_materializing_bitmap() -> (
    None
):
    start = 9_999_993
    for length in (16, 64, 256, 1024, 4096):
        radix = project_odd_prime_block_radix(start, length)
        bitmap = project_odd_prime_block(start, length)
        assert radix.summary == bitmap.summary
        assert radix.canonical_lanes == len(bitmap.canonical_lanes)
    largest = project_odd_prime_block_radix(start, 4096)
    assert largest.reachable_bdd_nodes == 456
    # Fail-honest instrumentation: compact final semantics do not mean the
    # construction itself is yet smaller than the lane basis.
    assert largest.allocated_bdd_nodes > largest.canonical_lanes
